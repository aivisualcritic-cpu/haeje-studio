const express = require('express');
const multer = require('multer');
const fs = require('fs');
const path = require('path');
const pdfParseLib = require('pdf-parse');
const mammoth = require('mammoth');
const iconv = require('iconv-lite');
const jschardet = require('jschardet');
const { exec } = require('child_process');

const app = express();
const PORT = process.env.PORT || 3217;
const ROOT = __dirname;
const upload = multer({ dest: path.join(ROOT, 'uploads') });
const outputsRoot = path.join(ROOT, 'outputs');
const todayLocal = new Date(Date.now() + 9 * 60 * 60 * 1000).toISOString().slice(0, 10);
const dailyOutputDir = path.join(outputsRoot, todayLocal);
const digestDir = path.join(outputsRoot, 'digests');

fs.mkdirSync(path.join(ROOT, 'uploads'), { recursive: true });
fs.mkdirSync(outputsRoot, { recursive: true });
fs.mkdirSync(dailyOutputDir, { recursive: true });
fs.mkdirSync(digestDir, { recursive: true });

app.use((req, res, next) => {
  res.setHeader('Content-Type', 'application/json; charset=utf-8');
  next();
});
app.use(express.json({ limit: '25mb', type: ['application/json', 'application/*+json'] }));
app.use(express.urlencoded({ extended: true, limit: '25mb' }));
app.use('/outputs', express.static(outputsRoot, {
  setHeaders: (res, filePath) => {
    const ext = path.extname(filePath).toLowerCase();
    if (ext === '.html') res.setHeader('Content-Type', 'text/html; charset=utf-8');
    if (ext === '.txt' || ext === '.md') res.setHeader('Content-Type', 'text/plain; charset=utf-8');
    if (ext === '.json') res.setHeader('Content-Type', 'application/json; charset=utf-8');
  }
}));
app.use(express.static(path.join(ROOT, 'public'), {
  setHeaders: (res, filePath) => {
    if (path.basename(filePath) === 'index.html') {
      res.setHeader('Content-Type', 'text/html; charset=utf-8');
    }
  }
}));

function isMojibake(text = '') {
  const s = String(text || '');
  if (!s) return false;
  const mojibakePatterns = [
    /Ã[\x80-\xBF]/g,
    /Â[\x80-\xBF ]/g,
    /ì|ë|ê|í|ó|ô|õ|ú|û|ü|ñ|Ð|þ|ã|á/g,
    /�/g,
    /[\x00-\x08\x0B\x0C\x0E-\x1F]/g
  ];
  let score = 0;
  for (const pattern of mojibakePatterns) {
    const matches = s.match(pattern);
    if (matches) score += matches.length;
  }
  const suspiciousClusters = s.match(/[A-Za-z][ÃÂ][A-Za-zÀ-ÿ]/g);
  if (suspiciousClusters) score += suspiciousClusters.length * 2;
  return score >= 2;
}

function normalizeText(text = '') {
  return String(text || '')
    .replace(/^\uFEFF/, '')
    .replace(/\u0000/g, ' ')
    .replace(/\r\n/g, '\n')
    .replace(/\r/g, '\n')
    .replace(/[\u200B-\u200D\u2060]/g, '')
    .normalize('NFC')
    .replace(/[ \t]+\n/g, '\n')
    .replace(/\n{3,}/g, '\n\n')
    .trim();
}

function scoreKoreanReadability(text = '') {
  const s = String(text || '');
  if (!s) return -999;
  const hangul = (s.match(/[가-힣]/g) || []).length;
  const latin = (s.match(/[A-Za-z]/g) || []).length;
  const replacement = (s.match(/�/g) || []).length;
  const mojis = (s.match(/[ÃÂÐþãá]/g) || []).length;
  const weird = (s.match(/[^\x20-\x7E가-힣ㄱ-ㅎㅏ-ㅣ。、·〈〉《》“”‘’…—–,:;!?()\[\]{}<>\-_=+/*'"\s]/g) || []).length;
  return hangul * 3 - replacement * 8 - mojis * 5 - weird * 4 + Math.min(latin, 40) * 0.2;
}

function tryRepairEncoding(text = '') {
  const original = normalizeText(text);
  if (!original) return original;

  const candidates = [{ label: 'original', text: original }];

  try {
    const latin1ToUtf8 = Buffer.from(original, 'latin1').toString('utf8');
    candidates.push({ label: 'latin1->utf8', text: normalizeText(latin1ToUtf8) });
  } catch {}

  try {
    const win1252ToUtf8 = Buffer.from(original, 'binary').toString('utf8');
    candidates.push({ label: 'binary->utf8', text: normalizeText(win1252ToUtf8) });
  } catch {}

  try {
    const utf8Bytes = Buffer.from(original, 'latin1');
    candidates.push({ label: 'latin1->cp949', text: normalizeText(iconv.decode(utf8Bytes, 'cp949')) });
    candidates.push({ label: 'latin1->euc-kr', text: normalizeText(iconv.decode(utf8Bytes, 'euc-kr')) });
  } catch {}

  const scored = candidates
    .filter(c => c.text)
    .map(c => ({ ...c, score: scoreKoreanReadability(c.text), mojibake: isMojibake(c.text) }))
    .sort((a, b) => b.score - a.score);

  const best = scored[0];
  const current = scored.find(c => c.label === 'original') || { score: scoreKoreanReadability(original), mojibake: isMojibake(original), text: original };

  if (!best) return original;
  if (best.label === 'original') return original;

  const clearlyBetter = best.score >= current.score + 6;
  const fixesMojibake = current.mojibake && !best.mojibake;
  const gainsHangul = (best.text.match(/[가-힣]/g) || []).length > (current.text.match(/[가-힣]/g) || []).length + 3;

  return (clearlyBetter || fixesMojibake || gainsHangul) ? best.text : original;
}

function sanitizeVisibleText(text = '') {
  return tryRepairEncoding(normalizeText(text));
}

function stripSensitive(text = '') {
  return String(text || '')
    .replace(/[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}/gi, '[email masked]')
    .replace(/\b\d{2,3}[-.\s]?\d{3,4}[-.\s]?\d{4}\b/g, '[phone masked]')
    .replace(/\b\d{6}-\d{7}\b/g, '[id masked]');
}

function cleanText(text = '') {
  return sanitizeVisibleText(text)
    .replace(/[ \t]{2,}/g, ' ')
    .replace(/\n{3,}/g, '\n\n')
    .trim();
}

function splitParagraphs(text = '') {
  return cleanText(text).split(/\n\s*\n+/).map(s => s.trim()).filter(Boolean);
}

function splitSentences(text = '') {
  return cleanText(text)
    .split(/(?<=[.!?。]|다\.|다\s)/)
    .map(s => s.trim())
    .filter(Boolean);
}

function sanitizeFileName(s = '') {
  return cleanText(s || 'untitled')
    .replace(/[<>:"/\\|?*\x00-\x1F]/g, ' ')
    .replace(/\s+/g, '_')
    .replace(/_+/g, '_')
    .replace(/^_+|_+$/g, '')
    .slice(0, 80) || 'untitled';
}

function readTextFileWithFallback(filePath) {
  const buffer = fs.readFileSync(filePath);
  const candidates = [];

  const utf8 = normalizeText(buffer.toString('utf8'));
  candidates.push({ label: 'utf8', text: tryRepairEncoding(utf8) });

  const detected = jschardet.detect(buffer) || {};
  const encodings = new Set(['cp949', 'euc-kr', 'utf8']);
  if (detected.encoding) encodings.add(String(detected.encoding).toLowerCase());

  for (const enc of encodings) {
    try {
      if (enc === 'utf8' || enc === 'utf-8') continue;
      const decoded = normalizeText(iconv.decode(buffer, enc));
      candidates.push({ label: enc, text: tryRepairEncoding(decoded) });
    } catch {}
  }

  const scored = candidates
    .filter(c => c.text)
    .map(c => ({ ...c, score: scoreKoreanReadability(c.text), mojibake: isMojibake(c.text) }))
    .sort((a, b) => b.score - a.score);

  return scored[0]?.text || utf8;
}

function inferTitle(text, fileName) {
  const lines = cleanText(text).split('\n').map(v => v.trim()).filter(Boolean);
  const candidate = lines.find(line => line.length >= 6 && line.length <= 180) || cleanText(path.parse(fileName || 'untitled').name);
  return candidate || '제목 미상';
}

function detectDocumentType(text, selectedType) {
  if (selectedType && selectedType !== 'auto-detect') return selectedType;
  if (/(abstract|methodology|references|conclusion|연구|논문|초록|방법론|선행연구|참고문헌)/i.test(text)) return 'academic paper';
  if (/(기자|연합뉴스|보도|취재|기사|인터뷰|속보)/i.test(text)) return 'newspaper article';
  if (/(비평|전시|작가|미학|문화비평|리뷰|criticism|essay)/i.test(text)) return 'magazine / criticism article';
  if (/(정책|보고서|권고|정부|예산|시행|평가|policy|recommendation)/i.test(text)) return 'policy report';
  return 'other';
}

function mapParagraphAnchors(paragraphs) {
  return paragraphs.map((p, i) => ({ id: `¶${i + 1}`, text: p }));
}

function pickSentences(sentences, count = 3) {
  return sentences.slice(0, count).join(' ').trim() || '원문에서 명확히 확인되지 않음';
}

function findByPatterns(text, patterns) {
  for (const pattern of patterns) {
    const match = text.match(pattern);
    if (match && match[1]) return cleanText(match[1]);
  }
  return '';
}

function buildAcademicSpecific(text, paragraphs, sentences) {
  return {
    researchQuestion: findByPatterns(text, [
      /(?:연구문제|연구 질문|research question)\s*[:：]?\s*([^\n]{10,300})/i,
      /(?:이 연구는|본 연구는|본 논문은)\s+([^\.\n]{20,260})/i
    ]) || pickSentences(sentences, 1),
    methodology: findByPatterns(text, [
      /(?:방법론|연구방법|methodology|methods?)\s*[:：]?\s*([^\n]{10,300})/i,
      /(?:분석|비교|고찰|검토|실험|조사)\s*(?:하였다|했다)([^\n]{0,80})/i
    ]) || '원문에서 명확히 확인되지 않음',
    contribution: findByPatterns(text, [
      /(?:의의|기여|contribution)\s*[:：]?\s*([^\n]{10,300})/i
    ]) || '원문에서 명확히 확인되지 않음'
  };
}

function buildNewsSpecific(text, paragraphs, sentences) {
  return {
    event: pickSentences(sentences, 1),
    framing: paragraphs[0] || '원문에서 명확히 확인되지 않음',
    sourcing: findByPatterns(text, [/(?:관계자|전문가|정부|당국|익명|자료에 따르면)([^\n]{0,120})/i]) || '원문에서 명확히 확인되지 않음',
    bias: '기사의 어조, 인용 배치, 사건 해석 프레임을 기준으로 판단해야 하나 자동 판독에는 한계가 있음'
  };
}

function buildCriticismSpecific(text, paragraphs, sentences) {
  return {
    frame: paragraphs[0] || '원문에서 명확히 확인되지 않음',
    rhetoric: '해석의 축, 비유, 대조, 참조 인물·사조 배치를 중심으로 읽어야 함',
    stance: pickSentences(sentences.slice(1), 1)
  };
}

function buildPolicySpecific(text, paragraphs, sentences) {
  return {
    policyProblem: paragraphs[0] || '원문에서 명확히 확인되지 않음',
    assumptions: findByPatterns(text, [/(?:가정|전제|assumption)\s*[:：]?\s*([^\n]{10,200})/i]) || '원문에서 명확히 확인되지 않음',
    recommendations: findByPatterns(text, [/(?:권고|제언|recommendation)\s*[:：]?\s*([^\n]{10,300})/i]) || pickSentences(sentences.slice(-3), 1),
    feasibility: '실행 주체, 재정, 제도, 이해관계자 저항 여부를 추가 검토해야 함'
  };
}

function inferKeywords(text) {
  const tokens = stripSensitive(text)
    .replace(/[^\p{L}\p{N}\s-]/gu, ' ')
    .split(/\s+/)
    .map(v => v.trim())
    .filter(v => v.length >= 2);
  const stop = new Set(['그리고','그러나','하지만','대한','에서','으로','이다','있다','위한','the','and','for','that','with','from','this','were','have','has','있음','명확히','확인되지','않음']);
  const freq = new Map();
  for (const token of tokens) {
    if (stop.has(token)) continue;
    freq.set(token, (freq.get(token) || 0) + 1);
  }
  return [...freq.entries()].sort((a,b) => b[1]-a[1]).slice(0, 10).map(([k]) => k);
}

function generateAnalysis({ text, fileName, selectedType, options = {} }) {
  const cleaned = cleanText(stripSensitive(text));
  const paragraphs = splitParagraphs(cleaned);
  const sentences = splitSentences(cleaned);
  const title = inferTitle(cleaned, fileName);
  const docType = detectDocumentType(cleaned, selectedType);
  const anchors = mapParagraphAnchors(paragraphs);
  const limitationNotes = [];

  if (!cleaned) limitationNotes.push('입력 원문이 비어 있어 실질 분석이 불가능함. 형식 요건 중심의 결과만 생성함.');
  if (cleaned.length < 300) limitationNotes.push('원문 분량이 매우 짧아 논지 구조와 근거 체계 분석의 정확도가 제한됨.');
  if (!paragraphs.length) limitationNotes.push('문단 구획을 안정적으로 식별하지 못해 문단 근거 매핑이 제한됨.');

  const thesis = findByPatterns(cleaned, [
    /(?:핵심 주장|주논지|논지|thesis)\s*[:：]?\s*([^\n]{20,300})/i,
    /(?:본 논문은|이 글은|본고는|이 기사는)\s+([^\.\n]{20,300})/i
  ]) || pickSentences(sentences, 2) || '원문에서 명확히 확인되지 않음';

  const problem = findByPatterns(cleaned, [
    /(?:문제의식|연구문제|문제 제기)\s*[:：]?\s*([^\n]{20,300})/i,
    /(?:왜|무엇을 문제 삼아)([^\.\n]{20,220})/i
  ]) || (paragraphs[0] || '원문에서 명확히 확인되지 않음');

  const structureItems = paragraphs.slice(0, Math.min(paragraphs.length, 5)).map((p, i) => {
    const head = p.split(/(?<=[.!?。]|다\.)/)[0]?.trim() || p.slice(0, 90);
    return `${i + 1}. ${head}${options.includeGrounding ? ` [${anchors[i]?.id || `¶${i+1}`}]` : ''}`;
  });

  const evidenceItems = paragraphs.slice(0, Math.min(paragraphs.length, 4)).map((p, i) => {
    const clipped = p.slice(0, 180);
    return `- 근거 ${i + 1}: ${clipped}${p.length > 180 ? '…' : ''}${options.includeGrounding ? ` (${anchors[i]?.id || `¶${i+1}`})` : ''}`;
  });

  const methods = findByPatterns(cleaned, [
    /(?:방법론|연구방법|방법|취재 방식|methodology|methods?)\s*[:：]?\s*([^\n]{10,300})/i
  ]) || (docType === 'newspaper article' ? '보도·인용·현장/자료 취재 방식으로 추정되나 원문에서 명확히 확인되지 않음' : '원문에서 명확히 확인되지 않음');

  const context = pickSentences(sentences.slice(0, 3), 2);
  const strengths = [];
  const limitations = [];

  if (paragraphs.length >= 3) strengths.push('도입-전개-정리의 최소 구조가 확인되어 독자의 추적 가능성이 비교적 높다.');
  if (sentences.length >= 8) strengths.push('핵심 주장과 보조 설명이 분리되어 있어 논점 추출이 가능하다.');
  if (!strengths.length) strengths.push('제한된 분량 안에서도 주제 단서와 핵심 어휘는 일부 파악 가능하다.');

  if (cleaned.length < 1200) limitations.push('분량이 충분하지 않아 반론 가능성, 자료 포섭 범위, 논증의 누락 지점을 정밀 판정하기 어렵다.');
  if (!findByPatterns(cleaned, [/(?:자료|통계|인용|각주|references|참고문헌|인터뷰|조사)/i])) limitations.push('자료 출처 또는 인용 체계가 자동 추출되지 않아 근거의 검증 가능성이 제한된다.');
  limitations.push('자동 분석 결과이므로 세부 사실관계와 페이지 매핑은 원문 대조가 필요하다.');

  let genreSpecific = {};
  if (docType === 'academic paper') genreSpecific = buildAcademicSpecific(cleaned, paragraphs, sentences);
  else if (docType === 'newspaper article') genreSpecific = buildNewsSpecific(cleaned, paragraphs, sentences);
  else if (docType === 'magazine / criticism article') genreSpecific = buildCriticismSpecific(cleaned, paragraphs, sentences);
  else if (docType === 'policy report') genreSpecific = buildPolicySpecific(cleaned, paragraphs, sentences);

  const keywords = inferKeywords(cleaned);
  const oneLine = `${title}은/는 ${docType}로 분류되며, ${thesis.slice(0, 120)}${thesis.length > 120 ? '…' : ''}`;

  const directQuote = options.includeQuotes && sentences[0]
    ? `“${sentences[0].slice(0, 110)}${sentences[0].length > 110 ? '…' : ''}”`
    : '직접 인용 비활성화 또는 적절한 짧은 문장을 안정적으로 추출하지 못함';

  const groundingBlock = options.includeGrounding
    ? anchors.slice(0, 8).map(a => `- ${a.id}: ${a.text.slice(0, 120)}${a.text.length > 120 ? '…' : ''}`).join('\n')
    : '비활성화';

  const chartNote = options.includeCharts
    ? '표·차트 해석: 원문에 표/차트가 포함되어 있더라도 현재 추출 경로에서는 구조화 판독이 제한될 수 있음. 설명 문장이 있을 경우 그 문장을 우선 해석함.'
    : '표·차트 해석 비활성화';

  const standard = `# 표준 해제\n\n${limitationNotes.length ? `> 제한 메모: ${limitationNotes.join(' / ')}\n\n` : ''}` +
`## 1. 제목 / Title\n${title}\n\n` +
`## 2. 문헌 또는 기사 기본 정보\n- 문서 유형: ${docType}\n- 입력 파일명: ${cleanText(fileName || 'pasted-text')}\n- 원문 길이: 약 ${cleaned.length}자\n- 분석 깊이: ${options.depth || 'standard'}\n- 톤: ${options.tone || 'academic'}\n- 출력 길이: ${options.length || 'medium'}\n- 대상 독자: ${options.audience || 'student'}\n- 해제 모드: ${options.mode || 'faithful-to-source'}\n- 목적: ${options.purpose || 'other'}\n\n` +
`## 3. 한 줄 규정\n${oneLine}\n\n` +
`## 4. 핵심 주제\n${keywords.slice(0, 5).join(', ') || '원문에서 명확히 확인되지 않음'}\n\n` +
`## 5. 문제의식\n${problem}\n\n` +
`## 6. 핵심 주장(주논지)\n${thesis}\n\n` +
`## 7. 논지 전개 구조\n${structureItems.length ? structureItems.join('\n') : '원문에서 명확히 확인되지 않음'}\n\n` +
`## 8. 핵심 근거 및 자료\n${evidenceItems.length ? evidenceItems.join('\n') : '- 원문에서 명확히 확인되지 않음'}\n\n` +
`## 9. 방법론 또는 취재 방식\n${methods}\n\n` +
`## 10. 핵심 개념 및 용어\n${keywords.length ? keywords.join(', ') : '원문에서 명확히 확인되지 않음'}\n\n` +
`## 11. 시대적 / 사회적 / 학문적 맥락\n${context}\n\n` +
`## 12. 강점\n- ${strengths.join('\n- ')}\n\n` +
`## 13. 한계 또는 비판적 검토\n- ${limitations.join('\n- ')}\n\n` +
`## 14. 의의 및 활용 가능성\n이 해제는 원문의 주제·논지·근거·맥락을 분리해 읽도록 설계되어 있으며, 수업 발표·연구 검토·콘텐츠 기획의 출발점으로 활용할 수 있다. 다만 정밀 인용과 사실 검증은 원문 대조가 필수다.\n\n` +
`## 15. 추천 독자\n${options.audience || 'student'} 독자층, 해당 주제의 입문자, 빠른 사전 검토가 필요한 연구자\n\n` +
`## 16. 핵심 키워드 5~10개\n${keywords.slice(0, 10).join(', ') || '원문에서 명확히 확인되지 않음'}\n\n` +
`## 근거 위치\n${groundingBlock}\n\n` +
`## 직접 인용\n${directQuote}\n\n` +
`## 표/차트 해석 메모\n${chartNote}\n`;

  const critical = `# 비판적 해제\n\n` +
`## 저자가 말하는 것\n${thesis}\n\n` +
`## 텍스트가 조직되는 방식\n${structureItems.join('\n') || '원문에서 명확히 확인되지 않음'}\n\n` +
`## 앱의 평가\n1. 논증의 중심축은 ${problem.slice(0, 100)}${problem.length > 100 ? '…' : ''}에 놓여 있다.\n2. 근거는 ${evidenceItems.length ? '일부 확인되나 자료 체계의 충분성은 재검토가 필요하다.' : '자동 추출이 부족해 검증이 제한된다.'}\n3. 강점은 ${strengths[0]}\n4. 취약점은 ${limitations[0]}\n`;

  const presentation = `# 발표용 해제\n\n- 세 문장 요약:\n  1) ${problem}\n  2) ${thesis}\n  3) 이 글의 의의는 ${strengths[0]} 반면 한계는 ${limitations[0]}\n\n- 발표 포인트:\n  - 핵심 주제: ${keywords.slice(0, 4).join(', ')}\n  - 구조: ${structureItems[0] || '원문에서 명확히 확인되지 않음'}\n  - 질문거리: 저자의 근거는 충분한가, 반대 해석은 가능한가?\n`;

  const abstractView = `# 초록형 해제\n\n이 문서는 ${docType}로 판독되며, 핵심 문제의식은 ${problem}이다. 저자의 주논지는 ${thesis}로 정리된다. 텍스트는 대체로 ${structureItems.length}개 안팎의 단락 전개를 통해 논지를 밀어가며, 주요 근거는 ${evidenceItems.length ? '본문 초반에 제시된 설명과 사례' : '원문에서 명확히 확인되지 않음'}에 의존한다. 의의는 ${strengths[0]}에 있고, 한계는 ${limitations[0]}에 있다.`;

  const contentPlanning = `# 콘텐츠 기획용 해제\n\n- 후킹 포인트: ${keywords.slice(0, 3).join(', ')}\n- 1문단 디제스트: ${oneLine}\n- 확장 아이디어:\n  - 비교 글: 같은 주제를 다른 입장과 대조\n  - 카드뉴스: 핵심 주장 / 근거 / 한계 3분할\n  - 쇼츠/릴스 스크립트: 문제제기 → 주장 → 왜 중요한가\n`;

  return {
    title: cleanText(title),
    docType,
    limitationNotes,
    standard: cleanText(standard),
    critical: cleanText(critical),
    presentation: cleanText(presentation),
    abstractView: cleanText(abstractView),
    contentPlanning: cleanText(contentPlanning),
    metadata: {
      title: cleanText(title),
      docType,
      options,
      fileName: cleanText(fileName || 'pasted-text'),
      length: cleaned.length,
      keywords,
      genreSpecific
    }
  };
}

function renderHtml(result) {
  const esc = (s='') => String(s)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');
  const tabs = [
    ['standard', '표준 해제', result.standard],
    ['critical', '비판적 해제', result.critical],
    ['presentation', '발표용 해제', result.presentation],
    ['abstract', '초록형 해제', result.abstractView],
    ['content', '콘텐츠 기획용 해제', result.contentPlanning]
  ];
  return `<!doctype html>
<html lang="ko">
<head>
<meta charset="UTF-8" />
<meta http-equiv="Content-Type" content="text/html; charset=UTF-8" />
<meta name="viewport" content="width=device-width, initial-scale=1" />
<meta http-equiv="X-UA-Compatible" content="IE=edge" />
<title>${esc(result.metadata.title)} 해제</title>
<style>
body{font-family:-apple-system,BlinkMacSystemFont,'Apple SD Gothic Neo','Noto Sans KR',sans-serif;margin:0;background:#111827;color:#e5e7eb}
header{padding:24px 28px;background:#0f172a;border-bottom:1px solid #334155}
main{display:grid;grid-template-columns:260px 1fr;min-height:100vh}
aside{border-right:1px solid #334155;padding:20px;background:#111827}
section{padding:24px 28px}
button.tab{display:block;width:100%;margin:0 0 10px;padding:12px 14px;border-radius:12px;border:1px solid #475569;background:#1f2937;color:#fff;text-align:left;cursor:pointer}
button.tab.active{background:#2563eb}
pre{white-space:pre-wrap;word-break:keep-all;line-height:1.7;background:#0b1220;border:1px solid #334155;border-radius:16px;padding:20px}
.small{font-size:13px;color:#94a3b8}
.card{background:#0b1220;border:1px solid #334155;border-radius:16px;padding:16px;margin-bottom:16px}
a{color:#93c5fd}
</style>
</head>
<body>
<header>
<h1 style="margin:0 0 8px">해제 엔진 결과</h1>
<div class="small">문서 유형: ${esc(result.metadata.docType)} · 원문 길이: 약 ${result.metadata.length}자</div>
</header>
<main>
<aside>
<div class="card"><strong>${esc(result.metadata.title)}</strong><div class="small" style="margin-top:8px">${esc((result.limitationNotes||[]).join(' / ') || '제한 메모 없음')}</div></div>
${tabs.map(([id,label]) => `<button class="tab" data-tab="${id}">${label}</button>`).join('')}
<div class="card">
<div><strong>고급 카드</strong></div>
<ul>
<li>논지 지도(thesis map): 핵심 주장 ↔ 근거 ↔ 한계</li>
<li>argument tree: 표준 해제의 구조 항목 참조</li>
<li>key terms card: ${esc(result.metadata.keywords.slice(0,6).join(', '))}</li>
<li>strengths vs limitations: 표준 해제 12·13절</li>
<li>3문장 발표 버전: 발표용 해제</li>
<li>1문단 에디터 디제스트: 초록형 해제</li>
</ul>
</div>
<div class="small">저장된 HTML 파일을 직접 열어도 동일한 결과를 볼 수 있습니다.</div>
</aside>
<section>
${tabs.map(([id,label,content], idx) => `<div class="panel" id="panel-${id}" style="display:${idx===0?'block':'none'}"><h2>${label}</h2><pre>${esc(content)}</pre></div>`).join('')}
</section>
</main>
<script>
const tabs=[...document.querySelectorAll('.tab')];
const panels=[...document.querySelectorAll('.panel')];
function activate(id){tabs.forEach(b=>b.classList.toggle('active',b.dataset.tab===id));panels.forEach(p=>p.style.display=p.id==='panel-'+id?'block':'none');}
tabs.forEach(b=>b.addEventListener('click',()=>activate(b.dataset.tab)));
activate('standard');
</script>
</body>
</html>`;
}

function saveUtf8File(filePath, content) {
  fs.writeFileSync(filePath, normalizeText(content), { encoding: 'utf8' });
}

function saveOutputs(result) {
  const date = todayLocal;
  const base = `${date}_${sanitizeFileName(result.docType)}_${sanitizeFileName(result.title)}_haeje`;
  const mdPath = path.join(dailyOutputDir, `${base}.md`);
  const txtPath = path.join(dailyOutputDir, `${base}.txt`);
  const htmlPath = path.join(dailyOutputDir, `${base}.html`);

  const markdown = [
    `# ${result.title} 해제 결과`,
    '',
    `- 문서 유형: ${result.docType}`,
    `- 제한 메모: ${(result.limitationNotes || []).join(' / ') || '없음'}`,
    '',
    result.standard,
    '',
    result.critical,
    '',
    result.presentation,
    '',
    result.abstractView,
    '',
    result.contentPlanning,
    '',
    '---',
    '',
    '## 메타데이터',
    '```json',
    JSON.stringify(result.metadata, null, 2),
    '```'
  ].join('\n');

  const text = [result.standard, result.critical, result.presentation, result.abstractView, result.contentPlanning].join('\n\n');
  const html = renderHtml(result);

  saveUtf8File(mdPath, markdown);
  saveUtf8File(txtPath, text);
  saveUtf8File(htmlPath, html);
  fs.copyFileSync(mdPath, path.join(digestDir, path.basename(mdPath)));
  fs.copyFileSync(htmlPath, path.join(digestDir, path.basename(htmlPath)));

  return { base, mdPath, txtPath, htmlPath, markdown, text, html };
}

function openTarget(targetPath) {
  return new Promise((resolve) => {
    exec(`open ${JSON.stringify(targetPath)}`, (error) => {
      resolve({ success: !error, error: error ? String(error.message || error) : null, targetPath });
    });
  });
}

async function extractFileText(file) {
  const ext = path.extname(file.originalname).toLowerCase();
  const filePath = file.path;
  try {
    if (ext === '.pdf') {
      const buffer = fs.readFileSync(filePath);
      let text = '';
      if (typeof pdfParseLib === 'function') {
        const data = await pdfParseLib(buffer);
        text = data?.text || '';
      } else if (typeof pdfParseLib?.PDFParse === 'function') {
        const parser = new pdfParseLib.PDFParse({ data: buffer });
        const data = await parser.getText();
        text = data?.text || '';
        if (typeof parser.destroy === 'function') await parser.destroy();
      }
      const raw = normalizeText(text || '');
      return tryRepairEncoding(raw);
    }
    if (ext === '.docx') {
      const data = await mammoth.extractRawText({ path: filePath });
      const raw = normalizeText(data.value || '');
      return tryRepairEncoding(raw);
    }
    if (ext === '.txt' || ext === '.md') {
      return readTextFileWithFallback(filePath);
    }
    return '';
  } finally {
    fs.unlink(filePath, () => {});
  }
}

app.get('/api/health', (_req, res) => {
  res.setHeader('Content-Type', 'application/json; charset=utf-8');
  res.json({ ok: true, app: '해제 엔진 (Annotation & Critical Digest Studio)', port: PORT });
});

app.post('/api/generate', upload.single('file'), async (req, res) => {
  res.setHeader('Content-Type', 'application/json; charset=utf-8');
  const body = req.body || {};
  const options = {
    depth: body.depth || 'standard',
    tone: body.tone || 'academic',
    length: body.length || 'medium',
    audience: body.audience || 'student',
    mode: body.mode || 'faithful-to-source',
    includeQuotes: String(body.includeQuotes || 'off') === 'on',
    includeGrounding: String(body.includeGrounding || 'on') === 'on',
    includeCharts: String(body.includeCharts || 'on') === 'on',
    purpose: body.purpose || 'other'
  };

  let text = cleanText(body.text || '');
  let sourceName = 'pasted-text';
  let limitationPrefix = [];

  if (req.file) {
    sourceName = cleanText(req.file.originalname);
    try {
      const extracted = await extractFileText(req.file);
      if (extracted) {
        text = cleanText(extracted);
      } else if (text) {
        limitationPrefix.push('업로드 파일에서 안정적으로 텍스트를 추출하지 못해 붙여넣기 텍스트를 대신 사용함.');
      } else {
        limitationPrefix.push('업로드 파일에서 텍스트 추출에 실패했으며 OCR 경로가 현재 앱에 내장되지 않아 이미지 기반 문서 해제가 제한됨.');
      }
    } catch (e) {
      const msg = cleanText(e && e.message ? e.message : String(e || 'unknown error'));
      limitationPrefix.push(`파일 파싱 중 오류가 발생해 부분 분석 모드로 진행함. (${msg})`);
    }
  }

  text = cleanText(text);
  if (!text) {
    limitationPrefix.push('입력 파일 또는 텍스트가 제공되지 않아 형식 검증 중심의 결과를 생성함.');
  }

  const result = generateAnalysis({
    text,
    fileName: sourceName,
    selectedType: body.docType || 'auto-detect',
    options
  });
  result.limitationNotes = [...limitationPrefix, ...(result.limitationNotes || [])].map(cleanText);

  const saved = saveOutputs(result);
  const opened = await openTarget(saved.htmlPath);
  const fileUrl = `file://${saved.htmlPath}`;

  res.json({
    ok: true,
    savedFilename: path.basename(saved.mdPath),
    savedPath: saved.mdPath,
    htmlPath: saved.htmlPath,
    txtPath: saved.txtPath,
    openedTarget: opened.success ? saved.htmlPath : null,
    openedFileUrl: fileUrl,
    autoOpenSuccess: opened.success,
    autoOpenError: opened.error,
    limitationNotes: result.limitationNotes,
    debugEncoding: {
      sourceName,
      sourceNameMojibake: isMojibake(sourceName),
      extractedTextMojibake: isMojibake(text)
    },
    result
  });
});

app.listen(PORT, () => {
  console.log(`해제 엔진 실행 중: http://localhost:${PORT}`);
});
