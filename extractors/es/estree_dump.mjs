// extractors/es/estree_dump.mjs — the frontend half of extractors/es/extract.py.
//
//   node estree_dump.mjs <acorn-entry> [--source-type script|module|auto]
//
// Reads one absolute path per line on stdin; writes one JSON object per line
// to stdout, IN INPUT ORDER, exactly one line per input line.
//
//   {"path":…, "ok":true,  "sourceType":"script", "ast":{…}}
//   {"path":…, "ok":false, "error":"…", "errorPos":123, "line":4, "col":8}
//   {"path":…, "runner_error":"…"}
//
// A source that does NOT PARSE is `ok:false` and is a SUCCESS of this tool —
// docs/es-envelope-schema.md §4: 4,248 of the core slice's tests assert that
// their source must not parse, so a rejection is data, not a failure. Only an
// unreadable file or a missing acorn is a runner_error.
//
// `auto` (the default) tries `script` then `module`, because test262 says
// which via metadata the frontend never sees and 5 core-slice files parse
// only as a module. Which one succeeded is REPORTED, never assumed.
//
// The AST is passed through structurally unchanged apart from dropping
// acorn's `loc`/`range` duplicates of `start`/`end`; all lowering, renaming
// and vocabulary checking happens on the Python side, where the schema lives.

import { createInterface } from 'node:readline';
import { readFileSync } from 'node:fs';

const argv = process.argv.slice(2);
const acornEntry = argv[0];
const stIdx = argv.indexOf('--source-type');
const wanted = stIdx >= 0 ? argv[stIdx + 1] : 'auto';
if (!['script', 'module', 'auto'].includes(wanted)) {
  process.stdout.write(JSON.stringify({ runner_error: `bad --source-type ${wanted}` }) + '\n');
  process.exit(3);
}

let acorn;
try {
  acorn = await import(acornEntry ? new URL(acornEntry, 'file://').href : 'acorn');
} catch (e) {
  process.stdout.write(JSON.stringify({ runner_error: `acorn not available: ${e.message}` }) + '\n');
  process.exit(3);
}

const ECMA = 'latest';
const DROP = new Set(['loc', 'range']);

function clean(node) {
  if (node === null || typeof node !== 'object') return node;
  if (Array.isArray(node)) return node.map(clean);
  const out = {};
  for (const k of Object.keys(node)) {
    if (DROP.has(k)) continue;
    const v = node[k];
    // A RegExp literal's `value` is a host RegExp (or null when the host
    // cannot build it); `regex` carries the pattern and flags as text, which
    // is what the envelope keeps. A BigInt `value` is a host BigInt, which
    // JSON cannot encode — `bigint` carries its digits.
    if (k === 'value' && (v instanceof RegExp || typeof v === 'bigint')) continue;
    out[k] = clean(v);
  }
  return out;
}

function lineCol(src, pos) {
  if (typeof pos !== 'number' || pos < 0) return [0, 0];
  let line = 1, last = 0;
  for (let i = 0; i < pos && i < src.length; i++) {
    if (src.charCodeAt(i) === 10) { line++; last = i + 1; }
  }
  return [line, pos - last];
}

const rl = createInterface({ input: process.stdin, crlfDelay: Infinity });
for await (const raw of rl) {
  const path = raw.trim();
  if (!path) continue;
  let src;
  try {
    src = readFileSync(path, 'utf8');
  } catch (e) {
    process.stdout.write(JSON.stringify({ path, runner_error: `unreadable: ${e.message}` }) + '\n');
    continue;
  }
  const types = wanted === 'auto' ? ['script', 'module'] : [wanted];
  let out = null;
  for (const sourceType of types) {
    try {
      const ast = acorn.parse(src, { ecmaVersion: ECMA, sourceType, allowHashBang: true });
      out = { path, ok: true, sourceType, ast: clean(ast) };
      break;
    } catch (e) {
      if (out === null) {
        const [line, col] = lineCol(src, e.pos);
        out = {
          path, ok: false, sourceType: types[0],
          error: String(e.message).replace(/\s*\(\d+:\d+\)\s*$/, ''),
          errorPos: typeof e.pos === 'number' ? e.pos : -1, line, col,
        };
      }
    }
  }
  process.stdout.write(JSON.stringify(out) + '\n');
}
