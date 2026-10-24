// Build-time bridge to the exact hpcc JavaScript/WASM shipped by plastexdepgraph.
// Standard Node.js modules only. No network request or SVG cache is used.
'use strict';

const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const {Worker, isMainThread, parentPort, workerData} = require('node:worker_threads');

// Graphviz's dot layout recurses deeply on large graphs. Its WASM frames share
// the V8 stack, whose default size (about 1 MB) the full blueprint graph
// exceeds. The layout therefore runs in a worker thread with a larger stack.
const LAYOUT_STACK_MB = 256;

async function layoutInWorker(dot, assetRoot) {
  return new Promise((resolve, reject) => {
    const worker = new Worker(__filename, {
      workerData: {dot, assetRoot},
      resourceLimits: {stackSizeMb: LAYOUT_STACK_MB},
    });
    worker.once('message', resolve);
    worker.once('error', reject);
    worker.once('exit', code => {
      if (code !== 0) reject(new Error('Graphviz worker exited with code ' + code));
    });
  });
}

async function layoutWorker() {
  const {dot, assetRoot} = workerData;
  const hpcc = require(path.join(assetRoot, 'hpcc.min.js'));
  global.document = {}; // The same workaround as the bundled graph worker.
  global.fetch = async function (requested) {
    const filename = path.resolve(String(requested));
    const allowed = ['graphvizlib.wasm', 'expatlib.wasm']
      .some(name => filename === path.join(assetRoot, name));
    if (!allowed) throw new Error('Refusing a nonlocal Graphviz asset request');
    return new Response(fs.readFileSync(filename), {
      headers: {'Content-Type': 'application/wasm'},
    });
  };
  hpcc.wasmFolder(assetRoot);
  // Reserve stdout for the result; Graphviz diagnostics belong on stderr.
  console.log = (...args) => console.error(...args);
  const svg = await hpcc.graphviz.layout(dot, 'svg', 'dot', {images: []});
  parentPort.postMessage(svg);
}

async function main() {
  if (Number(process.versions.node.split('.')[0]) < 18) {
    throw new Error('Dependency graph precomputation requires Node.js 18 or newer');
  }
  const {source, assets, layout = true} = JSON.parse(fs.readFileSync(0, 'utf8'));
  const start = '.renderDot(`';
  const begin = source.indexOf(start);
  if (begin < 0 || source.indexOf(start, begin + start.length) >= 0) {
    throw new Error('Expected one pinned dependency graph DOT literal');
  }
  const literalStart = begin + start.length - 1;
  let end = literalStart + 1;
  for (; end < source.length; end++) {
    if (source[end] === '\\') {
      end++;
    } else if (source[end] === '`') {
      break;
    }
  }
  const literal = source.slice(literalStart, end + 1);
  if (source[end] !== '`' || source[end + 1] !== ')' || literal.includes('${')) {
    throw new Error('Dependency graph differs from the pinned literal contract');
  }
  // Only a non-interpolating string literal is evaluated. This reproduces the
  // browser's escape handling; reading the raw DOT bytes would not do so.
  const dot = vm.runInNewContext(literal, {}, {
    timeout: 1000,
    contextCodeGeneration: {strings: false, wasm: false},
  });
  if (typeof dot !== 'string') throw new Error('DOT literal did not yield a string');

  if (!layout) {
    process.stdout.write(JSON.stringify({dot}));
    return;
  }

  const assetRoot = path.resolve(assets);
  const svg = await layoutInWorker(dot, assetRoot);
  if (!svg) throw new Error('Graphviz returned no SVG');
  process.stdout.write(JSON.stringify({dot, svg}));
}

(isMainThread ? main() : layoutWorker()).catch(error => {
  console.error(String(error && error.stack || error));
  process.exitCode = 1;
});
