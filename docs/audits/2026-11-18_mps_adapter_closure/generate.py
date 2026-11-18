"""Reproduce the explicit import-line closure without checking out or compiling Lean."""
import collections
import json
import re
import subprocess
import sys

SOURCE = '42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d'
BASE = 'dccc85e5607077b51822664e9d475287d300d607'
ref = sys.argv[1] if len(sys.argv) > 1 else SOURCE
changed = subprocess.check_output(
    ['git', 'diff', '--name-only', BASE, SOURCE, '--', 'TNLean']).decode().splitlines()
lines = subprocess.check_output(
    ['git', 'grep', '-n', '-E', '^[[:space:]]*(public )?import ', ref, '--', '*.lean']
).decode().splitlines()
reverse = collections.defaultdict(set)
imports = collections.defaultdict(set)
for line in lines:
    _, path, number, text = line.split(':', 3)
    for module in re.sub(r'^\s*(public )?import\s+', '', text).split('--')[0].split():
        if re.fullmatch(r"[A-Za-z_][\w.']*", module):
            imports[path].add(module)
            reverse[module].add(path)
result = {
    'base': BASE,
    'method': 'repository explicit import-line reverse graph; includes aggregators and fixtures; no compilation',
    'files': [],
}
for path in changed:
    seen = {path}
    todo = [path]
    while todo:
        current = todo.pop()
        for consumer in reverse[current[:-5].replace('/', '.')]:
            if consumer not in seen:
                seen.add(consumer)
                todo.append(consumer)
    result['files'].append({
        'path': path,
        'imports': sorted(imports[path]),
        'direct_consumers': sorted(reverse[path[:-5].replace('/', '.')]),
        'reverse_consumers_excluding_self': sorted(seen - {path}),
    })
result['union_including_targets'] = sorted(set().union(*(
    set(row['reverse_consumers_excluding_self']) | {row['path']}
    for row in result['files'])))
print(json.dumps(result, indent=2))
