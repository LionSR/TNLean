"""Add to drop.json the interaction hypotheses that the linter reports as unused in a
declaration's signature. Run from the TNLean root on the log of a build of the current tree."""
import json, re, sys, pathlib
P = pathlib.Path(__file__).parent / 'drop.json'
drop = json.loads(P.read_text()) if P.exists() else {}
DECL = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*"
                  r"(theorem|lemma|def|abbrev)\s+([\w.'«»]+)")
added = 0
for line in open(sys.argv[1]):
    m = re.match(r"(?:(?:warning|error): )?(TNLean[^:]+):(\d+):(\d+): (?:error: |warning: )?Variable name `(h\w*?J?'*)` is not explicitly referenced", line)
    if not m:
        continue
    f, ln, var = m[1], int(m[2]), m[4]
    if not re.fullmatch(r"h\w*", var) or var in ('h0', 'h1', 'hJ', 'hs'):
        continue
    lines = pathlib.Path(f).read_text().split('\n')
    # the enclosing declaration, and whether the position is in its signature
    for k in range(ln - 1, -1, -1):
        d = DECL.match(lines[k])
        if d:
            sig = '\n'.join(lines[k:ln])
            if ':=' in sig.split('\n')[-1][:int(m[3])] or re.search(r":=\s*(by)?\s*$", '\n'.join(lines[k:ln - 1])):
                break
            # the hypothesis must be one of the two introduced for an interaction
            if not re.search(rf"\({re.escape(var)} : ∀ X, (?:\(\w+'*\.term X\)\.IsHermitian|‖\w+'*\.term X‖ ≤)", lines[ln - 1]):
                break
            name = d[2].split('.')[-1]
            if var not in drop.setdefault(name, []):
                drop[name].append(var); added += 1
            break
P.write_text(json.dumps(drop, indent=1, sort_keys=True))
print(added, 'added;', sum(map(len, drop.values())), 'in total')
