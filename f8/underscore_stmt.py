"""In the statements of the theorems listed in underscore_stmt.json, the bond hypotheses `h0` and
`h1` bound inside a `∀` and unused by the proof are named `_`: the source states the theorems for
positive bonds bounded by one."""
import json, re, subprocess, pathlib
names = set(json.load(open(pathlib.Path(__file__).parent / 'underscore_stmt.json')))
HEAD = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected)\s+)*(?:theorem|lemma) ([\w.'«»]+)", re.M)
for p in subprocess.run(['git', 'ls-files', 'TNLean/*.lean'], capture_output=True, text=True).stdout.split():
    f = pathlib.Path(p); t = f.read_text(); n = t
    for m in list(HEAD.finditer(t))[::-1]:
        if m[1].split('.')[-1] not in names:
            continue
        end = t.find(':= by', m.end()); end = len(t) if end < 0 else end
        stmt = n[m.end():end]
        stmt2 = re.sub(r"\((h0|h1) : ∀ j, ", "(_ : ∀ j, ", stmt)
        n = n[:m.end()] + stmt2 + n[end:]
    if n != t:
        f.write_text(n)
