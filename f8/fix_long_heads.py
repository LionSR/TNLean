"""A declaration `theorem _root_.ManyBody.ChainInteraction.<long name>` whose head line exceeds
100 characters is declared inside `namespace ManyBody.ChainInteraction` instead, the enclosing
namespace being closed and reopened around it and opened inside it. Only files whose enclosing
namespace declares no section variables are changed."""
import re, subprocess, pathlib
files = [pathlib.Path(p) for p in subprocess.run(['git', 'ls-files', 'TNLean/*.lean'],
         capture_output=True, text=True).stdout.split()]
DECL = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|example)\b|^end\b|^namespace\b|^section\b",
                  re.M)
for f in files:
    t = f.read_text()
    if not re.search(r"^theorem _root_\.ManyBody\.\w+\.\S+.{0,}$", t, re.M):
        continue
    ns = re.search(r"^namespace (\S+)\n", t, re.M)
    if not ns or re.search(r"^variable\b", t, re.M):
        continue
    N = ns[1]
    changed = False
    while True:
        m = next((m for m in re.finditer(r"^(theorem|lemma) _root_\.(ManyBody\.\w+)\.(\S+)", t, re.M)
                  if len(t[m.start():t.find('\n', m.start())]) > 100), None)
        if not m:
            break
        start = m.start()
        doc = re.search(r"/--(?:(?!-/).)*-/\n$", t[:start], re.S)
        if doc:
            start = doc.start()
        nxt = DECL.search(t, m.end())
        stop = nxt.start() if nxt else len(t)
        # the docstring of the next declaration stays with it
        d2 = re.search(r"/--(?:(?!-/).)*-/\n$", t[:stop], re.S)
        if d2 and d2.start() > m.end():
            stop = d2.start()
        body = t[start:stop].replace(f"{m[1]} _root_.{m[2]}.", f"{m[1]} ", 1).rstrip('\n')
        t = (t[:start] + f"end {N}\n\nnamespace {m[2]}\n\nopen {N}\n\n" + body
             + f"\n\nend {m[2]}\n\nnamespace {N}\n\n" + t[stop:])
        changed = True
    if changed:
        t = re.sub(rf"\nnamespace {re.escape(N)}\n\nend {re.escape(N)}\n", "\n", t)
        f.write_text(t)
