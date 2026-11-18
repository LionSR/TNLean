"""Remove parameters that the bond constructions no longer need, from the declarations listed
in remove_params.json ({name: [param, ...]}), and the matching top-level arguments at every call.
Run from the TNLean root after the threading passes."""
import json, re, subprocess, pathlib
P = pathlib.Path(__file__).parent / 'remove_params.json'
TABLE = json.loads(P.read_text())
files = [pathlib.Path(p) for p in subprocess.run(['git', 'ls-files', 'TNLean/*.lean'],
         capture_output=True, text=True).stdout.split()]
HEAD = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def) "
                  r"([\w.'«»]+)", re.M)


def strip_binders(t, start, params):
    """Drop the binders `(p : ...)` of `params` from the signature starting at `start`."""
    depth, k = 0, start
    while k < len(t):
        c = t[k]
        if c in '([{⦃⟨': depth += 1
        elif c in ')]}⦄⟩': depth -= 1
        elif c == ':' and depth == 0 and t[k + 1] != '=': break
        k += 1
    sig = t[start:k]
    for p in params:
        sig = re.sub(rf"\s*\({re.escape(p)} :(?:[^()]|\([^()]*(?:\([^()]*\)[^()]*)*\))*\)", "", sig, count=1)
    return t[:start] + sig + t[k:]


def drop_args(t, name, params):
    """At each call `name a₁ a₂ ...`, drop the top-level arguments spelled as one of `params`."""
    out, i = [], 0
    for m in re.finditer(rf"(?<![\w.'])(?:[\w.]+\.)?{re.escape(name)}(?![\w'])", t):
        if m.start() < i:
            continue
        line_start = t.rfind('\n', 0, m.start()) + 1
        base = len(t[line_start:m.start()]) - len(t[line_start:m.start()].lstrip())
        out.append(t[i:m.end()]); k = m.end(); depth = 0; seg = []
        while k < len(t):
            c = t[k]
            if c == '\n':
                nxt = t[k + 1:]
                ind = len(nxt) - len(nxt.lstrip(' '))
                if ind <= base or nxt.lstrip(' ').startswith(('·', '|')):
                    break
            if c in '([{⟨': depth += 1
            elif c in ')]}⟩':
                if depth == 0: break
                depth -= 1
            elif depth == 0 and (t.startswith(':=', k) or c == ','):
                break
            if depth == 0 and c in ' \n':
                w = re.match(r"\s+([\w'₀-₉]+)(?![\w'.])", t[k:])
                if w and w[1] in params:
                    k += len(w[0]); continue
            seg.append(c); k += 1
        out.append(''.join(seg)); i = k
    out.append(t[i:])
    return ''.join(out)


for f in files:
    t = f.read_text(); n = t
    for m in list(HEAD.finditer(n))[::-1]:
        name = m[1].split('.')[-1]
        if name in TABLE:
            n = strip_binders(n, m.end(), TABLE[name])
            # an implicit real bound that only the removed hypothesis mentioned
            nx = HEAD.search(n, m.end())
            end = nx.start() if nx else len(n)
            decl = n[m.start():end]
            g = re.search(r"\{((?:[\w']+ )*J(?: [\w']+)*) : ℝ\}", decl)
            if g:
                rest = re.sub(r"/-.*?-/|--[^\n]*", "", decl.replace(g[0], '', 1), flags=re.S)
                if not re.search(r"(?<![\w'])J(?![\w'])", rest):
                    names = [x for x in g[1].split() if x != 'J']
                    new = f"{{{' '.join(names)} : ℝ}}" if names else ''
                    decl = decl.replace(g[0] + ('' if names else '\n'), new, 1) if not names and g[0] + '\n' in decl else decl.replace(g[0], new, 1)
                    decl = re.sub(r"(?<=\S) {2,}(?=[({])", " ", decl)
                    n = n[:m.start()] + decl + n[end:]
    for name, params in TABLE.items():
        if re.search(rf"(?<![\w'])(?:[\w.]+\.)?{re.escape(name)}(?![\w'])", n):
            n = drop_args(n, name, params)
    if n != t:
        f.write_text(n)
