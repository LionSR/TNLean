#!/usr/bin/env python3
"""F8, chain and domain part: ChainHamiltonian L q R J -> ManyBody.ChainInteraction L q R and
DomainHamiltonian Λ q R J -> ManyBody.DomainInteraction Λ q R.

Run from the TNLean root:  python3 f8_chain.py [--write] [--thread]

* in each declaration binding `v : ChainHamiltonian L q R J`, the binder becomes
  `v : ChainInteraction L q R` with the hypotheses `hv : ∀ X, (v.term X).IsHermitian` and
  `hvJ : ∀ X, ‖v.term X‖ ≤ J` (`hh`, `hhJ` for `h`); inside a statement's `∀` they are `_`;
* the structure API of `v` is rewritten: `operator` is `hamiltonian`, `supported` is `mem`,
  `hermitian` and `norm_le` are the hypotheses, `operator_isHermitian` is
  `ManyBody.Interaction.isHermitian_hamiltonian`;
* `ChainHamiltonian.X` lemmas move to `ManyBody.ChainInteraction.X` (dot notation on `v`);
* `--thread` passes the hypotheses at the dot-notation uses of the moved lemmas whose final
  signatures take them right after the interaction.
"""
import re, sys, pathlib, subprocess
sys.path.insert(0, '/tmp/claude-0/-home-user-TNLean/a113a978-1f85-52c9-8773-a6b19c2e5dba/scratchpad')
from leanwrap import wrap

WRITE = '--write' in sys.argv
STRUCTS = {'ChainHamiltonian': 'ChainInteraction', 'DomainHamiltonian': 'DomainInteraction',
           'LocalHamiltonian': 'PlaneInteraction'}
NEWS = 'ChainInteraction|DomainInteraction|PlaneInteraction'
QUAL = r"(?:(?:TNLean\.)?(?:MPS\.)?AreaLaw\.(?:Hastings\.)?|Hastings\.|(?:TNLean\.)?Lattice\.)?"
# one argument of a type application: a word, or a balanced parenthesized term
ARG = r"(\w[\w.'₀-₉⁻¹]*|\((?:[^()]|\([^()]*\))*\))"
ARG4 = rf"{ARG} {ARG} {ARG} {ARG}"
DECL_START = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*"
                        r"(?:theorem|lemma|def|abbrev|instance|structure|example)\b", re.M)


def hyp_names(v):
    """The two hypothesis names for the interaction variable `v`."""
    base = v.rstrip("'"); primes = v[len(base):]
    return f"h{base}{primes}", f"h{base}J{primes}"


def lean_files():
    out = subprocess.run(['git', 'ls-files', '*.lean'], capture_output=True, text=True).stdout
    return [pathlib.Path(p) for p in out.split() if p.startswith(('TNLean/', 'scripts/'))]


def per_var(chunk, v):
    """Rewrite the structure API of the interaction variable `v` in one declaration."""
    V = re.escape(v); H, HJ = hyp_names(v)
    subs = [
        (rf"\b{V}\.operator_isHermitian\b", rf"(ManyBody.Interaction.isHermitian_hamiltonian {H})"),
        (rf"\b{V}\.doubled\.operator_isHermitian\b",
         rf"(ManyBody.Interaction.isHermitian_hamiltonian ({v}.isHermitian_doubled_term {H}))"),
        (rf"\({V}\.swappedDoubled (\w+)\)\.operator_isHermitian\b",
         rf"(ManyBody.Interaction.isHermitian_hamiltonian ({v}.isHermitian_swappedDoubled_term {H} \1))"),
        (rf"\b{V}\.operator\b", rf"{v}.hamiltonian"),
        (rf"\b{V}\.(\w*?)operator(\w*)\b", rf"{v}.\1hamiltonian\2"),
        (rf"\(\b{V}\.supported ([^()]+)\)\.mono\b", rf"Entropy.IsSupportedOn.mono ({v}.mem \1)"),
        (rf"\b{V}\.supported\b", rf"{v}.mem"),
        (rf"\b{V}\.hermitian\b", H),
        (rf"\b{V}\.norm_le\b", HJ),
        # the two hypotheses follow the variable wherever it is introduced
        # (not a lone binder `fun h ↦`, `intro h`, which is a local name)
        (rf"(\bintro\b[^\n:]*?(?<![⟨.])\b{V}\b)(?! {H}\b|,|'|\.)(?=[ \t]+\S)", rf"\1 {H} {HJ}"),
        (rf"(\bfun\b[^\n↦:]*?(?<![⟨.])\b{V}\b)(?! {H}\b|,|'|\.| ↦)(?=[^\n↦]*↦)", rf"\1 {H} {HJ}"),
    ]
    for a, b in subs:
        chunk = re.sub(a, b, chunk)
    return chunk


import json
DROPFILE = pathlib.Path(__file__).parent / 'drop.json'
DROP = json.loads(DROPFILE.read_text()) if DROPFILE.exists() else {}


KEEP_DEF = set(DROP.get('__keep_def__', []))


def binders(old, new, decl='', kind=''):
    drop = set(DROP.get(decl, []))
    if kind in ('def', 'abbrev') and decl not in KEEP_DEF:
        drop |= {'*'}

    def explicit(m):
        H, HJ = hyp_names(m[1])
        out = f"({m[1]} : {new} {m[2]} {m[3]} {m[4]})"
        # a binder of a quantifier: the hypotheses are bound there too, unnamed
        if re.search(r"[∀∃]\s*(?:\((?:[^()]|\([^()]*\))*\)\s*|\{[^{}]*\}\s*|\[(?:[^\[\]]|\[[^\[\]]*\])*\]\s*|[\w']+\s+)*$",
                     m.string[max(0, m.start() - 400):m.start()]):
            return (out + f" (_ : ∀ X, ({m[1]}.term X).IsHermitian)"
                    f" (_ : ∀ X, ‖{m[1]}.term X‖ ≤ {m[5]})")
        if H not in drop and '*' not in drop:
            out += f" ({H} : ∀ X, ({m[1]}.term X).IsHermitian)"
        if HJ not in drop and '*' not in drop:
            out += f" ({HJ} : ∀ X, ‖{m[1]}.term X‖ ≤ {m[5]})"
        return out
    return [
        (rf"\((\w+'*) : {QUAL}{old} {ARG4}\)", explicit),
        (rf"∀ (\w+'*) : {QUAL}{old} {ARG4},",
         lambda m: (f"∀ {m[1]} : {new} {m[2]} {m[3]} {m[4]}, (∀ X, ({m[1]}.term X).IsHermitian) → "
                    f"(∀ X, ‖{m[1]}.term X‖ ≤ {m[5]}) →")),
    ]


def signature(t, i):
    """The binders of the declaration whose name ends at `i`: up to the first `:` at depth 0."""
    depth = 0
    for k in range(i, len(t)):
        c = t[k]
        if c in '([{⦃⟨':
            depth += 1
        elif c in ')]}⦄⟩':
            depth -= 1
        elif c == ':' and depth == 0 and t[k + 1] != '=':
            return t[i:k]
    return ''


def hamName(x):
    return x.replace('operator', 'hamiltonian')


GLOBAL = [
    # lemmas of the bond constructions: the positivity and the bound left the construction
    (r"\b(ofNearestNeighborPositive_(?:term|term_eq_zero|term_eq_zero_of_card_one|operator|hamiltonian)"
     r"|ofBonds_operator|ofBonds_hamiltonian) (\w+) (\w+) (\w+) (\w+)\b", r"\1 \2 \3"),
    (r"\b(ofNearestNeighborPositive_term_nonneg|posSemidef_ofBonds_term) (\w+) (\w+) (\w+) (\w+)\b",
     r"\1 \2 \3 \4"),
    (r"\b(ofNearestNeighborPositive_term_le_one) (\w+) (\w+) (\w+) (\w+)\b", r"\1 \2 \3 \5"),
    (r"\.smul_(?:operator|hamiltonian) (\S+) \((?:[^()]|\([^()]*\))*\)", r".smul_hamiltonian \1"),
    # the rectangular interaction placed on the lattice: no bound, the hypotheses are lemmas
    (r"\((\w+'*)\.toAreaLawHamiltonian (?:\w+'*)\)\.operator_isHermitian\b",
     r"(ManyBody.Interaction.isHermitian_hamiltonian \1.isHermitian_toAreaLawHamiltonian_term)"),
    (r"\((\w+'*)\.toAreaLawHamiltonian (?:\w+'*)\)\.operator\b", r"\1.toAreaLawHamiltonian.hamiltonian"),
    (r"\((\w+'*)\.toAreaLawHamiltonian (?:\w+'*)\)", r"\1.toAreaLawHamiltonian"),
    (r"\.isGapped_toAreaLawHamiltonian (?:\w+'*) ", ".isGapped_toAreaLawHamiltonian "),
    (r"\.toAreaLawHamiltonian_operator (?:\w+'*) ", ".toAreaLawHamiltonian_hamiltonian "),
    # families of all models of a size: the hypotheses join the subtype condition
    (r"Σ L : ℕ, ChainHamiltonian L q R J ×", "Σ L : ℕ, ManyBody.ChainInteraction L q R ×"),
    (r"(\{a : Σ L : ℕ, ManyBody\.ChainInteraction L q R ×\s*EuclideanSpace ℂ \(Fin L → Fin q\) × ℝ //\s*"
     r"L₀ ≤ a\.1 ∧) ", r"\1 (∀ X, (a.2.1.term X).IsHermitian) ∧ (∀ X, ‖a.2.1.term X‖ ≤ J) ∧ "),
    (r"\ba\.2\.1\.operator\b", "a.2.1.hamiltonian"),
    # the sums and constructions: the hypotheses of the former fields are gone from them
    (rf"(?<![\w.]){QUAL}(?:ChainHamiltonian|DomainHamiltonian|LocalHamiltonian)\.operator\b(?!_)",
     "ManyBody.Interaction.hamiltonian"),
    (r"\b(ofBonds|ofNearestNeighborPositive) (\w+) (\w+) (\w+) (\w+)\b", r"\1 \2 \3"),
    (r"\.toChain (?!\(\w+'* :)(?:\((?:[^()]|\([^()]*\))*\)|\w[\w.']*)(?=[\s).,⟩])", ".toChain"),
    (r"\.toChain_(?:hamiltonian|operator) hJ\b", ".toChain_hamiltonian"),
    (r"\.toChain_term (?:\((?:[^()]|\([^()]*\))*\)|\w[\w.']*) ", ".toChain_term "),
    (r"\b(doubled|toChain)\.operator\b", r"\1.hamiltonian"),
    (r"(\((?:[^()]|\([^()]*\))*\b(?:swappedDoubled|smul|ofBonds|ofNearestNeighborPositive)\b"
     r"(?:[^()]|\([^()]*\))*\))\.operator\b", r"\1.hamiltonian"),
]


SECVAR = re.compile(rf"^variable((?:[^\n]|\n[ \t]+)*?)\((\w+'*) : {QUAL}(ChainHamiltonian|DomainHamiltonian|LocalHamiltonian) {ARG4}\)", re.M)


def section_variables(t):
    """A section variable `v : ChainHamiltonian ...`: the variable becomes the interaction with
    its two hypotheses, the API of `v` is rewritten up to the end of the section, and each
    declaration there whose proof uses a hypothesis includes it."""
    for m in list(SECVAR.finditer(t))[::-1]:
        v, old = m[2], m[3]
        H, HJ = hyp_names(v)
        new = STRUCTS[old]
        line = (f"variable{m[1]}({v} : {new} {m[4]} {m[5]} {m[6]}) ({H} : ∀ X, ({v}.term X).IsHermitian)"
                f" ({HJ} : ∀ X, ‖{v}.term X‖ ≤ {m[7]})")
        end = re.search(r"^end\b", t[m.end():], re.M)
        stop = m.end() + end.start() if end else len(t)
        body = t[m.end():stop]
        starts = [k.start() for k in DECL_START.finditer(body)] + [len(body)]
        out = [body[:starts[0]]]
        for a, b in zip(starts, starts[1:]):
            chunk = per_var(body[a:b], v)
            used = [x for x in (H, HJ) if re.search(rf"(?<![\w']){re.escape(x)}(?![\w'])", chunk)]
            if used and re.match(r"(?:@\[[^\n]*\]\s*)?(?:(?:private|protected)\s+)*(?:theorem|lemma)\b", chunk):
                inc = f"include {' '.join(used)} in\n"
                # before the docstring, which must stay next to the declaration
                d = re.search(r"/--(?:(?!-/).)*-/\n$", out[-1], re.S)
                if d:
                    out[-1] = out[-1][:d.start()] + inc + out[-1][d.start():]
                else:
                    chunk = inc + chunk
            out.append(chunk)
        nb = ''.join(out)
        t = t[:m.start()] + line + nb + t[stop:]
    return t


def process_text(t):
    for a, b in GLOBAL:
        t = re.sub(a, b, t)
    t = section_variables(t)
    for old, new in STRUCTS.items():
        t = re.sub(rf"(theorem|lemma|def) {old}\.([\w']+)",
                   lambda m: f"{m[1]} _root_.ManyBody.{new}.{hamName(m[2])}", t)
        t = re.sub(rf"(?<![\w.]){QUAL}{old}\.([a-z][\w']*)",
                   lambda m: f"ManyBody.{new}.{hamName(m[1])}", t)
    varre = re.compile(rf"(?:\(|∀ )(\w+'*) : {QUAL}(?:{'|'.join(STRUCTS)})\b")
    starts = [m.start() for m in DECL_START.finditer(t)] + [len(t)]
    out = [t[:starts[0]]]
    for a, b in zip(starts, starts[1:]):
        chunk = t[a:b]
        for v in sorted(set(varre.findall(chunk))):
            chunk = per_var(chunk, v)
        h = re.match(r"[^\n]*?(theorem|lemma|def|abbrev|instance|structure|example)\b\s*([\w.'«»]*)",
                     chunk)
        decl = h.group(2).split('.')[-1] if h else ''
        kind = h.group(1) if h else ''
        cut = len(h.group(0)) + len(signature(chunk, h.end())) if h else 0
        head, tail = chunk[:cut], chunk[cut:]
        for old, new in STRUCTS.items():
            for x, y in binders(old, new, decl, kind):
                head = re.sub(x, y, head)
                # inside a `∀` of the statement the hypotheses are never named
                tail = re.sub(x, lambda m, y=y: re.sub(r"\((h\w*'*) : ∀ X,", "(_ : ∀ X,", y(m)), tail)
        chunk = head + tail
        # a bound that no longer occurs leaves its binder
        if decl in DROP:
            for x in ('J',):
                body = re.sub(rf"\{{([^{{}}]*?)\b{x}\b([^{{}}]*?) : ℝ\}}", "", chunk, count=1)
                body = re.sub(r"/-.*?-/|--[^\n]*", "", body, flags=re.S)
                # the energy terms take the bound as an argument, inserted after this pass
                if not re.search(rf"(?<![\w']){x}(?![\w'])|\b(?:truncatedEnergyTerm|actualEnergyTerms|positiveTerm)\b", body):
                    def strip(m):
                        names = [n for n in m[1].split() if n != x]
                        return f"{{{' '.join(names)} : ℝ}}" if names else ''
                    chunk = re.sub(rf"\{{((?:[\w']+ )*{x}(?: [\w']+)*) : ℝ\}}", strip, chunk, count=1)
                    chunk = re.sub(r"(?<=\S) {2,}(?=\()", " ", chunk)
                    chunk = re.sub(r"[ \t]+\n", "\n", chunk)
            # a bound that the dropped hypothesis bound automatically, still used elsewhere
            head2 = chunk[:len(h.group(0)) + len(signature(chunk, h.end()))] if h else ''
            code = re.sub(r"/-.*?-/|--[^\n]*", "", chunk, flags=re.S)
            bound = re.search(r"[{(][^(){}]*(?<![\w'])J(?![\w'])[^(){}]*: ℝ[)}]", head2)
            if h and kind in ('theorem', 'lemma') and not bound and re.search(r"(?<![\w'.])J(?![\w'])", code):
                chunk = re.sub(r"\((\w+'*) : (?:ManyBody\.)?(?:ChainInteraction|DomainInteraction|PlaneInteraction) ",
                               lambda m: "{J : ℝ} " + m[0], chunk, count=1)
        out.append(chunk)
    return ''.join(out)


def ensure_open(t):
    needed = [n for n in STRUCTS.values() if re.search(rf"(?<![\w.]){n}\b(?!\.)", t)]
    for n in needed:
        m = re.search(r"^open ManyBody \(([^)]*)\)\n", t, re.M)
        if m and n in m.group(1).split():
            continue
        if m:
            names = m.group(1).split() + [n]
            line = 'open ManyBody (' + ' '.join(names) + ')'
            if len(line) > 100:
                lines, cur = [], 'open ManyBody ('
                for i, w in enumerate(names):
                    piece = w + (')' if i == len(names) - 1 else '')
                    if len(cur) + 1 + len(piece) > 100:
                        lines.append(cur.rstrip()); cur = '  ' + piece
                    else:
                        cur += ('' if cur.endswith('(') else ' ') + piece
                lines.append(cur); line = '\n'.join(lines)
            t = t[:m.start()] + line + '\n' + t[m.end():]
        else:
            d = re.search(r"^/-!.*?-/\n", t, re.M | re.S)
            t = t[:d.end()] + f'\nopen ManyBody ({n})\n' + t[d.end():]
    return t


def ensure_norm_scope(t):
    scoped = re.search(r"^open scoped [^\n]*\bMatrix\.Norms\.L2Operator\b(?![^\n]* in$)", t, re.M)
    if not scoped and re.search(r"‖[\w.']+\.term X‖", t):
        d = re.search(r"^/-!.*?-/\n", t, re.M | re.S)
        return t[:d.end()] + '\nopen scoped Matrix.Norms.L2Operator\n' + t[d.end():]
    return t


HEADS = re.compile(r"(?:theorem|lemma) _root_\.ManyBody\.(?:ChainInteraction|DomainInteraction|PlaneInteraction)\.([\w']+)")


def count_explicit(sig):
    """The number of explicit arguments bound by the binder groups `(a b : T)` of `sig`."""
    depth, k, i = 0, 0, 0
    while i < len(sig):
        c = sig[i]
        if c == '(' and depth == 0:
            m = re.match(r"\(((?:[\w'₀-₉]+ )*[\w'₀-₉]+) :", sig[i:])
            if m:
                k += len(m[1].split())
        if c in '([{⦃⟨':
            depth += 1
        elif c in ')]}⦄⟩':
            depth -= 1
        i += 1
    return k


def construction_hyps(v, name, args, H, HJ):
    """The Hermiticity and norm lemmas of the construction `v.name args`."""
    args = args.strip()
    sp = f" {args}" if args else ''
    if name == 'toChain':
        return f"({v}.isHermitian_toChain_term {H})", f"({v}.norm_toChain_term_le {HJ} hJ)"
    return f"({v}.isHermitian_{name}_term {H}{sp})", f"({v}.norm_{name}_term_le {HJ}{sp})"


def bond_receivers(chunk):
    """The bond constructions in `chunk`, with their two lemmas from `h0` and `h1`."""
    out = []
    for m in re.finditer(r"\(ManyBody\.ChainInteraction\.(ofBonds|ofNearestNeighborPositive) (\w+) (\w+)\)", chunk):
        c, a, b = m[1], m[2], m[3]
        out.append((m[0], f"(ManyBody.ChainInteraction.isHermitian_{c}_term {a} {b} h0)",
                    f"(ManyBody.ChainInteraction.norm_{c}_term_le {a} {b} h0 h1)", ()))
    for m in re.finditer(r"\b(?:let|set) (\w+'*) := ManyBody\.ChainInteraction\.(ofBonds|ofNearestNeighborPositive) (\w+) (\w+)\b", chunk):
        g, c, a, b = m[1], m[2], m[3], m[4]
        out.append((g, f"(ManyBody.ChainInteraction.isHermitian_{c}_term {a} {b} h0)",
                    f"(ManyBody.ChainInteraction.norm_{c}_term_le {a} {b} h0 h1)", ()))
    return out


KEYWORDS = {'exact', 'apply', 'refine', 'using', 'from', 'by', 'at', 'have', 'show', 'calc',
            'then', 'else', 'with', 'rw', 'simpa', 'simp', 'only', 'fun', 'return', 'obtain',
            'rcases', 'refine\'', 'convert', 'exacts', 'nlinarith', 'linarith', 'positivity'}


def in_argument_position(text, i):
    """Whether the term starting at `i` is an argument of an application before it."""
    before = text[:i].rstrip()
    if not before or before[-1] in '([,⟨←↦|{=:;⦃·':
        return False
    word = re.search(r"([\w'.]+)$", before)
    if word and word.group(1) in KEYWORDS:
        return False
    return before[-1].isalnum() or before[-1] in "_)'}⟩₀₁₂₃₄₅₆₇₈₉]"


def threaded(m, text):
    """`text`, parenthesized when the call it replaces stands as an argument."""
    return f"({text})" if in_argument_position(m.string, m.start()) else text


def thread_receiver(chunk, r, rH, rJ, guard, table, ptable):
    """Pass the two lemmas `rH`, `rJ` of the interaction `r` at its uses in `chunk`."""
    R_ = re.escape(r)
    ng = ''.join(rf"(?!\s+{re.escape(g)})" for g in tuple(guard) + (rH.split(' ')[0], rJ.split(' ')[0]))
    for name, (k, args) in table.items():
        pass_ = ' '.join(rH if x == 'H' else rJ for x in args)
        chunk = re.sub(rf"(?<![\w.]){R_}\.({re.escape(name)}(?: {ARG}){{{k}}})(?![\w'])(?![\w']){ng}",
                       lambda m: threaded(m, f"{r}.{m[1]} {pass_}"), chunk)
    for name, (k, args) in ptable.items():
        pass_ = ' '.join(rH if x == 'H' else rJ for x in args)
        chunk = re.sub(rf"(?<![\w.'])((?:[\w.]+\.)?{re.escape(name)}(?:\s+{ARG}){{{k}}})(\s+){R_}"
                       rf"(?![\w.']){ng}",
                       lambda m: f"{m[1]}{m[m.re.groups]}{r} {pass_}", chunk)
    return chunk


def thread_local_hypotheses(chunk, v, H, HJ):
    """Pass the hypotheses where `v` is an argument of a local hypothesis `hX ... v`, bound in
    `chunk` by `obtain`, `intro`, `fun` or a binder, whose statement quantifies over interactions."""
    V = re.escape(v)
    def rep(m):
        head = m[1]
        if head in (v, H, HJ) or not re.search(
                rf"(?:\(|⟨|, |\bintro [^\n]*|\bfun [^\n]*)(?<![\w']){re.escape(head)}(?:\s*:|⟩|,|\s)", chunk):
            return m[0]
        # the hypothesis must head its application, not be an argument of another one
        before = m.string[:m.start()].rstrip()
        prev = re.search(r"([\w'₀-₉.]+)$", before)
        if before and before[-1] not in "(⟨,=▸↦!|$;" and not (prev and prev[1] in (
                'exact', 'apply', 'refine', 'using', 'by', 'from', 'have', 'show', 'at', 'in', 'then', 'else')):
            return m[0]
        # a hypothesis with a visible type must quantify over interactions
        b = re.search(rf"\((?:[\w'₀-₉]+ )*{re.escape(head)}(?: [\w'₀-₉]+)* :((?:[^()]|\((?:[^()]|\([^()]*\))*\))*)\)", chunk)
        if (b and not re.search(r"(?:Chain|Domain|Plane)Interaction\b|[∀→]", b[1])
                and re.search(r"[=≤<∈]", b[1])
                and not re.search(rf"[⟨,]\s*{re.escape(head)}\s*[,⟩]", chunk)):
            return m[0]
        return f"{m[1]}{m[2]}{m[m.re.groups]}{v} {H} {HJ}"
    return re.sub(rf"(?<![\w.'])(h[\w'₀-₉]*)((?:[ \t]+(?!{V}\b){ARG})*?)([ \t]+|\n[ \t]+){V}(?![\w.'])(?!\s+{re.escape(H)}\b)"
                  rf"(?!\s+\({V}\.isHermitian)", rep, chunk)


def thread_hypotheses(files):
    """Pass the hypotheses at every dot-notation use, on an interaction variable, of a moved
    lemma whose signature now takes them right after the interaction."""
    table = {}
    for f in files:
        t = f.read_text()
        heads = list(HEADS.finditer(t))
        # lemmas declared inside a namespace block of an interaction
        for b in re.finditer(r"^namespace ManyBody\.(?:ChainInteraction|DomainInteraction|PlaneInteraction)$"
                             r"(.*?)^end ManyBody\.", t, re.M | re.S):
            heads += [m for m in re.finditer(r"^(?:theorem|lemma) ([\w']+)", t, re.M)
                      if b.start(1) <= m.start() < b.end(1)]
        for m in heads:
            sig = signature(t, m.end())
            v = re.search(r"\((\w+'*) : (?:ChainInteraction|DomainInteraction|PlaneInteraction)\b", sig)
            if not v:
                continue
            # dot notation fills the explicit arguments before the interaction first
            k = count_explicit(sig[:v.start()])
            H, HJ = hyp_names(v[1])
            args = [k for k, a in (('H', H), ('J', HJ)) if re.search(rf"\({re.escape(a)} :", sig)]
            if args:
                table[m.group(1)] = (k, args)
    # positional calls: every theorem taking an interaction and its hypotheses, with the number
    # of explicit arguments before the interaction
    ptable = {}
    anyhead = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected)\s+)*(?:theorem|lemma) ([\w.'«»]+)", re.M)
    for f in files:
        t = f.read_text()
        for m in anyhead.finditer(t):
            sig = signature(t, m.end())
            v = re.search(r"\((\w+'*) : (?:ChainInteraction|DomainInteraction|PlaneInteraction)\b", sig)
            if not v:
                continue
            H, HJ = hyp_names(v[1])
            args = [k for k, a in (('H', H), ('J', HJ)) if re.search(rf"\({re.escape(a)} :", sig)]
            k = count_explicit(sig[:v.start()])
            if args:
                ptable[m.group(1).split('.')[-1]] = (k, args)
    # theorems whose statement quantifies over interactions together with their hypotheses
    stable = set()
    for f in files:
        t = f.read_text()
        for m in anyhead.finditer(t):
            sig = signature(t, m.end())
            k = m.end() + len(sig)
            nxt = DECL_START.search(t, k + 1)
            stmt = t[k:nxt.start() if nxt else len(t)].split(':=')[0]
            if re.search(r"\((\w+'*) : (?:ManyBody\.)?(?:ChainInteraction|DomainInteraction|PlaneInteraction)\b[^()]*\)"
                         r"\s*\(_ : ∀ X, \(\1\.term X\)\.IsHermitian\)", stmt):
                stable.add(m.group(1).split('.')[-1])
    varre = re.compile(r"(?:\(|∀ )(\w+'*) : (?:ChainInteraction|DomainInteraction|PlaneInteraction)\b")
    secre = re.compile(r"^variable(?:[^\n]|\n[ \t]+)*?\((\w+'*) : (?:ChainInteraction|DomainInteraction|PlaneInteraction)\b", re.M)
    for f in files:
        t = f.read_text()
        for m in re.finditer(r"^include ([^\n]*) in\n(?:/--(?:(?!-/).)*-/\n)?(?:theorem|lemma) ([\w.'«»]+)", t, re.M | re.S):
            for sv in secre.findall(t):
                H, HJ = hyp_names(sv)
                inc = m[1].split()
                args = [k for k, a in (('H', H), ('J', HJ)) if a in inc]
                if args:
                    table[m[2].split('.')[-1]] = (0, args)
                    # dot notation on an earlier section variable, such as a scanner `S.name v`
                    ptable.setdefault(m[2].split('.')[-1], (0, args))
    for f in files:
        t = f.read_text()
        secvars = set(secre.findall(t))
        starts = [m.start() for m in DECL_START.finditer(t)] + [len(t)]
        out = [t[:starts[0]]]
        for a, b in zip(starts, starts[1:]):
            chunk = t[a:b]
            # aliases of constructed interactions
            for m in re.finditer(r"\b(?:let|set) (\w+'*)(?: : [^\n]*?)? := (?:\(?\w+'*\.(?:doubled|swappedDoubled|toChain|smul)\b"
                                 r"|ManyBody\.ChainInteraction\.(?:ofBonds|ofNearestNeighborPositive)\b)", chunk):
                chunk = re.sub(rf"(?<![\w.]){re.escape(m[1])}\.operator\b", f"{m[1]}.hamiltonian", chunk)
            for r, rH, rJ, guard in bond_receivers(chunk):
                chunk = thread_receiver(chunk, r, rH, rJ, guard, table, ptable)
            # interactions introduced together with their hypotheses, as in `intro Λ h hh hhJ`
            intro_vars = {m[1] for m in re.finditer(r"(?<![\w.'])(?=([\w']+)(?: |, )([\w']+)(?: |, )([\w']+)(?![\w']))", chunk)
                          if m[1][0].isalpha() and hyp_names(m[1]) == (m[2], m[3])}
            for v in set(varre.findall(chunk)) | secvars | intro_vars:
                # a declaration that binds the name to something else, such as a history `h`
                if re.search(rf"\({re.escape(v)} : (?!(?:ManyBody\.)?(?:Chain|Domain|Plane)Interaction\b)", chunk):
                    continue
                H, HJ = hyp_names(v)
                # the interaction itself, and the interactions constructed from it
                recv = [(v, H, HJ, (H, HJ)),
                        (f"({v}.toChain)", f"({v}.isHermitian_toChain_term {H})",
                         f"({v}.norm_toChain_term_le {HJ} hJ)", (H,))]
                # a rescaling keeps only the factor; its sign condition goes to the norm lemma
                for m in list(re.finditer(rf"\({re.escape(v)}\.smul ({ARG}) ({ARG})\)", chunk))[::-1]:
                    chunk = chunk[:m.start()] + f"({v}.smul {m[1]})" + chunk[m.end():]
                    recv.append((f"({v}.smul {m[1]})", f"({v}.isHermitian_smul_term {H} {m[1]})",
                                 f"({v}.norm_smul_term_le {HJ} {m[1]} {m[3]})", ()))
                for m in re.finditer(rf"\(({re.escape(v)}\.(doubled|swappedDoubled|toChain)((?: {ARG})*))\)", chunk):
                    recv.append((m[0],) + construction_hyps(v, m[2], m[3], H, HJ) + ((H,),))
                for m in re.finditer(rf"\b(?:let|set) (\w+'*)(?: : [^\n]*?)? := ({re.escape(v)}\.(doubled|swappedDoubled|toChain)((?: {ARG})*))\s*(?:with \w+)?\n", chunk):
                    rH, rJ = construction_hyps(v, m[3], m[4], H, HJ)
                    g = re.escape(m[1])
                    chunk = re.sub(rf"(?<![\w.]){g}\.supported\b", f"{m[1]}.mem", chunk)
                    chunk = re.sub(rf"(?<![\w.]){g}\.hermitian\b", rH, chunk)
                    chunk = re.sub(rf"(?<![\w.]){g}\.norm_le\b", rJ, chunk)
                    recv.append((m[1], rH, rJ, (rH,)))
                for r, rH, rJ, guard in recv:
                    chunk = thread_receiver(chunk, r, rH, rJ, guard, table, ptable)
                chunk = thread_local_hypotheses(chunk, v, H, HJ)
                if stable:
                    V = re.escape(v)
                    chunk = re.sub(
                        rf"(?<![\w.'])((?:[\w.]+\.)?(?:{'|'.join(map(re.escape, sorted(stable)))})(?![\w'])"
                        rf"(?:[ \t]+{ARG}|\n[ \t]+{ARG})*?)([ \t]+|\n[ \t]+){V}(?![\w.'])"
                        rf"(?!\s+{re.escape(H)}\b)(?!\s+_\b)(?!\s+\({V}\.isHermitian)",
                        lambda m: f"{m[1]}{m[m.re.groups]}{v} {H} {HJ}", chunk)
            out.append(chunk)
        n = ''.join(out)
        for sv in secvars:
            n = fix_includes(n, sv)
        if n != t:
            f.write_text(wrap(t, n))


def fix_includes(t, v):
    """In the section of the variable `v`, include the hypotheses each theorem now uses."""
    H, HJ = hyp_names(v)
    m = re.search(rf"^variable(?:[^\n]|\n[ \t]+)*?\({re.escape(v)} : (?:ChainInteraction|DomainInteraction|PlaneInteraction)\b[^\n]*\n", t, re.M)
    if not m:
        return t
    end = re.search(r"^end\b", t[m.end():], re.M)
    stop = m.end() + end.start() if end else len(t)
    body = t[m.end():stop]
    starts = [k.start() for k in DECL_START.finditer(body)] + [len(body)]
    out = [body[:starts[0]]]
    for a, b in zip(starts, starts[1:]):
        chunk = body[a:b]
        if re.match(r"(?:@\[[^\n]*\]\s*)?(?:(?:private|protected)\s+)*(?:theorem|lemma)\b", chunk):
            prev = out[-1]
            d = re.search(r"(include ([^\n]*) in\n)?(/--(?:(?!-/).)*-/\n)?$", prev, re.S)
            have = d[2].split() if d and d[2] else []
            code = re.sub(r"/-.*?-/|--[^\n]*|^include [^\n]*$", "", chunk, flags=re.S | re.M)
            # a theorem whose statement quantifies over its own interaction rebinds the names
            if re.search(rf"\b(?:intro|rintro|fun)(?: [\w'₀-₉]+)*? (?:{re.escape(v)} )?{re.escape(H)} {re.escape(HJ)}(?![\w'])", code):
                code = ''
            used = [x for x in (H, HJ) if re.search(rf"(?<![\w']){re.escape(x)}(?![\w'])", code)]
            want = [x for x in (H, HJ) if x in used]
            if want != have:
                inc = f"include {' '.join(want)} in\n" if want else ''
                out[-1] = prev[:d.start()] + inc + (d[3] or '')
        out.append(chunk)
    return t[:m.end()] + ''.join(out) + t[stop:]


def docs_pass():
    """The declaration names in the blueprint and the docs (audit records excepted)."""
    out = subprocess.run(['git', 'ls-files', 'blueprint/src', 'docs'], capture_output=True,
                         text=True).stdout.split()
    n = 0
    for f in out:
        if not f.endswith(('.tex', '.md')) or f.startswith('docs/audits/'):
            continue
        p = pathlib.Path(f); t = p.read_text(); u = t
        for old, new in STRUCTS.items():
            u = re.sub(rf"(?<![\w.]){QUAL}{old}\.operator_isHermitian\b",
                       "ManyBody.Interaction.isHermitian_hamiltonian", u)
            u = re.sub(rf"(?<![\w.]){QUAL}{old}\.operator\b(?!_)", "ManyBody.Interaction.hamiltonian", u)
            u = re.sub(rf"(?<![\w.]){QUAL}{old}\.([a-z][\w']*)",
                       lambda m, new=new: f"ManyBody.{new}.{hamName(m[1])}", u)
            u = re.sub(rf"(?<![\w.]){QUAL}{old}\b", f"ManyBody.{new}", u)
        if u != t:
            n += 1
            if WRITE:
                p.write_text(u)
    print(n, 'doc files')


def main():
    if '--docs' in sys.argv:
        return docs_pass()
    changed = []
    for f in lean_files():
        t = f.read_text()
        if not re.search('|'.join(list(STRUCTS) + ['toAreaLawHamiltonian']), t):
            continue
        n = ensure_norm_scope(ensure_open(process_text(t)))
        if n != t:
            n = wrap(t, n)
            changed.append(str(f))
            if WRITE:
                f.write_text(n)
    print(len(changed), 'files'); print('\n'.join(changed))


if '--thread' in sys.argv:
    thread_hypotheses([f for f in lean_files() if f.exists() and
                       re.search(NEWS, f.read_text())])
else:
    main()
