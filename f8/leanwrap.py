import re, sys

def split_segments(s):
    i, n, start, out = 0, len(s), 0, []

    def flush(j):
        nonlocal start
        if j > start:
            out.append(('code', s[start:j]))
        start = j
    while i < n:
        if s.startswith('--', i):
            flush(i); j = s.find('\n', i); j = n if j < 0 else j
            out.append(('comment', s[i:j])); start = i = j
        elif s.startswith('/-', i):
            flush(i); depth, j = 1, i + 2
            while j < n and depth:
                if s.startswith('/-', j): depth += 1; j += 2
                elif s.startswith('-/', j): depth -= 1; j += 2
                else: j += 1
            out.append(('comment', s[i:j])); start = i = j
        elif s[i] == '"' and (i == 0 or s[i - 1] != "'"):
            flush(i); j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            out.append(('string', s[i:j + 1])); start = i = j + 1
        else:
            i += 1
    flush(n)
    return out



def comment_mask(text):
    mask, pos = [False] * len(text), 0
    for kind, seg in split_segments(text):
        if kind == 'comment':
            mask[pos:pos + len(seg)] = [True] * len(seg)
        pos += len(seg)
    return mask


def wrap_line(line, is_comment, maxlen=100):
    """Split one line at the last space before maxlen, preferring the outermost bracket level."""
    if len(line) <= maxlen:
        return [line]
    ind = len(line) - len(line.lstrip())
    cuts = [k for k in range(ind + 1, maxlen + 1) if line[k] == ' '
            and line.count('`', 0, k) % 2 == 0 and line[k - 1] != ' '
            and not line.startswith(':=', k + 1) and k > ind + 24]
    if not cuts:
        return [line]

    def depth(k):
        d = 0
        for ch in line[ind:k]:
            d += ch in '([{⟨'
            d -= ch in ')]}⟩'
        return d
    if is_comment:
        k = cuts[-1]
    else:
        cand = [k for k in cuts if len(line) - k - 1 >= 15] or cuts
        dmin = min(depth(c) for c in cand)
        top = [k for k in cand if depth(k) == dmin]
        ops = [k for k in top if line[:k].endswith(('↔', ' =', '≠', '∧', '∨', '→', ',', '≤', ' <'))]
        k = (ops or top)[-1]
    first = line[:k]
    cont = line[k + 1:]
    # continuation lines keep the indentation of an earlier continuation
    cind = ind if is_comment else (ind + 4 if not getattr(wrap_line, 'cont', False) else ind)
    wrap_line.cont = True
    rest = wrap_line(' ' * cind + cont, is_comment, maxlen)
    wrap_line.cont = False
    return [first] + rest


def wrap(old, new, maxlen=100):
    oldlines = set(old.split('\n'))
    mask, out, off = comment_mask(new), [], 0
    for line in new.split('\n'):
        start = off; off += len(line) + 1
        if len(line) <= maxlen or line in oldlines or line.lstrip().startswith('--'):
            out.append(line); continue
        ind = len(line) - len(line.lstrip())
        wrap_line.cont = False
        pieces = wrap_line(line, mask[start + ind], maxlen)
        if '--log-wraps' in sys.argv:
            print('WRAP\n' + '\n'.join(pieces), file=sys.stderr)
        out.extend(pieces)
    return '\n'.join(out)


