#!/usr/bin/env python3
"""Check finite-state output recovery for small monomial quantum unitaries.

The exact row-rank estimate and two parallel computations are described in
``docs/audits/2026-10-02_mpu_finite_alphabet_circuits.tex``. This script
constructs residual tables by enumeration for small examples, verifies their
rank bounds, and checks output recovery and inverse erasure on every input.
Enumeration here is for verification; the note gives a different construction
from MPO tensors. These checks do not verify a compiled quantum circuit.

Requires SymPy. Run from any directory with Python 3.
"""

from itertools import product, permutations
from random import Random
from sympy import I, Matrix

LETTERS = tuple(product((0, 1), repeat=2))


def residual_automaton(n, perm, phases):
    words = [tuple(product(LETTERS, repeat=k)) for k in range(n + 1)]
    def coeff(w):
        y = sum(a << (n - j - 1) for j, (a, _) in enumerate(w))
        x = sum(b << (n - j - 1) for j, (_, b) in enumerate(w))
        return phases[x] if perm[x] == y else 0
    states, labels, ranks = [], [], []
    for k in range(n + 1):
        rows = [tuple(coeff(p + s) for s in words[n-k]) for p in words[k]]
        distinct = tuple(dict.fromkeys(rows))
        states.append(distinct)
        labels.append({p: distinct.index(row) for p, row in zip(words[k], rows)})
        rank = Matrix(distinct).rank()
        assert len(distinct) <= len(set(phases) | {0}) ** rank
        ranks.append(rank)
    transitions = []
    for j in range(n):
        representatives = {}
        for p, q in labels[j].items():
            representatives.setdefault(q, p)
        transitions.append([[labels[j+1][p + (c,)] for c in LETTERS]
                            for _, p in sorted(representatives.items())])
    return states, transitions, ranks


def bool_mul(a, b):
    return [[any(x and y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def suffix_products(items):
    if not items:
        return []
    if len(items) == 1:
        return [items[0]]
    k = len(items) // 2
    left, right = suffix_products(items[:k]), suffix_products(items[k:])
    return [bool_mul(x, right[0]) for x in left] + right


def prefix_functions(items):
    if not items:
        return []
    if len(items) == 1:
        return [items[0]]
    k = len(items) // 2
    left, right = prefix_functions(items[:k]), prefix_functions(items[k:])
    return left + [[f[q] for q in left[-1]] for f in right]


def recover(n, states, transitions, x):
    bits = [(x >> (n-j-1)) & 1 for j in range(n)]
    width = max(map(len, states))
    delta = []
    for j, layer in enumerate(transitions):
        delta.append(layer + [layer[0]] * (width-len(layer)))
    e = []
    for j in range(n):
        e.append([[any(delta[j][q][2*a + bits[j]] == r for a in (0,1))
                   for r in range(width)] for q in range(width)])
    suffix = suffix_products(e)
    t = [bool(states[n][q][0]) if q < len(states[n]) else False for q in range(width)]
    flags = [[any(v and w for v, w in zip(row, t)) for row in mat] for mat in suffix]
    flags.append(t)
    choices, h = [], []
    for j in range(n):
        a = [0 if flags[j+1][delta[j][q][bits[j]]] else 1
             if flags[j+1][delta[j][q][2+bits[j]]] else 0 for q in range(width)]
        choices.append(a)
        h.append([delta[j][q][2*a[q] + bits[j]] for q in range(width)])
    prefix = prefix_functions(h)
    q = [0] + [f[0] for f in prefix]
    y = sum(choices[j][q[j]] << (n-j-1) for j in range(n))
    return y, states[n][q[n]][0]


def check(n, perm, phases):
    states, delta, ranks = residual_automaton(n, perm, phases)
    for x in range(1 << n):
        assert recover(n, states, delta, x) == (perm[x], phases[x])
    inverse = [perm.index(y) for y in range(1 << n)]
    # Transposing the relation changes the placement of phases, but not the alphabet.
    inverse_phases = [phases[inverse[y]] for y in range(1 << n)]
    states_i, delta_i, ranks_i = residual_automaton(n, inverse, inverse_phases)
    assert ranks == ranks_i
    for x in range(1 << n):
        y, phase = recover(n, states, delta, x)
        back, _ = recover(n, states_i, delta_i, y)
        assert x ^ back == 0 and phase == phases[x]
    return max(ranks), [len(q) for q in states]


count = 0
for perm in permutations(range(4)):
    for phases in product((-1, 1), repeat=4):
        check(2, list(perm), list(phases))
        count += 1
rng = Random(5704)
for n, cases in ((3, 24), (4, 12)):
    for _ in range(cases):
        perm = list(range(1 << n))
        rng.shuffle(perm)
        phases = [rng.choice((1, -1, I, -I)) for _ in perm]
        check(n, perm, phases)
        count += 1
for n in range(2, 6):
    perm = list(range(1 << n))
    perm[-2], perm[-1] = perm[-1], perm[-2]
    rank, widths = check(n, perm, [1] * len(perm))
    print(f'multi-controlled NOT: N={n}, maximum cut rank={rank}, residual counts={widths}')
    count += 1
print(f'Exact parallel reconstruction and inverse erasure verified for {count} monomial unitaries.')
