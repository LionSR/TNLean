---
layout: default
---

TNLean is a [Lean 4](https://lean-lang.org/) formalization of tensor-network
theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

Its first released part is the **fundamental theorem of matrix product
states**: two tensors generate the same quantum states at every system size
exactly when an invertible gauge transformation on the bond indices relates
them. Chapters 1&ndash;12 of the blueprint contain this theorem, the theory
its proof rests on (quantum channels, Perron&ndash;Frobenius theory, the
quantum Wielandt inequality, canonical forms), and a first application to
symmetry-protected topological phases. This part is available as a separate
PDF via the "Blueprint ch. 1&ndash;12" button above.

The library goes beyond these chapters: parent Hamiltonians, matrix-product
density operators and renormalization fixed points, correlation decay,
quantum Markov semigroups, entropy inequalities, and projected entangled pair
states are developed in the later blueprint chapters and in the source tree,
at varying levels of completeness.

The header buttons link to the blueprint (web and full PDF), the
fundamental-theorem volume (chapters 1&ndash;12), the API documentation, and
the source code.

## Companion Paper

The companion paper "Autoformalizing the fundamental theorem of matrix product
states: A multi-agent, blueprint-guided formalization in Lean 4" is in
preparation. A bibliographic citation and public link will be added here once
the paper is available.
