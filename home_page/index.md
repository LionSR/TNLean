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
PDF via the "FT&ndash;MPS Blueprint" button above. The quantum-channel
theory itself now lives in the companion library
[QICLean](https://github.com/LionSR/QICLean), with its own blueprint and
documentation at [sirui-lu.com/QICLean](https://sirui-lu.com/QICLean/);
TNLean depends on it as an ordinary Lake package.

The library goes beyond these chapters: parent Hamiltonians, matrix-product
density operators and renormalization fixed points, correlation decay, and
projected entangled pair states are developed in the later blueprint
chapters and in the source tree, at varying levels of completeness.

## Paper-Gap Notes

Where the formalization deviates from a cited source &mdash; a missing
hypothesis, a scalar correction, a scope restriction, a replacement proof
route &mdash; the deviation is recorded as a standalone mathematical note.
The [paper-gap notes](paper-gaps/) are indexed by source paper; each note has
a stable link, a PDF, and a citation entry.

## Companion Paper

S. Lu, E. Tjoa, J. I. Cirac, *Multi-agent Autoformalization of Tensor Network
Theory*, [arXiv:2607.07857](https://arxiv.org/abs/2607.07857).

Most of the formalization was carried out by agents running on
[TeXRA](https://texra.ai), whose `lean-env-action` also sets up the Lean and
blueprint toolchain used throughout this repository's CI workflows.
