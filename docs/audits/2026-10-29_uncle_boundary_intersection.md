# The finite-chain single-domain-wall boundary space

Issue #10285; native tracker #7685. Baseline main `3af48c184`.
Source: `Papers/1210.6613/UncleHMPS.tex:1077–1098,1768–1940`,
equation defining S_n and the Appendix intersection proof, arXiv:1210.6613.

## Actual boundary family

`UncleBoundaryProduct.lean` defines the explicit bilinear product on the existing
full matrix vector space. Its four blocks are `(AA′, AR′+RB′, LA′+BL′, BB′)`.
It is associative and unital; no new algebra structure or parallel injectivity
predicate is introduced. Ordinary full-matrix multiplication would introduce
alternating walls and therefore would describe the wrong finite-chain family.

`UncleBoundaryWords.lean` defines coefficient words using that product, proves
the exact sum over every position of a single R or L wall, and defines the source
S_n as the range of the actual trace boundary map. At two original physical sites
the coefficient is exactly the already defined uncle tensor letter, and
`uncleBoundaryMap_two` identifies the map with the existing ground-space map.

## Derived reconstruction

Full perturbation injectivity is the existing `Kraus.IsInjective` condition on
the full letters C_i. The identity belongs to their span, so coefficients c_i
satisfy sum c_i C_i=I. Contracting a first physical letter against these
coefficients removes that letter. This proves full coefficient span at every
positive length. No uncle injectivity, genericity, inverse coefficients, or
intersection property is supplied as an additional hypothesis.

`UncleBoundaryIntersection.lean` proves that fixing either endpoint preserves S_n
and derives the reverse overlap inclusion. If X_k and Y_i describe the two
restrictions, their compatibility gives Z=sum c_i Y_i and
trace(F(w) X_k)=trace(F(wk) Z). The full span on the positive-length middle word
extends the identity to all matrices. Evaluation on the longer prefix then
reconstructs the common boundary Z. Mathlib's `LinearMap.ext_on_range` and the
existing finite-matrix trace representation theorem implement the two span and
duality steps. No new dual structure is needed.

The theorem states window lengths n+2 and total lengths n+3. This follows the
Appendix's explicit base case S_2 and induction for k>2. It makes the positive
middle length visible rather than silently claiming the generally false
one-site intersection identity. Arbitrary natural virtual dimensions are
allowed, and no dimension, irreducibility, gauge, or normalization premise is
added.

## Remaining work and verification

This slice does not assert the periodic uncle Hamiltonian kernel equality.
Periodic closure and the assembly with actual local-kernel constraints are
separate work, and no closure premise has been substituted for either proof.
The existing `contiguous_mem_of_restriction_intersection_submodules` theorem
can consume this intersection identity for the open-chain induction.

These are source-written proof candidates. The user explicitly requested no
local Lean invocation, so no local compilation or builds were run. Source/API
inspection, generated-import checks, formatting, tactic scanning and integrity
checks do not establish Lean acceptance. New Blueprint nodes remain notready;
the issue remains open pending verification and integration. No placeholders,
new axioms or persistent Lean fixtures are added.
