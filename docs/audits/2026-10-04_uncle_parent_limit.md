# Two-block uncle parent limit

Source: `Papers/1210.6613/UncleHMPS.tex`, continuity lemma at 314–340,
span-change lemma at 890–902, and uncle form theorem at 912–953.

The actual canonical two-site parent projector is used throughout. The
rescaling multiplies both off-diagonal virtual blocks by the same scalar.
It is an invertible linear map on virtual matrices, not in general a bond
similarity. Its self-duality for the bilinear trace pairing proves equality
of the physical boundary-map ranges.

The rescaled blocked tensor has a polynomial continuation through zero.
Its zero value is exactly the printed uncle tensor. The existing QIC inverse
Gram formula and Mathlib openness of injectivity localize TNLean's global
projector-continuity API. The existing global theorem is retained as a
short consequence of the stronger local theorem, avoiding duplicate inverse
Gram proofs. No injectivity assumption is imposed away from
the base point. This is the source's continuous-basis argument expressed
through the Gram inverse instead of new Gram–Schmidt infrastructure.

The local convergence is transported through the existing physical-blocking
isometry. The actual periodic parent Hamiltonian then converges through the
existing averaged cyclic-restriction formula. Both complex punctured limits
and the real-parameter specialization are recorded at every fixed N≥2.
The two-site ring keeps the existing ordered-window convention.

The proof only requires injectivity of the explicit uncle tensor. The
source's block-injectivity hypothesis for A⊕B is not needed for this local
limit argument. This extends the algebraic operator-limit statement; it does
not assert every physical interpretation of an uncle Hamiltonian for block
data outside the source standard form. There is no stronger hypothesis
hidden in the signature.
Diagonal perturbations disappear from the explicit limit; the off-diagonal
perturbations remain. Generic gaplessness and algebraic exceptional-set
claims are separate source results and remain open under #7685.

A fresh audit of all 48 open PR filename lists found no overlap with the
changed continuity module or the new uncle modules/chapter. PR #8531 adds a
different block-ground-space continuity file and edits a separate blueprint
fragment, which this change does not modify.
