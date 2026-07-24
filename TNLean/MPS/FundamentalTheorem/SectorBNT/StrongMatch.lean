/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.ProportionalMatch.Core

/-!
# Strong existential and bijective sector matching

The strong existential matching theorem states the CPSV16 Appendix MPV proof,
line 1182, matching conclusion directly on the original pair `(P, Q)` of BNT
canonical forms.  In the equal-MPV case both theorems reduce to their
proportional-sector counterparts via the
`SameMPV₂Pos → EventuallyNonzeroProportionalMPV₂` conversion, and the
bijection step is the shared construction `bijection_from_matches`.

The coefficient identity of CPSV16 Appendix MPV proof, lines 1187–1188
(Corollary substitution) lives in the companion module
`SectorBNT/CoeffIdentity.lean`.

## Paper anchor

CPSV16 (arXiv:1606.00608) Appendix MPV proof, line 1182, gives the matching
step of the proportional theorem proof.  The equal-vector corollary gives an
index $j_k$ with $|V^{(N)}(B_k)\rangle = |V^{(N)}(A_{j_k})\rangle$, and the
single-block fundamental theorem gives $B_k = X_k A_{j_k} X_k^{-1}$.
-/

open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-! ### Strong existential matching: CPSV16 Appendix MPV proof, line 1182 -/

/-- **CPSV16 Appendix MPV proof, line 1182, Step 1 (full-basis form).**

Suppose that the total tensors of `P` and `Q` generate the same MPV family at
every positive length.  For every sector `k` of `Q`, there exists a sector `j`
of `P` of equal bond dimension, gauge-phase equivalent to `Q.basis k` after the
dimension cast, and with non-decaying cross-overlap.

This is derived from the proportional sector-matching lemma
`forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional` using the
conversion `SameMPV₂Pos.toNonzeroProportionalMPV₂.eventually`.

Paper anchor: CPSV16 Appendix MPV proof, line 1182 (arXiv:1606.00608), CPSV21
Definition 4.2 lines 1846–1850, and the two-layer display at lines 1864–1884. -/
theorem forall_k_exists_j_nondecaying_overlap_of_sameMPV
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∀ k : Fin Q.basisCount, ∃ (j : Fin P.basisCount) (h : P.basisDim j = Q.basisDim k),
      GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) h) (P.basis j))
          (Q.basis k) ∧
      ¬ Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j) (Q.basis k) N)
        atTop (𝓝 0) :=
  forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional hP hQ
    (hEqual.toNonzeroProportionalMPV₂.eventually)

/-! ### Bijective sector matching by symmetry -/

/-- **CPSV16 Appendix MPV proof, line 1182, full-basis bijection.**

Applying `forall_k_exists_j_nondecaying_overlap_of_sameMPV` in both
directions gives injective maps `Fin Q.basisCount → Fin P.basisCount` and
`Fin P.basisCount → Fin Q.basisCount`.  Finite cardinal comparison turns
the forward injection into an equivalence `β : Fin Q.basisCount ≃
Fin P.basisCount`, carrying the matched bond-dimension equality,
gauge-phase equivalence, and non-decaying overlap for every sector of `Q`.

The proof derives both directions from the proportional matching lemma
`forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional` using the
`SameMPV₂Pos → NonzeroProportionalMPV₂` conversion, then delegates to the
shared bijection construction `bijection_from_matches`. -/
theorem bijective_match_of_sameMPV
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ β : Fin Q.basisCount ≃ Fin P.basisCount,
      ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis (β k)))
            (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis (β k)) (Q.basis k) N)
          atTop (𝓝 0) := by
  have hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor :=
    hEqual.toNonzeroProportionalMPV₂.eventually
  have hProp_symm : EventuallyNonzeroProportionalMPV₂ Q.toTensor P.toTensor :=
    hProp.symm
  have hFwd := forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional hP hQ hProp
  have hBwd := forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional hQ hP hProp_symm
  exact bijection_from_matches hP hQ hFwd hBwd

end MPSTensor
