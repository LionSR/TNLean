/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.DominantMatch

/-!
# Strong existential and bijective sector matching (CPSV16 §II.C line 1182)

The strong existential matching theorem states the CPSV16 §II.C line 1182
*Step 1* conclusion directly on the original pair `(P, Q)` of BNT canonical
forms, iterated over each sector `k` of `Q` that carries a unit-modulus copy.

The coefficient identity of CPSV16 §II.C lines 1187–1188 (Corollary substitution)
lives in the companion module `SectorBNT/CoeffIdentity.lean`.

## Paper anchor

CPSV16 (arXiv:1606.00608) §II.C line 1182 gives the *entire* matching step
of the proportional theorem proof.  In mathematical terms, this step fixes a
block $B_k$ and observes that its overlaps with the $A_j$ blocks cannot all
decay to zero, since then the two MPV families would fail to be proportional
for all lengths.  The equal-vector corollary then gives an index $j_k$ with
$|V^{(N)}(B_k)\rangle = e^{i\phi_k N} |V^{(N)}(A_{j_k})\rangle$, and the
single-block fundamental theorem gives
$B_k = e^{i\phi_k} X_k A_{j_k} X_k^{-1}$.

The paper's "given $k$" is *iterated externally* over each unit-block
sector of `Q` (those with at least one unit-modulus weight, per the
CPSV16 §II.C line-246 normalization which is recorded **globally** —
not per-block — in `IsBNTCanonicalForm.weight_unit_exists`).  Non-unit
blocks contribute coefficients that decay exponentially and so do not
constrain the matching; the paper restricts attention to the
"physical" (unit-modulus carrying) blocks.

## Proof structure

The result is a **single `∀ k, ∃ j` existential statement** on the
original pair, with the paper's "given $k$" hypothesis explicitly
encoded as the unit-modulus existential.  There is **no recursion**,
no `dropSector` usage, and no combined-LI obligation on a partial
union: the entire proof routes through the existing
`exists_block_match_of_sameMPV` lemma (which itself routes
through the full-family combined LI `combined_family_eventually_li`,
`SectorBNT/Api.lean`).

The bijective matching (`bijective_match_of_sameMPVPos`) applies the
forward existential twice — once with `(P, Q)` and once with `(Q, P)` —
to derive `P.basisCount = Q.basisCount` and the full bijection
`β : Fin Q.basisCount ≃ Fin P.basisCount`.

## Proof of the existential

Given a sector `k` of `Q` with a unit-modulus weight, apply the
existing `exists_block_match_of_sameMPV` (`SectorBNT/DominantMatch`)
**with `P` and `Q` swapped**:

* feed `hQ`, `hP` (in that order);
* supply `hP_pos : 0 < P.basisCount` from `hP.weight_unit_exists`
  (which exists globally on `P`);
* supply the unit-modulus witness on `Q`'s `k` (the hypothesis of this
  theorem); and
* supply `SameMPV₂ Q.toTensor P.toTensor` via the trivial symmetric
  flip of `hEqual` (pointwise `.symm`).

The result is a `j₀ : Fin P.basisCount` with `Q.basisDim k = P.basisDim j₀`,
a gauge-phase equivalence in the `Q → P` cast direction, and a
non-decaying overlap in the `(Q.basis k, P.basis j₀)` order.  Two
local auxiliary lemmas (`gaugePhaseEquiv_swap_cast` and
`tendsto_mpvOverlap_zero_swap`) flip those into the `(P, Q)`-ordered
conclusion.

All proofs in this file are closed constructively.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-! ### Strong existential matching: CPSV16 §II.C line 1182 -/

/-- **CPSV16 §II.C line 1182 Step 1 (full-basis form).**

For every sector `k` of `Q`, there exists a sector `j` of `P` of equal
bond dimension, gauge-phase equivalent to `Q.basis k` after the dimension
cast, and with non-decaying cross-overlap.

The proof iterates `exists_block_match_of_sameMPV` over every `Q`-sector
with `(P, Q)` swapped, so it consumes the per-block unit-modulus
witnesses on the *swapped* side, namely `hUnitQ : ∀ k, ∃ q, ‖μ_{k,q}‖ = 1`
for $Q$.  The per-block unit-modulus convention is paper-implicit in
CPSV16 §II.C line 1182's projection argument; it is taken here as an
explicit theorem-level hypothesis (CPSV16 §II.C line 246 records only
the global unit witness).

Paper anchor: CPSV16 §II.C line 1182 (arXiv:1606.00608), CPSV21
Definition 4.2 lines 1846–1850, and the two-layer display at lines 1864–1884. -/
theorem forall_k_exists_j_nondecaying_overlap_of_sameMPVPos
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∀ k : Fin Q.basisCount, ∃ (j : Fin P.basisCount) (h : P.basisDim j = Q.basisDim k),
      GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) h) (P.basis j))
          (Q.basis k) ∧
      ¬ Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j) (Q.basis k) N)
        atTop (𝓝 0) := by
  classical
  intro k
  -- `P.basisCount > 0`: the global unit witness on `P` supplies a sector index.
  have hP_pos : 0 < P.basisCount := by
    obtain ⟨j₀, _, _⟩ := hP.weight_unit_exists
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) j₀.isLt
  have hQ_pos : 0 < Q.basisCount := Nat.lt_of_le_of_lt (Nat.zero_le _) k.isLt
  have hEqual_symm : SameMPV₂Pos Q.toTensor P.toTensor := hEqual.symm
  obtain ⟨j, hsymDim, hGE_swapped, hNonDecay_swapped⟩ :=
    exists_block_match_of_sameMPVPos
      (P := Q) (Q := P) hQ hP k (hUnitQ k) hQ_pos hP_pos hEqual_symm
  refine ⟨j, hsymDim.symm, ?_, ?_⟩
  · exact gaugePhaseEquiv_swap_cast hsymDim.symm
      (by simpa using hGE_swapped)
  · intro hTend
    apply hNonDecay_swapped
    exact tendsto_mpvOverlap_zero_swap (P.basis j) (Q.basis k) hTend

/-- Reformulation for the all-length `SameMPV₂` form. -/
theorem forall_k_exists_j_nondecaying_overlap_of_sameMPV
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∀ k : Fin Q.basisCount, ∃ (j : Fin P.basisCount) (h : P.basisDim j = Q.basisDim k),
      GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) h) (P.basis j))
          (Q.basis k) ∧
      ¬ Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j) (Q.basis k) N)
        atTop (𝓝 0) :=
  forall_k_exists_j_nondecaying_overlap_of_sameMPVPos
    (P := P) (Q := Q) hP hQ hUnitQ hEqual.toSameMPV₂Pos

/-! ### Bijective sector matching by symmetry -/

/-- **CPSV16 §II.C line 1182 full-basis bijection.**

Applying `forall_k_exists_j_nondecaying_overlap_of_sameMPV` in both
directions gives injective maps `Fin Q.basisCount → Fin P.basisCount` and
`Fin P.basisCount → Fin Q.basisCount`.  Finite cardinal comparison turns
the forward injection into an equivalence `β : Fin Q.basisCount ≃
Fin P.basisCount`, carrying the matched bond-dimension equality,
gauge-phase equivalence, and non-decaying overlap for every sector of `Q`.

This is the Lean counterpart of the CPSV16 symmetry step "$g_A \geq g_B$
and $g_B \geq g_A$".  The proof invokes
`forall_k_exists_j_nondecaying_overlap_of_sameMPV` once with $(P,Q)$ and
once with $(Q,P)$, hence it consumes per-block unit-modulus witnesses on
both sides: `hUnitP : ∀ j, ∃ q, ‖μ_{j,q}^P‖ = 1` and `hUnitQ : ∀ k, ∃ q,
‖μ_{k,q}^Q‖ = 1`.  These are paper-implicit in CPSV16 §II.C line 1182's
projection argument and are taken as explicit theorem-level hypotheses
here (CPSV16 §II.C line 246 records only the global unit witness). -/
theorem bijective_match_of_sameMPVPos
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitP : ∀ j : Fin P.basisCount, ∃ q : Fin (P.copies j), ‖P.weight j q‖ = 1)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ β : Fin Q.basisCount ≃ Fin P.basisCount,
      ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis (β k)))
            (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis (β k)) (Q.basis k) N)
          atTop (𝓝 0) := by
  classical
  have hFwd :=
    forall_k_exists_j_nondecaying_overlap_of_sameMPVPos hP hQ hUnitQ hEqual
  have hEqual_symm : SameMPV₂Pos Q.toTensor P.toTensor := hEqual.symm
  have hBwd :=
    forall_k_exists_j_nondecaying_overlap_of_sameMPVPos hQ hP hUnitP hEqual_symm
  let φ₀ : Fin Q.basisCount → Fin P.basisCount := fun k => (hFwd k).choose
  have φ₀_spec : ∀ k : Fin Q.basisCount,
      ∃ h : P.basisDim (φ₀ k) = Q.basisDim k,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis (φ₀ k)))
            (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis (φ₀ k)) (Q.basis k) N)
          atTop (𝓝 0) := fun k => (hFwd k).choose_spec
  have rebase_centre_P :
      ∀ (j j' : Fin P.basisCount) (_hj : j = j')
        {kv : Fin Q.basisCount}
        (h_t : P.basisDim j' = Q.basisDim kv)
        (_GE : GaugePhaseEquiv
                  (cast (congr_arg (MPSTensor d) h_t) (P.basis j')) (Q.basis kv)),
        ∃ h_t' : P.basisDim j = Q.basisDim kv,
          GaugePhaseEquiv
              (cast (congr_arg (MPSTensor d) h_t') (P.basis j)) (Q.basis kv) := by
    rintro _ _ rfl _ h_t GE
    exact ⟨h_t, GE⟩
  have hφ₀_inj : Function.Injective φ₀ := by
    intro k₁ k₂ hjEq
    obtain ⟨h₁, GE₁, _⟩ := φ₀_spec k₁
    obtain ⟨h₂, GE₂, _⟩ := φ₀_spec k₂
    by_contra hne
    obtain ⟨h₂', GE₂'⟩ :=
      rebase_centre_P (φ₀ k₁) (φ₀ k₂) hjEq h₂ GE₂
    have hQdim : Q.basisDim k₁ = Q.basisDim k₂ := h₁.symm.trans h₂'
    have hQGE :
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) hQdim) (Q.basis k₁))
            (Q.basis k₂) :=
      gaugePhaseEquiv_cast_compose_via_centre (A := P.basis (φ₀ k₁))
        (B := Q.basis k₁) (C := Q.basis k₂) h₁ h₂' GE₁ GE₂'
    exact hQ.basis_distinct k₁ k₂ hne hQdim hQGE
  let ψ₀ : Fin P.basisCount → Fin Q.basisCount := fun j => (hBwd j).choose
  have ψ₀_spec : ∀ j : Fin P.basisCount,
      ∃ h : Q.basisDim (ψ₀ j) = P.basisDim j,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (Q.basis (ψ₀ j)))
            (P.basis j) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (Q.basis (ψ₀ j)) (P.basis j) N)
          atTop (𝓝 0) := fun j => (hBwd j).choose_spec
  have rebase_centre_Q :
      ∀ (k k' : Fin Q.basisCount) (_hk : k = k')
        {jv : Fin P.basisCount}
        (h_t : Q.basisDim k' = P.basisDim jv)
        (_GE : GaugePhaseEquiv
                  (cast (congr_arg (MPSTensor d) h_t) (Q.basis k')) (P.basis jv)),
        ∃ h_t' : Q.basisDim k = P.basisDim jv,
          GaugePhaseEquiv
              (cast (congr_arg (MPSTensor d) h_t') (Q.basis k)) (P.basis jv) := by
    rintro _ _ rfl _ h_t GE
    exact ⟨h_t, GE⟩
  have hψ₀_inj : Function.Injective ψ₀ := by
    intro j₁ j₂ hkEq
    obtain ⟨h₁, GE₁, _⟩ := ψ₀_spec j₁
    obtain ⟨h₂, GE₂, _⟩ := ψ₀_spec j₂
    by_contra hne
    obtain ⟨h₂', GE₂'⟩ :=
      rebase_centre_Q (ψ₀ j₁) (ψ₀ j₂) hkEq h₂ GE₂
    have hPdim : P.basisDim j₁ = P.basisDim j₂ := h₁.symm.trans h₂'
    have hPGE :
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) hPdim) (P.basis j₁))
            (P.basis j₂) :=
      gaugePhaseEquiv_cast_compose_via_centre (A := Q.basis (ψ₀ j₁))
        (B := P.basis j₁) (C := P.basis j₂) h₁ h₂' GE₁ GE₂'
    exact hP.basis_distinct j₁ j₂ hne hPdim hPGE
  have hCardQP : Fintype.card (Fin Q.basisCount) ≤ Fintype.card (Fin P.basisCount) :=
    Fintype.card_le_of_injective φ₀ hφ₀_inj
  have hCardPQ : Fintype.card (Fin P.basisCount) ≤ Fintype.card (Fin Q.basisCount) :=
    Fintype.card_le_of_injective ψ₀ hψ₀_inj
  have hCard : Fintype.card (Fin Q.basisCount) = Fintype.card (Fin P.basisCount) :=
    le_antisymm hCardQP hCardPQ
  have hφ₀_bij : Function.Bijective φ₀ :=
    (Fintype.bijective_iff_injective_and_card φ₀).2 ⟨hφ₀_inj, hCard⟩
  let β : Fin Q.basisCount ≃ Fin P.basisCount := Equiv.ofBijective φ₀ hφ₀_bij
  refine ⟨β, ?_⟩
  intro k
  simpa [β] using φ₀_spec k

/-- Reformulation for the all-length `SameMPV₂` form. -/
theorem bijective_match_of_sameMPV
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitP : ∀ j : Fin P.basisCount, ∃ q : Fin (P.copies j), ‖P.weight j q‖ = 1)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ β : Fin Q.basisCount ≃ Fin P.basisCount,
      ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis (β k)))
            (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis (β k)) (Q.basis k) N)
          atTop (𝓝 0) :=
  bijective_match_of_sameMPVPos
    (P := P) (Q := Q) hP hQ hUnitP hUnitQ hEqual.toSameMPV₂Pos


end MPSTensor
