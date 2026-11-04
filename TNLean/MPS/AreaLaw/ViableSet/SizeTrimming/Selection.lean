/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundaryNet
import TNLean.MPS.AreaLaw.ViableSet.BoundaryNetPolynomial
import TNLean.MPS.AreaLaw.ViableSet.FiniteBoundarySelection
import TNLean.MPS.AreaLaw.ViableSet.Span
import TNLean.MPS.AreaLaw.ViableSet.ViableLeadingBounds

/-!
# The size-trimming selection, chosen before the ground state

For each actual bond dimension, minimize the left energy over the chosen boundary net.
The union of the resulting columns has polynomial cardinality and is viable whenever
the original family is viable, with the choice fixed before the ground state.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, equation `eq:conv`,
lines 472–478, Lemmas `l:leading` and `l:within`, lines 493–515, and Claim `c:2`,
lines 520–527.

**Scope restriction (physical viability applications):** The size-trimming viability
conclusions for physical chains assume `0 < L` and `2 ≤ q`, as recorded in
`docs/paper-gaps/lvv13_nontrivial_chain.tex`, and use the library's
uniform cut bound rather than the sharper AKLV dependence; see
`docs/paper-gaps/lvv13_constant_bond.tex`. Taking the union over actual bond dimensions
avoids extending a bond isometry beyond the dimension of the right physical space.
The boundary nets use the corrected matrix-space exponent recorded in
https://sirui-lu.com/QICLean/paper-gaps/lvv13_trace_norm_net.pdf.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- **The size-trimming selection.** For every bond dimension `m ≤ D`, take the chosen
trace-norm net of radius `c / (2L)` on the boundary space of the bond, and at each of its
feasible points the left columns of the leading vector of a chosen density of least left
energy supported on `span S`. The selection depends only on the Hamiltonian, the gap
parameter and the family `S`; no ground pair enters. LVV13, `algo53.tex`, equation
`eq:conv`, lines 472–478, and Claim `c:2`, lines 520–527, using all actual bond dimensions
up to the uniform cut bound. -/
noncomputable def ChainHamiltonian.sizeTrimmingSelection {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hq : 2 ≤ q) (Δ : ℝ) (S : Finset (LeftBlockVector L q k)) :
    Finset (LeftBlockVector L q k) :=
  haveI : NeZero q := ⟨by omega⟩
  let c : ℝ := (Δ / 169) ^ 2
  let D := constantCutBond q 1 1 Δ c
  open Classical in Finset.univ.biUnion fun m : Fin (D + 1) ↦
    boundaryMinimizerFamily (S : Set (LeftBlockVector L q k)) (leftCutOperator k (h.cutLeftPart k))
      m.val (c / (2 * L)) (rectangularTraceNormNet (CutSite L q k × Fin m.val) (c / (2 * L)))

/-- The selection lies in the span of the input family.
LVV13, `algo53.tex`, Claim `c:2`, line 526. -/
theorem ChainHamiltonian.sizeTrimmingSelection_subset_span {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hq : 2 ≤ q) (Δ : ℝ) (S : Finset (LeftBlockVector L q k)) :
    (h.sizeTrimmingSelection hq Δ S : Set (LeftBlockVector L q k)) ⊆
      Submodule.span ℂ (S : Set (LeftBlockVector L q k)) := by
  classical
  intro v hv
  simp only [ChainHamiltonian.sizeTrimmingSelection, Finset.mem_coe, Finset.mem_biUnion,
    Finset.mem_univ, true_and] at hv
  obtain ⟨m, hm⟩ := hv
  exact boundaryMinimizerFamily_subset_span _ _ _ _ _ hm

/-- Every retained column has norm at most one, since it is a column of a unit leading
vector. This bound depends on no ground pair or viability assumption.
LVV13, `algo53.tex`, column extraction, lines 477–478. -/
theorem ChainHamiltonian.norm_le_one_of_mem_sizeTrimmingSelection {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hq : 2 ≤ q) (Δ : ℝ)
    (S : Finset (LeftBlockVector L q k)) {v : LeftBlockVector L q k}
    (hv : v ∈ h.sizeTrimmingSelection hq Δ S) : ‖v‖ ≤ 1 := by
  classical
  let : NeZero q := ⟨by omega⟩
  simp only [ChainHamiltonian.sizeTrimmingSelection, Finset.mem_biUnion,
    Finset.mem_univ, true_and] at hv
  obtain ⟨m, hm⟩ := hv
  exact norm_le_one_of_mem_boundaryMinimizerFamily
    (S : Set (LeftBlockVector L q k)) (leftCutOperator k (h.cutLeftPart k)) _ _ _ hm

/-- The selection has at most `(D + 1) D K` members, with `K` the net bound.
LVV13, `algo53.tex`, Claim `c:2`, lines 520–527. -/
theorem ChainHamiltonian.card_sizeTrimmingSelection_le {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q k)) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let K : ℕ := (2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ + 1) ^
      (2 * (q * D) ^ 2)
    (h.sizeTrimmingSelection hq Δ S).card ≤ (D + 1) * D * K := by
  classical
  intro c D K
  let : NeZero q := ⟨by omega⟩
  have hc : 0 < c := sq_pos_of_pos (div_pos hΔ (by norm_num))
  have hη : 0 < c / (2 * L) :=
    div_pos hc (mul_pos (by norm_num) (by exact_mod_cast hL))
  have hm (m : Fin (D + 1)) : (boundaryMinimizerFamily (S : Set (LeftBlockVector L q k))
      (leftCutOperator k (h.cutLeftPart k)) m.val (c / (2 * L))
      (rectangularTraceNormNet (CutSite L q k × Fin m.val) (c / (2 * L)))).card ≤ D * K :=
    (card_boundaryMinimizerFamily_le _ _ _ _ _).trans
      (Nat.mul_le_mul (Nat.le_of_lt_succ m.isLt)
        (card_boundary_rectangularTraceNormNet_le (by omega) hη (Nat.le_of_lt_succ m.isLt)))
  simpa only [ChainHamiltonian.sizeTrimmingSelection, Finset.card_univ, Fintype.card_fin,
    Nat.mul_assoc] using Finset.card_biUnion_le_card_mul Finset.univ _ (D * K) fun m _ ↦ hm m

/-- The selection has explicit polynomial cardinality in the chain length, with coefficient
and degree independent of that length. LVV13, `algo53.tex`, Claim `c:2`, lines 520–527. -/
theorem ChainHamiltonian.card_sizeTrimmingSelection_le_polynomial {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q k)) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let p := 2 * (q * D) ^ 2
    let A := ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊
    let C := (D + 1) * D * (2 * A + 1) ^ p
    (h.sizeTrimmingSelection hq Δ S).card ≤ C * L ^ p := by
  intro c D p A C
  have hnet := boundaryNet_card_bound_le_polynomial (q := q) (D := D) (c := c)
    (by omega : 1 ≤ L) (sq_pos_of_pos (div_pos hΔ (by norm_num)))
  simpa only [C, Nat.mul_assoc] using
    (h.card_sizeTrimmingSelection_le hL hq hΔ S).trans (Nat.mul_le_mul_left ((D + 1) * D) hnet)

/-- **Size trimming is chosen before the ground state.** Whenever the input family is
`c / L`-viable for a ground pair with gap at least `Δ`, the selection is `1 / 12`-viable
for it, with a witness given by an isometry `W` on a bond of dimension `m ≤ D` and a unit
vector `u` all of whose columns belong to the selection. Library-bond version of LVV13,
`algo53.tex`, Claim `c:2`, lines 520–527. -/
theorem ChainHamiltonian.isViable_sizeTrimmingSelection {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q k)) (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q))
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ)
    (hviable : IsViable Γ ((Δ / 169) ^ 2 / L) (S : Set (LeftBlockVector L q k))) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    IsViable Γ (1 / 12) (h.sizeTrimmingSelection hq Δ S : Set (LeftBlockVector L q k)) ∧
      ∃ (m : ℕ) (W : Matrix (CutRight L q k) (Fin m) ℂ)
        (u : EuclideanSpace ℂ
          (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)),
        Wᴴ * W = 1 ∧ m ≤ D ∧ ‖u‖ = 1 ∧
        (∀ a, WithLp.toLp 2 (fun x ↦ u (x, a)) ∈ h.sizeTrimmingSelection hq Δ S) ∧
        1 - 1 / 12 ≤ ‖⟪Γ, WithLp.toLp 2 (fun z ↦ rightApply W u
          (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k) z))⟫_ℂ‖ := by
  classical
  intro c D
  let : NeZero q := ⟨by omega⟩
  let P := reindex
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (spanProjection (S : Set (LeftBlockVector L q k)))
  have hc : 0 < c := sq_pos_of_pos (div_pos hΔ (by norm_num))
  have hη : 0 < c / (2 * L) :=
    div_pos hc (mul_pos (by norm_num) (by exact_mod_cast hL))
  let HL := leftCutOperator k (h.cutLeftPart k)
  let N := fun m : ℕ ↦ rectangularTraceNormNet (CutSite L q k × Fin m) (c / (2 * L))
  let T := fun m : ℕ ↦ boundaryMinimizerFamily (S : Set (LeftBlockVector L q k)) HL m
    (c / (2 * L)) (N m)
  have hTtotal : h.sizeTrimmingSelection hq Δ S = Finset.univ.biUnion fun m : Fin (D + 1) ↦
      T m.val := rfl
  obtain ⟨_, m, W, x, -, -, -, -, hW, hmD, -, hxnorm, hxP, huniform⟩ :=
    h.exists_uniform_leading_bounds_of_isViable hpos hL hq hΔ
      (h.cutLeftPart k) (h.cutBoundaryPart k) (h.cutLeftPart_add_cutBoundaryPart k)
      (h.cutLeftPart_isSupportedOn k) (h.cutBoundaryPart_isSupportedOn k)
      (h.norm_cutBoundaryPart_le k) hgs hviable
  let ρx := vecMulVec x (star x)
  have hρxp : ρx.PosSemidef := posSemidef_vecMulVec_self_star x
  have hρxt : ρx.trace = 1 := by
    change (vecMulVec (WithLp.ofLp (WithLp.toLp 2 x))
      (star (WithLp.ofLp (WithLp.toLp 2 x)))).trace = 1
    rw [trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hxnorm]
    norm_num
  have hρxP : (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρx = ρx := by
    dsimp only [ρx]
    rw [mul_vecMulVec, hxP]
  let e := Equiv.prodAssoc (CutLeft L q k) (CutSite L q k) (Fin m)
  have hYp : (partialTraceFirst ρx).PosSemidef :=
    (hρxp.submatrix e.symm).partialTraceLeft
  have hYt : (partialTraceFirst ρx).trace = 1 := by
    rw [partialTraceFirst, trace_partialTraceLeft]
    exact (e.symm.sum_comp (fun i ↦ ρx i i)).trans hρxt
  have hYnorm : rectangularTraceNorm (partialTraceFirst ρx) = 1 := by
    rw [rectangularTraceNorm_eq_re_trace_abs, CFC.abs_of_nonneg _ hYp.nonneg, hYt]
    norm_num
  let i : Fin (D + 1) := ⟨m, Nat.lt_succ_of_le hmD⟩
  obtain ⟨X, hXN, hX⟩ := exists_mem_rectangularTraceNormNet hη (partialTraceFirst ρx) hYnorm.le
  have hXfeasible : (feasibleBoundaryDensities (S : Set (LeftBlockVector L q k)) m
      (c / (2 * L)) X).Nonempty := ⟨ρx, hρxp, hρxt, hρxP, hX⟩
  have hXmem : X ∈ feasibleBoundaryPoints (S : Set (LeftBlockVector L q k)) m (c / (2 * L))
      (N m) := mem_feasibleBoundaryPoints.mpr ⟨hXN, hXfeasible⟩
  obtain ⟨hσ, htr, hσP, hσX, hmin, hu, -, heig, -, hmax⟩ :=
    boundaryMinimizer_spec (S : Set (LeftBlockVector L q k)) HL m (c / (2 * L)) hXfeasible
  set σ := boundaryMinimizer (S : Set (LeftBlockVector L q k)) HL m (c / (2 * L)) X
  set u := boundaryLeadingVector (S : Set (LeftBlockVector L q k)) HL m (c / (2 * L)) X
  set μ := boundaryLeadingValue (S : Set (LeftBlockVector L q k)) HL m (c / (2 * L)) X
  obtain ⟨_, _, hvnorm, _, _, hvΓ⟩ := huniform X hX σ hσ htr hσP hσX hmin u μ hu heig hmax
  have hsubset : (T m : Set (LeftBlockVector L q k)) ⊆
      (h.sizeTrimmingSelection hq Δ S : Set (LeftBlockVector L q k)) := by
    rw [hTtotal]
    exact fun z hz ↦ Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hz⟩
  have hviable' : IsViable Γ (1 / 12)
      (h.sizeTrimmingSelection hq Δ S : Set (LeftBlockVector L q k)) := by
    refine ⟨_, hvnorm, ?_, ?_⟩
    · rw [norm_inner_symm]
      exact hvΓ
    · rw [gluingLeftCoordinates_rightApply W u]
      have hvT := rightApply_mem_leftSupportSubmodule_leftColumns
        (feasibleBoundaryPoints (S : Set (LeftBlockVector L q k)) m (c / (2 * L)) (N m))
        (fun z ↦ gluingLeftCoordinates L q k m
          (boundaryLeadingVector (S : Set (LeftBlockVector L q k)) HL m (c / (2 * L)) z))
        hXmem W
      exact mem_leftSupportSubmodule.mpr fun β ↦
        Submodule.span_mono hsubset ((mem_leftSupportSubmodule.mp hvT) β)
  refine ⟨hviable', m, W, gluingLeftCoordinates L q k m u, hW, hmD, ?_, ?_, ?_⟩
  · rw [(gluingLeftCoordinates L q k m).norm_map]
    exact hu
  · intro a
    apply hsubset
    unfold T boundaryMinimizerFamily leftColumns
    exact Finset.mem_image.mpr ⟨(X, a), Finset.mem_product.mpr
      ⟨hXmem, Finset.mem_univ a⟩, rfl⟩
  · rw [← gluingLeftCoordinates_rightApply W u]
    exact hvΓ

end TNLean.MPS.AreaLaw
