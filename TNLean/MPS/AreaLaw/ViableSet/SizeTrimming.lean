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

Fix the Hamiltonian, the gap parameter and a finite left family. For every actual bond
dimension up to the uniform cut bound, take the chosen boundary net and minimize the left
energy at each feasible point. The union of the resulting left columns is the named
selection `sizeTrimmingSelection`, a function of the Hamiltonian, the gap parameter and
the input family alone. Whenever the input family is viable, one of these optimization
problems supplies a unit vector witnessing viability of the selection with error `1 / 12`.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, equation `eq:conv`,
lines 472–478, Lemmas `l:leading` and `l:within`, lines 493–515, and Claim `c:2`,
lines 520–527.

**Scope restriction (nontrivial chains and bond bound):** The result assumes `0 < L` and
`2 ≤ q`, as recorded in `docs/paper-gaps/lvv13_nontrivial_chain.tex`, and uses the library's
uniform cut bound rather than the sharper AKLV dependence; see
`docs/paper-gaps/lvv13_constant_bond.tex`. Taking the union over actual bond dimensions
avoids extending a bond isometry beyond the dimension of the right physical space.
The boundary nets use the corrected matrix-space exponent recorded in
https://sirui-lu.com/QICLean/paper-gaps/lvv13_trace_norm_net.pdf.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- **The size-trimming selection of a net and a solver.** For every bond dimension `m ≤ D`,
take the boundary set `net m` and at each of its feasible points the left columns of the
leading vector `sol m X`. The selection depends only on the Hamiltonian, the gap parameter,
the family `S`, the nets and the solver; no ground pair enters. LVV13, `algo53.tex`,
equation `eq:conv`, lines 472–478, and Claim `c:2`, lines 520–527. -/
noncomputable def ChainHamiltonian.sizeTrimmingSelectionWith {L q k : ℕ}
    (_h : ChainHamiltonian L q 1 1) (hq : 2 ≤ q) (Δ : ℝ) (S : Finset (LeftBlockVector L q k))
    (net : (m : ℕ) → Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ))
    (sol : (m : ℕ) → Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ →
      EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) :
    Finset (LeftBlockVector L q k) :=
  haveI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le two_pos hq)⟩
  let c : ℝ := (Δ / 169) ^ 2
  let D := constantCutBond q 1 1 Δ c
  open Classical in Finset.univ.biUnion fun m : Fin (D + 1) ↦
    boundaryFamily (S : Set (LeftBlockVector L q k)) m.val (c / (2 * L)) (net m.val) (sol m.val)

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
  h.sizeTrimmingSelectionWith hq Δ S
    (fun m ↦ rectangularTraceNormNet (CutSite L q k × Fin m) ((Δ / 169) ^ 2 / (2 * L)))
    (fun m ↦ boundaryLeadingVector (S : Set (LeftBlockVector L q k))
      (leftCutOperator k (h.cutLeftPart k)) m ((Δ / 169) ^ 2 / (2 * L)))

/-- The nets are admissible when each covers the boundary densities within `c / (2L)`
and has at most `K` points up to the uniform cut bound. -/
def ChainHamiltonian.IsAdmissibleNet {L q k : ℕ} (_h : ChainHamiltonian L q 1 1) (Δ : ℝ)
    (net : (m : ℕ) → Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)) :
    Prop :=
  let c : ℝ := (Δ / 169) ^ 2
  let D := constantCutBond q 1 1 Δ c
  ∀ m ≤ D, ∀ Y : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ,
    rectangularTraceNorm Y ≤ 1 → ∃ X ∈ net m, rectangularTraceNorm (Y - X) ≤ c / (2 * L)

/-- The solver is admissible when at every bond dimension it returns admissible leading
vectors for the left part of the Hamiltonian at tolerance `c / (2L)`. -/
def ChainHamiltonian.IsAdmissibleSolver {L q k : ℕ} (h : ChainHamiltonian L q 1 1) (hq : 2 ≤ q)
    (Δ : ℝ) (S : Finset (LeftBlockVector L q k))
    (sol : (m : ℕ) → Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ →
      EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) : Prop :=
  haveI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le two_pos hq)⟩
  ∀ m, IsAdmissibleLeadingVector (S : Set (LeftBlockVector L q k))
    (leftCutOperator k (h.cutLeftPart k)) m ((Δ / 169) ^ 2 / (2 * L)) (sol m)

/-- The selection of an admissible solver lies in the span of the input family.
LVV13, `algo53.tex`, Claim `c:2`, line 526. -/
theorem ChainHamiltonian.sizeTrimmingSelectionWith_subset_span {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hq : 2 ≤ q) (Δ : ℝ) (S : Finset (LeftBlockVector L q k))
    (net : (m : ℕ) → Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ))
    {sol : (m : ℕ) → Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ →
      EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)}
    (hsol : h.IsAdmissibleSolver hq Δ S sol) :
    (h.sizeTrimmingSelectionWith hq Δ S net sol : Set (LeftBlockVector L q k)) ⊆
      Submodule.span ℂ (S : Set (LeftBlockVector L q k)) := by
  classical
  intro v hv
  simp only [ChainHamiltonian.sizeTrimmingSelectionWith, Finset.mem_coe, Finset.mem_biUnion,
    Finset.mem_univ, true_and] at hv
  obtain ⟨m, hm⟩ := hv
  exact boundaryFamily_subset_span _ _ _ _ _ (hsol m.val) hm

/-- The selection lies in the span of the input family.
LVV13, `algo53.tex`, Claim `c:2`, line 526. -/
theorem ChainHamiltonian.sizeTrimmingSelection_subset_span {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hq : 2 ≤ q) (Δ : ℝ) (S : Finset (LeftBlockVector L q k)) :
    (h.sizeTrimmingSelection hq Δ S : Set (LeftBlockVector L q k)) ⊆
      Submodule.span ℂ (S : Set (LeftBlockVector L q k)) :=
  h.sizeTrimmingSelectionWith_subset_span hq Δ S _ fun m ↦
    isAdmissibleLeadingVector_boundaryLeadingVector _ _ m _

/-- The selection of nets with at most `K` points each has at most `(D + 1) D K` members.
LVV13, `algo53.tex`, Claim `c:2`, lines 520–527. -/
theorem ChainHamiltonian.card_sizeTrimmingSelectionWith_le {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hq : 2 ≤ q) (Δ : ℝ) (S : Finset (LeftBlockVector L q k))
    {net : (m : ℕ) → Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)}
    (sol : (m : ℕ) → Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ →
      EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) {K : ℕ}
    (hnet : ∀ m ≤ constantCutBond q 1 1 Δ ((Δ / 169) ^ 2), (net m).card ≤ K) :
    (h.sizeTrimmingSelectionWith hq Δ S net sol).card ≤
      (constantCutBond q 1 1 Δ ((Δ / 169) ^ 2) + 1) * constantCutBond q 1 1 Δ ((Δ / 169) ^ 2) *
        K := by
  classical
  set D := constantCutBond q 1 1 Δ ((Δ / 169) ^ 2) with hD
  have hm (m : Fin (D + 1)) : (boundaryFamily (S : Set (LeftBlockVector L q k)) m.val
      ((Δ / 169) ^ 2 / (2 * L)) (net m.val) (sol m.val)).card ≤ D * K :=
    (card_boundaryFamily_le _ _ _ _ _).trans
      (Nat.mul_le_mul (Nat.le_of_lt_succ m.isLt) (hnet m.val (Nat.le_of_lt_succ m.isLt)))
  simpa only [ChainHamiltonian.sizeTrimmingSelectionWith, Finset.card_univ, Fintype.card_fin,
    Nat.mul_assoc] using Finset.card_biUnion_le_card_mul Finset.univ _ (D * K) fun m _ ↦ hm m

/-- The selection has at most `(D + 1) * D * K` members, with `K` the net bound.
LVV13, `algo53.tex`, Claim `c:2`, lines 520–527. -/
theorem ChainHamiltonian.card_sizeTrimmingSelection_le {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q k)) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let K : ℕ := (2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ + 1) ^
      (2 * (q * D) ^ 2)
    (h.sizeTrimmingSelection hq Δ S).card ≤ (D + 1) * D * K := by
  intro c D K
  let : NeZero q := ⟨by omega⟩
  have hc : 0 < c := sq_pos_of_pos (div_pos hΔ (by norm_num))
  have hη : 0 < c / (2 * L) :=
    div_pos hc (mul_pos (by norm_num) (by exact_mod_cast hL))
  exact h.card_sizeTrimmingSelectionWith_le hq Δ S _ fun m hm ↦
    card_boundary_rectangularTraceNormNet_le (by omega) hη hm

/-- The selection of nets with the standard point bound has explicit polynomial cardinality
in the chain length, with coefficient and degree independent of that length. LVV13,
`algo53.tex`, Claim `c:2`, lines 520–527. -/
theorem ChainHamiltonian.card_sizeTrimmingSelectionWith_le_polynomial {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q k))
    {net : (m : ℕ) → Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)}
    (sol : (m : ℕ) → Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ →
      EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))
    (hnet : ∀ m ≤ constantCutBond q 1 1 Δ ((Δ / 169) ^ 2), (net m).card ≤
      (2 * ⌈((q * constantCutBond q 1 1 Δ ((Δ / 169) ^ 2) : ℕ) : ℝ) ^ 2 /
        ((Δ / 169) ^ 2 / (2 * L))⌉₊ + 1) ^
        (2 * (q * constantCutBond q 1 1 Δ ((Δ / 169) ^ 2)) ^ 2)) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let p := 2 * (q * D) ^ 2
    let A := ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊
    let C := (D + 1) * D * (2 * A + 1) ^ p
    (h.sizeTrimmingSelectionWith hq Δ S net sol).card ≤ C * L ^ p := by
  intro c D p A C
  have hnet' := boundaryNet_card_bound_le_polynomial (q := q) (D := D) (c := c)
    (by omega : 1 ≤ L) (sq_pos_of_pos (div_pos hΔ (by norm_num)))
  simpa only [C, Nat.mul_assoc] using
    (h.card_sizeTrimmingSelectionWith_le hq Δ S sol hnet).trans
      (Nat.mul_le_mul_left ((D + 1) * D) hnet')

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
  let : NeZero q := ⟨by omega⟩
  have hc : 0 < c := sq_pos_of_pos (div_pos hΔ (by norm_num))
  have hη : 0 < c / (2 * L) :=
    div_pos hc (mul_pos (by norm_num) (by exact_mod_cast hL))
  exact h.card_sizeTrimmingSelectionWith_le_polynomial hL hq hΔ S _ fun m hm ↦
    card_boundary_rectangularTraceNormNet_le (by omega) hη hm

/-- **Size trimming with any admissible nets and solver is chosen before the ground state.**
Whenever the input family is `c / L`-viable for a ground pair with gap at least `Δ`, the
selection is `1 / 12`-viable for it, with a witness given by an isometry `W` on a bond of
dimension `m ≤ D` and a unit vector `u` all of whose columns belong to the selection.
Library-bond version of LVV13, `algo53.tex`, Claim `c:2`, lines 520–527, for every solver
of the convex program returning optimal solutions. -/
theorem ChainHamiltonian.isViable_sizeTrimmingSelectionWith {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q k))
    {net : (m : ℕ) → Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)}
    (hnet : h.IsAdmissibleNet Δ net)
    {sol : (m : ℕ) → Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ →
      EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)}
    (hsol : h.IsAdmissibleSolver hq Δ S sol)
    (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q))
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ)
    (hviable : IsViable Γ ((Δ / 169) ^ 2 / L) (S : Set (LeftBlockVector L q k))) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    IsViable Γ (1 / 12) (h.sizeTrimmingSelectionWith hq Δ S net sol : Set (LeftBlockVector L q k)) ∧
      ∃ (m : ℕ) (W : Matrix (CutRight L q k) (Fin m) ℂ)
        (u : EuclideanSpace ℂ
          (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)),
        Wᴴ * W = 1 ∧ m ≤ D ∧ ‖u‖ = 1 ∧
        (∀ a, WithLp.toLp 2 (fun x ↦ u (x, a)) ∈ h.sizeTrimmingSelectionWith hq Δ S net sol) ∧
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
  let N := net
  let T := fun m : ℕ ↦ boundaryFamily (S : Set (LeftBlockVector L q k)) m (c / (2 * L)) (N m)
    (sol m)
  have hTtotal : h.sizeTrimmingSelectionWith hq Δ S net sol =
      Finset.univ.biUnion fun m : Fin (D + 1) ↦
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
  obtain ⟨X, hXN, hX⟩ := hnet m hmD (partialTraceFirst ρx) hYnorm.le
  have hXfeasible : (feasibleBoundaryDensities (S : Set (LeftBlockVector L q k)) m
      (c / (2 * L)) X).Nonempty := ⟨ρx, hρxp, hρxt, hρxP, hX⟩
  have hXmem : X ∈ feasibleBoundaryPoints (S : Set (LeftBlockVector L q k)) m (c / (2 * L))
      (N m) := mem_feasibleBoundaryPoints.mpr ⟨hXN, hXfeasible⟩
  obtain ⟨σ, μ, hσ, htr, hσP, hσX, hmin, hu, -, heig, -, hmax⟩ := hsol m X hXfeasible
  set u := sol m X with hu_def
  obtain ⟨_, _, hvnorm, _, _, hvΓ⟩ := huniform X hX σ hσ htr hσP hσX hmin u μ hu heig hmax
  have hsubset : (T m : Set (LeftBlockVector L q k)) ⊆
      (h.sizeTrimmingSelectionWith hq Δ S net sol : Set (LeftBlockVector L q k)) := by
    rw [hTtotal]
    exact fun z hz ↦ Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hz⟩
  have hviable' : IsViable Γ (1 / 12)
      (h.sizeTrimmingSelectionWith hq Δ S net sol : Set (LeftBlockVector L q k)) := by
    refine ⟨_, hvnorm, ?_, ?_⟩
    · rw [norm_inner_symm]
      exact hvΓ
    · rw [gluingLeftCoordinates_rightApply W u]
      have hvT := rightApply_mem_leftSupportSubmodule_leftColumns
        (feasibleBoundaryPoints (S : Set (LeftBlockVector L q k)) m (c / (2 * L)) (N m))
        (fun z ↦ gluingLeftCoordinates L q k m (sol m z))
        hXmem W
      exact mem_leftSupportSubmodule.mpr fun β ↦
        Submodule.span_mono hsubset ((mem_leftSupportSubmodule.mp hvT) β)
  refine ⟨hviable', m, W, gluingLeftCoordinates L q k m u, hW, hmD, ?_, ?_, ?_⟩
  · rw [(gluingLeftCoordinates L q k m).norm_map]
    exact hu
  · intro a
    apply hsubset
    unfold T boundaryFamily leftColumns
    exact Finset.mem_image.mpr ⟨(X, a), Finset.mem_product.mpr
      ⟨hXmem, Finset.mem_univ a⟩, rfl⟩
  · rw [← gluingLeftCoordinates_rightApply W u]
    exact hvΓ

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
  let : NeZero q := ⟨by omega⟩
  have hc : 0 < (Δ / 169) ^ 2 := sq_pos_of_pos (div_pos hΔ (by norm_num))
  have hη : 0 < (Δ / 169) ^ 2 / (2 * L) :=
    div_pos hc (mul_pos (by norm_num) (by exact_mod_cast hL))
  exact h.isViable_sizeTrimmingSelectionWith hpos hL hq hΔ S
    (fun _ _ Y hY ↦ exists_mem_rectangularTraceNormNet hη Y hY)
    (fun m ↦ isAdmissibleLeadingVector_boundaryLeadingVector _ _ m _) E₀ Γ hgs hviable

end TNLean.MPS.AreaLaw
