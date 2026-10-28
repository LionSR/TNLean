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
# A finite size-trimming family chosen before the ground state

Fix the Hamiltonian, the gap parameter and a finite left family. For every actual bond
dimension up to the uniform cut bound, choose a boundary net and minimize the left energy
at each feasible point. The union of the resulting left columns is chosen before the
ground vector. Whenever the input family is viable, one of these optimization problems
supplies a unit vector witnessing viability of the output family with error `1 / 12`.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, equation `eq:conv`,
lines 472–478, Lemmas `l:leading` and `l:within`, lines 493–515, and Claim `c:2`,
lines 520–527.

**Scope restriction (nontrivial chains and bond bound):** The result assumes `0 < L` and
`2 ≤ q`, as recorded in `docs/paper-gaps/lvv13_nontrivial_chain.tex`, and uses the library's
uniform cut bound rather than the sharper AKLV dependence; see
`docs/paper-gaps/lvv13_constant_bond.tex`. Taking the union over actual bond dimensions
avoids extending a bond isometry beyond the dimension of the right physical space.
The finite-span estimate uses the effective input budget `max 1 b` of `IsLeftOpenMPS`.
The boundary nets use the corrected matrix-space exponent recorded in
https://sirui-lu.com/QICLean/paper-gaps/lvv13_trace_norm_net.pdf.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A finite family chosen independently of the ground vector performs size trimming with
error `1 / 12`. Auxiliary library-bond version of LVV13, `algo53.tex`, Claim `c:2`,
lines 520–527, using all actual bond dimensions up to the uniform cut bound. -/
theorem ChainHamiltonian.exists_size_trimmed_column_family {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q k)) (b : ℕ)
    (hS : ∀ v ∈ S, IsLeftOpenMPS b v) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let K : ℕ := (2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ + 1) ^
      (2 * (q * D) ^ 2)
    ∃ T : Finset (LeftBlockVector L q k),
      T.card ≤ (D + 1) * D * K ∧
      (T : Set (LeftBlockVector L q k)) ⊆ Submodule.span ℂ (S : Set (LeftBlockVector L q k)) ∧
      (∀ v ∈ T, IsLeftOpenMPS (S.card * max 1 b) v) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        IsGappedGroundState h.operator E₀ Γ Δ →
        IsViable Γ (c / L) (S : Set (LeftBlockVector L q k)) →
        IsViable Γ (1 / 12) (T : Set (LeftBlockVector L q k)) ∧
        ∃ (m : ℕ) (W : Matrix (CutRight L q k) (Fin m) ℂ)
          (u : EuclideanSpace ℂ
            (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)),
          Wᴴ * W = 1 ∧ m ≤ D ∧ ‖u‖ = 1 ∧
          (∀ a, WithLp.toLp 2 (fun x ↦ u (x, a)) ∈ T) ∧
          1 - 1 / 12 ≤ ‖⟪Γ, WithLp.toLp 2 (fun z ↦ rightApply W u
            (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k) z))⟫_ℂ‖ := by
  classical
  intro c D K
  let : NeZero q := ⟨by omega⟩
  let P := reindex
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (spanProjection (S : Set (LeftBlockVector L q k)))
  have hc : 0 < c := sq_pos_of_pos (div_pos hΔ (by norm_num))
  have hη : 0 < c / (2 * L) :=
    div_pos hc (mul_pos (by norm_num) (by exact_mod_cast hL))
  obtain ⟨HL, B, hsplit, hHL, hBS, hBn⟩ := h.exists_gluing_decomposition_of_range_one k
  choose N hNcard hcover using fun m : Fin (D + 1) ↦
    exists_finset_boundary_rectangularTraceNorm_net (L := L) (k := k) (m := m.val)
      (D := D) (by omega : 1 ≤ q) hη (Nat.le_of_lt_succ m.isLt)
  choose F σ u μ T hF hTeq hTcard hTspan hspec using fun m : Fin (D + 1) ↦
    exists_finite_boundary_minimizer_family (L := L) (q := q) (k := k)
      (S : Set (LeftBlockVector L q k)) (leftCutOperator k HL) m.val (c / (2 * L)) (N m)
  let Ttotal := Finset.univ.biUnion T
  have hgood : ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState h.operator E₀ Γ Δ →
      IsViable Γ (c / L) (S : Set (LeftBlockVector L q k)) →
      IsViable Γ (1 / 12) (Ttotal : Set (LeftBlockVector L q k)) ∧
      ∃ (m : ℕ) (W : Matrix (CutRight L q k) (Fin m) ℂ)
        (u : EuclideanSpace ℂ
          (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)),
        Wᴴ * W = 1 ∧ m ≤ D ∧ ‖u‖ = 1 ∧
        (∀ a, WithLp.toLp 2 (fun x ↦ u (x, a)) ∈ Ttotal) ∧
        1 - 1 / 12 ≤ ‖⟪Γ, WithLp.toLp 2 (fun z ↦ rightApply W u
          (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k) z))⟫_ℂ‖ := by
    intro E₀ Γ hgs hviable
    obtain ⟨_, m, W, x, -, -, -, -, hW, hmD, -, hxnorm, hxP, huniform⟩ :=
      h.exists_uniform_leading_bounds_of_isViable hpos hL hq hΔ
        HL B hsplit hHL hBS hBn hgs hviable
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
    obtain ⟨X, hXN, hX⟩ := hcover i (partialTraceFirst ρx) hYnorm.le
    let j : F i := ⟨X, (hF i X).mpr ⟨hXN, ⟨ρx, hρxp, hρxt, hρxP, hX⟩⟩⟩
    obtain ⟨⟨hσ, htr, hσP, hσX⟩, hmin, hu, -, heig, -, hmax⟩ := hspec i j
    obtain ⟨_, _, hvnorm, _, _, hvΓ⟩ := huniform X hX (σ i j) hσ htr hσP hσX
      (fun ρ hρ htρ hρP hρX ↦ hmin ρ ⟨hρ, htρ, hρP, hρX⟩)
      (u i j) (μ i j) hu heig hmax
    have hviable : IsViable Γ (1 / 12) (Ttotal : Set (LeftBlockVector L q k)) := by
      refine ⟨_, hvnorm, ?_, ?_⟩
      · rw [norm_inner_symm]
        exact hvΓ
      · rw [gluingLeftCoordinates_rightApply W (u i j)]
        have hvT := rightApply_mem_leftSupportSubmodule_leftColumns
          (Finset.univ : Finset (F i))
          (fun z ↦ gluingLeftCoordinates L q k i.val (u i z))
          (i := j) (Finset.mem_univ j) W
        rw [← hTeq i] at hvT
        have hsubset : (T i : Set (LeftBlockVector L q k)) ⊆
            (Ttotal : Set (LeftBlockVector L q k)) :=
          fun z hz ↦ Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hz⟩
        exact mem_leftSupportSubmodule.mpr fun β ↦
          Submodule.span_mono hsubset ((mem_leftSupportSubmodule.mp hvT) β)
    refine ⟨hviable, m, W, gluingLeftCoordinates L q k m (u i j), hW, hmD, ?_, ?_, ?_⟩
    · rw [(gluingLeftCoordinates L q k m).norm_map]
      exact hu
    · intro a
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [hTeq i]
      unfold leftColumns
      exact Finset.mem_image.mpr ⟨(j, a), Finset.mem_product.mpr
        ⟨Finset.mem_univ j, Finset.mem_univ a⟩, rfl⟩
    · rw [← gluingLeftCoordinates_rightApply W (u i j)]
      exact hvΓ
  have hTsub : (Ttotal : Set (LeftBlockVector L q k)) ⊆
      Submodule.span ℂ (S : Set (LeftBlockVector L q k)) := by
    intro v hv
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
    exact hTspan i hi
  have hcard : Ttotal.card ≤ (D + 1) * D * K := by
    simpa only [Ttotal, Finset.card_univ, Fintype.card_fin, Nat.mul_assoc] using
      Finset.card_biUnion_le_card_mul Finset.univ T (D * K)
        (fun i _ ↦ (hTcard i).trans
          (Nat.mul_le_mul (Nat.le_of_lt_succ i.isLt) (hNcard i)))
  exact ⟨Ttotal, hcard, hTsub,
    fun v hv ↦ isLeftOpenMPS_of_mem_span S hS (hTsub hv), hgood⟩

/-- A finite family chosen independently of the ground vector performs size trimming with
error `1 / 12`. Auxiliary library-bond version of LVV13, `algo53.tex`, Claim `c:2`,
lines 520–527, using all actual bond dimensions up to the uniform cut bound. -/
theorem ChainHamiltonian.exists_size_trimmed_family {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q k)) (b : ℕ)
    (hS : ∀ v ∈ S, IsLeftOpenMPS b v) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let K : ℕ := (2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ + 1) ^
      (2 * (q * D) ^ 2)
    ∃ T : Finset (LeftBlockVector L q k),
      T.card ≤ (D + 1) * D * K ∧
      (T : Set (LeftBlockVector L q k)) ⊆ Submodule.span ℂ (S : Set (LeftBlockVector L q k)) ∧
      (∀ v ∈ T, IsLeftOpenMPS (S.card * max 1 b) v) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        IsGappedGroundState h.operator E₀ Γ Δ →
        IsViable Γ (c / L) (S : Set (LeftBlockVector L q k)) →
        IsViable Γ (1 / 12) (T : Set (LeftBlockVector L q k)) := by
  obtain ⟨T, hcard, hspan, hbond, hgood⟩ :=
    h.exists_size_trimmed_column_family hpos hL hq hΔ S b hS
  exact ⟨T, hcard, hspan, hbond, fun E₀ Γ hgs hv ↦ (hgood E₀ Γ hgs hv).1⟩

/-- The finite size-trimming family has an explicit polynomial cardinality in the chain
length, with coefficient and degree independent of that length. Auxiliary library-bond
version of LVV13, `algo53.tex`, Claim `c:2`, lines 520–527. -/
theorem ChainHamiltonian.exists_size_trimmed_column_family_polynomial {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q k)) (b : ℕ)
    (hS : ∀ v ∈ S, IsLeftOpenMPS b v) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let p := 2 * (q * D) ^ 2
    let A := ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊
    let C := (D + 1) * D * (2 * A + 1) ^ p
    ∃ T : Finset (LeftBlockVector L q k),
      T.card ≤ C * L ^ p ∧
      (T : Set (LeftBlockVector L q k)) ⊆ Submodule.span ℂ (S : Set (LeftBlockVector L q k)) ∧
      (∀ v ∈ T, IsLeftOpenMPS (S.card * max 1 b) v) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        IsGappedGroundState h.operator E₀ Γ Δ →
        IsViable Γ (c / L) (S : Set (LeftBlockVector L q k)) →
        IsViable Γ (1 / 12) (T : Set (LeftBlockVector L q k)) ∧
        ∃ (m : ℕ) (W : Matrix (CutRight L q k) (Fin m) ℂ)
          (u : EuclideanSpace ℂ
            (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)),
          Wᴴ * W = 1 ∧ m ≤ D ∧ ‖u‖ = 1 ∧
          (∀ a, WithLp.toLp 2 (fun x ↦ u (x, a)) ∈ T) ∧
          1 - 1 / 12 ≤ ‖⟪Γ, WithLp.toLp 2 (fun z ↦ rightApply W u
            (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k) z))⟫_ℂ‖ := by
  classical
  intro c D p A C
  obtain ⟨T, hcard, hspan, hbond, hgood⟩ :=
    h.exists_size_trimmed_column_family hpos hL hq hΔ S b hS
  have hnet := boundaryNet_card_bound_le_polynomial (q := q) (D := D) (c := c)
    (by omega : 1 ≤ L) (sq_pos_of_pos (div_pos hΔ (by norm_num)))
  refine ⟨T, ?_, hspan, hbond, hgood⟩
  simpa only [C, Nat.mul_assoc] using
    hcard.trans (Nat.mul_le_mul_left ((D + 1) * D) hnet)

/-- The finite size-trimming family has polynomial cardinality. This is the library-bond
version of LVV13, `algo53.tex`, Claim `c:2`, lines 520–527. -/
theorem ChainHamiltonian.exists_size_trimmed_family_polynomial {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q k)) (b : ℕ)
    (hS : ∀ v ∈ S, IsLeftOpenMPS b v) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let p := 2 * (q * D) ^ 2
    let A := ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊
    let C := (D + 1) * D * (2 * A + 1) ^ p
    ∃ T : Finset (LeftBlockVector L q k),
      T.card ≤ C * L ^ p ∧
      (T : Set (LeftBlockVector L q k)) ⊆ Submodule.span ℂ (S : Set (LeftBlockVector L q k)) ∧
      (∀ v ∈ T, IsLeftOpenMPS (S.card * max 1 b) v) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        IsGappedGroundState h.operator E₀ Γ Δ →
        IsViable Γ (c / L) (S : Set (LeftBlockVector L q k)) →
        IsViable Γ (1 / 12) (T : Set (LeftBlockVector L q k)) := by
  obtain ⟨T, hcard, hspan, hbond, hgood⟩ :=
    h.exists_size_trimmed_column_family_polynomial hpos hL hq hΔ S b hS
  exact ⟨T, hcard, hspan, hbond, fun E₀ Γ hgs hv ↦ (hgood E₀ Γ hgs hv).1⟩

end TNLean.MPS.AreaLaw
