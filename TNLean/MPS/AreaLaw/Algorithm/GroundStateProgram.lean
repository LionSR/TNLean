/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Algorithm.SweepProgram
import TNLean.MPS.AreaLaw.ViableSet.SuccessiveAccuracy
import TNLean.MPS.AreaLaw.OverlapEnergy

/-!
# The ground-state program

The algorithm of Landau, Vazirani and Vidick, as a program over the linear-algebra queries:
pad the chain by `2 R²` sites with a penalty on the padding, run the sweep on the padded
chain, read the final family on the original chain, and return a unit vector of least
energy in its span, the leading eigenvector of the final convex program. Run with the honest
oracle, the output is a unit matrix product state of polynomial bond dimension whose overlap
with the ground state is at least `1 - 4 L / (R² Δ)`, for every ground pair with gap `Δ`.

The padding replaces the paper's final error-reduction step at precision `c_ε / (n p(n))`
(lines 669--671): the sweep on the padded chain at its fixed precision gives a vector of the
final span within distance `1 / R` of the ground state, and the energy-overlap lemma turns the
least energy of the final convex program into the overlap bound.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, proof of Theorem 1, lines 652--678.
-/

open Matrix Cslib
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

variable {q : ℕ}

open LinearAlgebraQuery

/-- **The ground-state program** at accuracy parameter `R`: sweep the chain padded by
`2 R²` sites and return the solution of the final convex program over the final family, read
on the original chain. LVV13, `algo53.tex`, lines 652--678. -/
noncomputable def groundStateProgram {L : ℕ} (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    (Delta : ℝ) (R : ℕ) : LVVProgram q (EuclideanSpace ℂ (Fin L → Fin q)) :=
  let N := L + 2 * R ^ 2
  let hi : L ≤ N := Nat.le_add_right _ _
  let z : Fin q := ⟨0, by omega⟩
  open Classical in do
    let S ← sweepProgram hq (paddedInteraction hi z h) (paddedInteraction_supported hi z h hs)
      (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).1)
      (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).2) (min Delta 1) L
    FreeM.lift (LinearAlgebraQuery.energyMinimizer L (lvvSuccessiveBondBound q (min Delta 1) N)
      (∑ j, h j)
      (S.image fun w ↦
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv (q := q) hi)).symm w))

/-- With the honest oracle, the program returns the chosen energy minimizer over the final
family of the padded sweep, read on the original chain. -/
theorem eval_groundStateProgram {L : ℕ} (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    (Delta : ℝ) (R : ℕ) :
    let N := L + 2 * R ^ 2
    let hi : L ≤ N := Nat.le_add_right _ _
    let z : Fin q := ⟨0, by omega⟩
    FreeM.eval honestOracle (groundStateProgram hq h hs h0 h1 Delta R) =
      open Classical in
      energyMinimizer (∑ j, h j)
        ((lvvSweep hq (paddedInteraction hi z h) (paddedInteraction_supported hi z h hs)
          (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).1)
          (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).2) (min Delta 1) L).image
          fun w ↦
            (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
              (leftConfigOfFinEquiv (q := q) hi)).symm w) := by
  intro N hi z
  simp only [groundStateProgram, FreeM.eval_bind, FreeM.eval_lift, eval_sweepProgram,
    honestOracle_energyMinimizer]
  rfl

/-- A unit vector within squared distance `2 δ` of a unit vector has overlap at least
`1 - δ` with it. -/
theorem one_sub_le_norm_inner_of_norm_sub_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {δ : ℝ}
    (hxy : ‖x - y‖ ^ 2 ≤ 2 * δ) : 1 - δ ≤ ‖⟪y, x⟫_ℂ‖ := by
  have h := norm_sub_sq (𝕜 := ℂ) x y
  rw [hx, hy] at h
  have hre : 1 - δ ≤ RCLike.re ⟪x, y⟫_ℂ := by nlinarith
  calc
    1 - δ ≤ RCLike.re ⟪x, y⟫_ℂ := hre
    _ ≤ ‖⟪x, y⟫_ℂ‖ := RCLike.re_le_norm _
    _ = ‖⟪y, x⟫_ℂ‖ := by rw [← inner_conj_symm x y, RCLike.norm_conj]

/-- **The ground-state program finds the ground state** (LVV13, Theorem 1, the approximation
part). For every ground pair with gap `Δ > 0` and every `R ≥ 1`, the output of the program
with the honest oracle is a unit vector with overlap at least `1 - 4 L / (R² Δ)` with the
ground state, and an open-boundary matrix product state whose bond dimension is bounded by
the cardinality budget times the bond budget of the sweep on the padded chain. LVV13,
`algo53.tex`, lines 213--216 and 652--678. -/
theorem groundStateProgram_spec {L : ℕ} (hL : 1 ≤ L) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) {R : ℕ} (hR : 1 ≤ R)
    (E : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q))
    (hgs : IsGappedGroundState (∑ j, h j) E Γ Delta) :
    let N := L + 2 * R ^ 2
    let ψ := FreeM.eval honestOracle (groundStateProgram hq h hs h0 h1 Delta R)
    ‖ψ‖ = 1 ∧ 1 - 4 * L / (R ^ 2 * Delta) ≤ ‖⟪Γ, ψ⟫_ℂ‖ ∧
      IsOpenMPS L q (lvvSuccessiveCardBound q (min Delta 1) N *
        max 1 (lvvSuccessiveBondBound q (min Delta 1) N)) (fun x ↦ ψ x) := by
  classical
  intro N ψ
  have hi : L ≤ N := Nat.le_add_right _ _
  let z : Fin q := ⟨0, by omega⟩
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv (q := q) hi)
  let hs' := paddedInteraction_supported hi z h hs
  let h0' := fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).1
  let h1' := fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).2
  set S := lvvSweep hq (paddedInteraction hi z h) hs' h0' h1' (min Delta 1) L with hSdef
  have hψ : ψ = energyMinimizer (∑ j, h j) (S.image fun w ↦ e.symm w) :=
    eval_groundStateProgram hq h hs h0 h1 Delta R
  have hg : 0 < min Delta 1 := lt_min hDelta zero_lt_one
  have hN : 1 ≤ N := hL.trans hi
  obtain ⟨hcard, hmps, hviable⟩ := lvvSweep_spec hq (paddedInteraction hi z h) hs' h0' h1' hg L hi
  simp only [show L ≠ 0 by omega, ↓reduceIte] at hcard hmps
  have hpad := isGappedGroundState_paddedInteraction hL hi z h hgs hDelta
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  set δ : ℝ := lvvSuccessiveError (min Delta 1) / N with hδdef
  have hδ1 : δ < 1 := by
    apply (div_lt_one hNreal).mpr
    exact (lvvSuccessiveError_min_lt_one hDelta).trans_le (by exact_mod_cast hN)
  have hδ0 : 0 ≤ δ := div_nonneg (lvvSuccessiveError_pos hg).le hNreal.le
  obtain ⟨w, hw, hwnorm, herror, hwmps⟩ :=
    (hviable E _ hpad).exists_prefix_mps_of_paddedGroundVector hi z hgs.1 hδ1 hmps
  -- The span of the final family, read on the original chain.
  set U := Submodule.span ℂ ((S.image fun w ↦ e.symm w : Finset _) :
    Set (EuclideanSpace ℂ (Fin L → Fin q))) with hUdef
  have hUmap : U = (Submodule.span ℂ (S : Set (LeftBlockVector N q L))).map
      e.symm.toLinearEquiv.toLinearMap := by
    rw [hUdef, Finset.coe_image, Submodule.map_span]
    rfl
  have hw'U : e.symm w ∈ U := by
    rw [hUmap]
    exact Submodule.mem_map_of_mem hw
  have hw'norm : ‖e.symm w‖ = 1 := by rw [e.symm.norm_map, hwnorm]
  have hUne : U ≠ ⊥ := by
    intro hbot
    have : e.symm w = 0 := by simpa only [hbot, Submodule.mem_bot] using hw'U
    rw [this, norm_zero] at hw'norm
    exact zero_ne_one hw'norm
  obtain ⟨hψU, hψnorm, hψmin⟩ := energyMinimizer_spec (∑ j, h j) (S.image fun w ↦ e.symm w) hUne
  rw [← hψ] at hψU hψnorm hψmin
  refine ⟨hψnorm, ?_, ?_⟩
  · -- Overlap: least energy in the span, then the gap.
    obtain ⟨hΓ, hEig, hgap⟩ := isGappedGroundState_iff.mp hgs
    have hover : 1 - δ ≤ ‖⟪Γ, e.symm w⟫_ℂ‖ :=
      one_sub_le_norm_inner_of_norm_sub_sq_le hw'norm hgs.1 herror
    let chain := ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1
    have hchain : chain.operator = ∑ j, h j :=
      ChainHamiltonian.ofNearestNeighborPositive_operator h hs h0 h1
    have hgsChain : IsGappedGroundState chain.operator E Γ Delta := by rwa [hchain]
    have henergy := chain.re_inner_sub_le_of_overlap_of_range_one hgsChain hw'norm hover
    rw [hchain] at henergy
    have hψenergy : (⟪ψ, toEuclideanLin (∑ j, h j) ψ⟫_ℂ).re - E ≤ 8 * L * δ :=
      (sub_le_sub_right (hψmin _ hw'U hw'norm) E).trans henergy
    have hbound := Entropy.norm_inner_ge_of_gap hDelta hgap hΓ hψnorm hψenergy
    refine le_trans ?_ hbound
    -- `8 L δ / Δ ≤ 4 L / (R² Δ)` since `δ ≤ 1 / (2 R²)`.
    have hR2 : (0 : ℝ) < (R : ℝ) ^ 2 := by positivity
    have hNR : 2 * (R : ℝ) ^ 2 ≤ N := by
      exact_mod_cast (show 2 * R ^ 2 ≤ N from Nat.le_add_left _ _)
    have hc1 : lvvSuccessiveError (min Delta 1) ≤ 1 := (lvvSuccessiveError_min_lt_one hDelta).le
    have hδle : δ ≤ 1 / (2 * (R : ℝ) ^ 2) := by
      rw [hδdef, div_le_div_iff₀ hNreal (by positivity)]
      nlinarith [lvvSuccessiveError_pos hg]
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have : 8 * L * δ / Delta ≤ 4 * L / (R ^ 2 * Delta) := by
      rw [div_le_div_iff₀ hDelta (by positivity)]
      calc 8 * L * δ * (R ^ 2 * Delta)
          ≤ 8 * L * (1 / (2 * (R : ℝ) ^ 2)) * (R ^ 2 * Delta) := by gcongr
        _ = 4 * L * Delta := by field_simp; ring
    linarith
  · -- The output is a matrix product state of the final span's bond dimension.
    have hψU' : ψ ∈ U := hψU
    rw [hUmap] at hψU'
    obtain ⟨v, hv, hvψ⟩ := Submodule.mem_map.mp hψU'
    have hvmps := isOpenMPS_leftChain_of_mem_span S hmps hv
    have hcoord : (fun x ↦ ψ x) = fun x ↦ v (leftConfigOfFin x) := by
      rw [← hvψ]
      rfl
    rw [hcoord]
    exact hvmps.mono (Nat.mul_le_mul_right _ hcard)

end TNLean.MPS.AreaLaw
