/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.PVBS.PVBSOneParticleWindow
import TNLean.MPS.ParentHamiltonian.Interaction.PeriodicInteractionSections

/-!
# The pure one-particle projector on adjacent windows

The orthogonal complement of the geometric one-particle line defines a positive
semidefinite local matrix. The Hamiltonian of its translates around a ring on
the union of two adjacent windows has zero kernel. The local section equations are derived from the
Hamiltonian equation by positivity, not supplied separately.

This is a component of the finite-prefix investigation of SPWC10,
arXiv:0909.5347, Theorem 5, lines 850--880. It makes no assertion about a
full model with a unique ground state at every volume.
-/

open scoped ComplexOrder MatrixOrder
open ManyBody.Interaction (translationInvariant)

namespace MPSTensor

/-- The matrix of the complementary projection of the existing geometric one-particle line.
Source: the PVBS one-particle coefficients, arXiv:1112.4097, Section II,
equations (1)--(8), restricted to the pure particle line. -/
noncomputable def pvbsPureWindowInteraction (q : ℂ) (R : ℕ) :
    Matrix (Cfg 2 R) (Cfg 2 R) ℂ :=
  Matrix.toEuclideanLin.symm
    (Submodule.span ℂ {WithLp.toLp 2 (pvbsEdge q R)})ᗮ.starProjection.toLinearMap

/-- The pure particle-line interaction is positive semidefinite.
Source: orthogonal projection onto the complement of the PVBS particle line. -/
theorem posSemidef_pvbsPureWindowInteraction (q : ℂ) (R : ℕ) :
    (pvbsPureWindowInteraction q R).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff, pvbsPureWindowInteraction,
    LinearEquiv.apply_symm_apply]
  exact (Submodule.isSymmetricProjection_starProjection
    (Submodule.span ℂ {WithLp.toLp 2 (pvbsEdge q R)})ᗮ).isPositive

/-- A local vector is killed precisely when it is a scalar multiple of the
actual geometric one-particle vector. Source: the complementary projection of
the pure PVBS particle line, arXiv:1112.4097, Section II. -/
theorem toEuclideanLin_pvbsPureWindowInteraction_apply_eq_zero_iff (q : ℂ) (R : ℕ)
    (ψ : MPVSpace (Fin 2) R) :
    Matrix.toEuclideanLin (pvbsPureWindowInteraction q R) ψ = 0 ↔
      ∃ c : ℂ, ∀ σ, ψ σ = c * pvbsEdge q R σ := by
  have hker : Matrix.toEuclideanLin (pvbsPureWindowInteraction q R) ψ = 0 ↔
      ψ ∈ Submodule.span ℂ {WithLp.toLp 2 (pvbsEdge q R)} := by
    rw [pvbsPureWindowInteraction, LinearEquiv.apply_symm_apply]
    change (Submodule.span ℂ {WithLp.toLp 2 (pvbsEdge q R)})ᗮ.starProjection ψ = 0 ↔ _
    rw [Submodule.starProjection_orthogonal']
    simp only [sub_apply, one_apply_eq_self]
    rw [sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]
  rw [hker, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, fun _ ↦ rfl⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    ext σ
    exact (hc σ).symm

/-- The two translated pure particle projectors on neighbouring windows
have no common kernel on their union. Source: the overlapping-window obstruction
for the PVBS particle line, arXiv:1112.4097, Section II. -/
theorem eq_zero_of_pvbsPureWindow_adjacent_terms_eq_zero
    (q : ℂ) (hq : q ≠ 0) (N : ℕ) (ψ : MPVSpace (Fin 2) (N + 3))
    (hleftTerm : Matrix.toEuclideanLin
      ((translationInvariant (N + 3) (pvbsPureWindowInteraction q (N + 2))).term
        ⟨0, by omega⟩) ψ = 0)
    (hrightTerm : Matrix.toEuclideanLin
      ((translationInvariant (N + 3) (pvbsPureWindowInteraction q (N + 2))).term
        ⟨1, by omega⟩) ψ = 0) : ψ = 0 := by
  have hsections₀ := (toEuclideanLin_translationInvariant_term_eq_zero_iff_sections
    (by omega) (pvbsPureWindowInteraction q (N + 2))
    (⟨0, by omega⟩ : Fin (N + 3)) ψ).mp hleftTerm
  have hsections₁ := (toEuclideanLin_translationInvariant_term_eq_zero_iff_sections
    (by omega) (pvbsPureWindowInteraction q (N + 2))
    (⟨1, by omega⟩ : Fin (N + 3)) ψ).mp hrightTerm
  have hleft (c : Fin 2) : ∃ f : ℂ, ∀ σ : Cfg 2 (N + 2),
      ψ (Fin.snoc σ c) = f * pvbsEdge q (N + 2) σ := by
    obtain ⟨f, hf⟩ := (toEuclideanLin_pvbsPureWindowInteraction_apply_eq_zero_iff q
      (N + 2) (LinearMap.withLpMap 2 (cyclicRestrictₗ (by omega) (N + 2) ⟨0, by omega⟩ (Fin.snoc 0
          c)) ψ)).mp
        (hsections₀ (Fin.snoc 0 c))
    refine ⟨f, fun σ ↦ ?_⟩
    have hcfg : cyclicCfg (by omega) (N + 2) (⟨0, by omega⟩ : Fin (N + 3))
        σ (Fin.snoc 0 c) = Fin.snoc σ c := by
      rw [cyclicCfg_eq_contiguousCfg (by omega) (by omega) (by simp)]
      funext k
      refine Fin.lastCases ?_ (fun j ↦ ?_) k
      · simp [contiguousCfg]
      · simp [contiguousCfg, j.isLt]
    have hσ := hf σ
    change ψ (cyclicCfg (by omega) (N + 2) ⟨0, by omega⟩ σ (Fin.snoc 0 c)) = _ at hσ
    rwa [hcfg] at hσ
  have hright (a : Fin 2) : ∃ g : ℂ, ∀ σ : Cfg 2 (N + 2),
      ψ (Fin.cons a σ) = g * pvbsEdge q (N + 2) σ := by
    obtain ⟨g, hg⟩ := (toEuclideanLin_pvbsPureWindowInteraction_apply_eq_zero_iff q
      (N + 2) (LinearMap.withLpMap 2 (cyclicRestrictₗ (by omega) (N + 2) ⟨1, by omega⟩ (Fin.cons a
          0)) ψ)).mp
        (hsections₁ (Fin.cons a 0))
    refine ⟨g, fun σ ↦ ?_⟩
    have hcfg : cyclicCfg (by omega) (N + 2) (⟨1, by omega⟩ : Fin (N + 3))
        σ (Fin.cons a 0) = Fin.cons a σ := by
      rw [cyclicCfg_eq_contiguousCfg (by omega) (by omega) (by simp; omega)]
      funext k
      refine Fin.cases ?_ (fun j ↦ ?_) k
      · simp [contiguousCfg]
      · have hj := j.isLt
        rw [Fin.cons_succ]
        simp only [contiguousCfg]
        rw [dite_eq_left (show 1 ≤ (j.succ : ℕ) ∧ (j.succ : ℕ) < 1 + (N + 2) by
          simp only [Fin.val_succ]; omega)]
        exact congrArg σ (Fin.ext (by simp))
    have hσ := hg σ
    change ψ (cyclicCfg (by omega) (N + 2) ⟨1, by omega⟩ σ (Fin.cons a 0)) = _ at hσ
    rwa [hcfg] at hσ
  have hraw := eq_zero_of_pvbsEdge_overlapping_sections q hq ψ.ofLp hleft hright
  apply PiLp.ext
  intro σ
  exact congrFun hraw σ

/-- On every ring strictly longer than the pure particle window, the Hamiltonian of the
translates of the pure particle projector has zero kernel. This includes range seven at
every volume at least eight. Positivity supplies the actual local term equations, and restriction to
an interval of one site more than the range supplies the adjacent-window
obstruction. No local or spectator kernel conclusion is assumed.
Source: the PVBS adjacent-window obstruction, arXiv:1112.4097, Section II;
the finite-prefix question in SPWC10, Theorem 5, lines 850--880. -/
theorem eq_zero_of_pvbsPureWindowHamiltonian_eq_zero
    (q : ℂ) (hq : q ≠ 0) (N : ℕ) {M : ℕ} (hM : N + 3 ≤ M)
    (ψ : MPVSpace (Fin 2) M)
    (hzero : haveI : NeZero M := ⟨by omega⟩;
      Matrix.toEuclideanLin
        (translationInvariant M (pvbsPureWindowInteraction q (N + 2))).hamiltonian ψ = 0) :
    ψ = 0 := by
  have : NeZero M := ⟨by omega⟩
  rw [ManyBody.Interaction.hamiltonian, map_sum] at hzero
  have hterms := (WeightedPositiveKernel.apply_sum_eq_zero_iff
    (fun i : Fin M ↦ Matrix.isPositive_toEuclideanLin_iff.mpr (Matrix.nonneg_iff_posSemidef.mp
      (ManyBody.Interaction.translationInvariant_term_nonneg (Matrix.nonneg_iff_posSemidef.mpr
        (posSemidef_pvbsPureWindowInteraction q (N + 2))) i))) ψ).mp hzero
  let s : Fin M := ⟨0, by omega⟩
  let U := cyclicActiveBlockConfigLinearIsometryEquiv 2 (N + 3) hM s
  have hfiber (τ : Cfg 2 (M - (N + 3))) :
      ContinuousLinearMap.rightFiber (U ψ) τ = 0 := by
    apply eq_zero_of_pvbsPureWindow_adjacent_terms_eq_zero q hq N
    · exact toEuclideanLin_translationInvariant_term_rightFiber_eq_zero_of_eq_zero
        (pvbsPureWindowInteraction q (N + 2)) hM s
        ⟨0, by omega⟩ (by simp) ψ (hterms _) τ
    · exact toEuclideanLin_translationInvariant_term_rightFiber_eq_zero_of_eq_zero
        (pvbsPureWindowInteraction q (N + 2)) hM s
        ⟨1, by omega⟩ (by simp; omega) ψ (hterms _) τ
  apply U.injective
  rw [map_zero]
  apply PiLp.ext
  rintro ⟨σ, τ⟩
  exact congrArg (fun v ↦ v σ) (hfiber τ)

/-- On every ring longer than its range, the Hamiltonian of the translates of the pure
particle-line interaction has trivial kernel.
Source: the adjacent-window obstruction for the PVBS particle line. -/
theorem ker_pvbsPureWindowHamiltonian_eq_bot
    (q : ℂ) (hq : q ≠ 0) (N : ℕ) {M : ℕ} (hM : N + 3 ≤ M) :
    haveI : NeZero M := ⟨by omega⟩;
    LinearMap.ker (Matrix.toEuclideanLin
      (translationInvariant M (pvbsPureWindowInteraction q (N + 2))).hamiltonian) = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro ψ hψ
  exact eq_zero_of_pvbsPureWindowHamiltonian_eq_zero q hq N hM ψ hψ

end MPSTensor
