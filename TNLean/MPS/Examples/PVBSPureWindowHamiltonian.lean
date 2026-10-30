/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.PVBSOneParticleWindow
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicInteractionSections

/-!
# The pure one-particle projector on adjacent windows

The orthogonal complement of the geometric one-particle line defines a positive
local interaction. Its actual periodic Hamiltonian on the union of two adjacent
windows has zero kernel. The local section equations are derived from the
Hamiltonian equation by positivity, not supplied separately.

This is a component of the finite-prefix investigation of SPWC10,
arXiv:0909.5347, Theorem 5, lines 850--880. It makes no assertion about a
full model with a unique ground state at every volume.
-/

namespace MPSTensor

/-- The complementary projection of the existing geometric one-particle line.
Source: the PVBS one-particle coefficients, arXiv:1112.4097, Section II,
equations (1)--(8), restricted to the pure particle line. -/
noncomputable def pvbsPureWindowInteraction (q : ℂ) (R : ℕ) :
    MPVSpace 2 R →ₗ[ℂ] MPVSpace 2 R :=
  (Submodule.span ℂ {WithLp.toLp 2 (pvbsEdge q R)})ᗮ.starProjection.toLinearMap

/-- The pure particle-line interaction is positive.
Source: orthogonal projection onto the complement of the PVBS particle line. -/
theorem pvbsPureWindowInteraction_isPositive (q : ℂ) (R : ℕ) :
    (pvbsPureWindowInteraction q R).IsPositive :=
  (Submodule.isSymmetricProjection_starProjection
    (Submodule.span ℂ {WithLp.toLp 2 (pvbsEdge q R)})ᗮ).isPositive

/-- A local vector is killed precisely when it is a scalar multiple of the
actual geometric one-particle vector. Source: the complementary projection of
the pure PVBS particle line, arXiv:1112.4097, Section II. -/
theorem pvbsPureWindowInteraction_apply_eq_zero_iff (q : ℂ) (R : ℕ)
    (ψ : MPVSpace 2 R) :
    pvbsPureWindowInteraction q R ψ = 0 ↔
      ∃ c : ℂ, ∀ σ, ψ σ = c * pvbsEdge q R σ := by
  have hker : pvbsPureWindowInteraction q R ψ = 0 ↔
      ψ ∈ Submodule.span ℂ {WithLp.toLp 2 (pvbsEdge q R)} := by
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

/-- The two actual translated pure particle projectors on neighbouring windows
have no common kernel on their union. Source: the overlapping-window obstruction
for the PVBS particle line, arXiv:1112.4097, Section II. -/
theorem eq_zero_of_pvbsPureWindow_adjacent_terms_eq_zero
    (q : ℂ) (hq : q ≠ 0) (N : ℕ) (ψ : MPVSpace 2 (N + 3))
    (hleftTerm : periodicLocalInteractionES (pvbsPureWindowInteraction q (N + 2))
      (⟨0, by omega⟩ : Fin (N + 3)) ψ = 0)
    (hrightTerm : periodicLocalInteractionES (pvbsPureWindowInteraction q (N + 2))
      (⟨1, by omega⟩ : Fin (N + 3)) ψ = 0) : ψ = 0 := by
  have hsections₀ := (periodicLocalInteractionES_eq_zero_iff_sections
    (pvbsPureWindowInteraction q (N + 2)) (by omega) (by omega)
    (⟨0, by omega⟩ : Fin (N + 3)) ψ).mp hleftTerm
  have hsections₁ := (periodicLocalInteractionES_eq_zero_iff_sections
    (pvbsPureWindowInteraction q (N + 2)) (by omega) (by omega)
    (⟨1, by omega⟩ : Fin (N + 3)) ψ).mp hrightTerm
  have hleft (c : Fin 2) : ∃ f : ℂ, ∀ σ : Cfg 2 (N + 2),
      ψ (Fin.snoc σ c) = f * pvbsEdge q (N + 2) σ := by
    obtain ⟨f, hf⟩ := (pvbsPureWindowInteraction_apply_eq_zero_iff q (N + 2)
      (cyclicRestrictES (by omega) (N + 2) ⟨0, by omega⟩ (Fin.snoc 0 c) ψ)).mp
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
    obtain ⟨g, hg⟩ := (pvbsPureWindowInteraction_apply_eq_zero_iff q (N + 2)
      (cyclicRestrictES (by omega) (N + 2) ⟨1, by omega⟩ (Fin.cons a 0) ψ)).mp
        (hsections₁ (Fin.cons a 0))
    refine ⟨g, fun σ ↦ ?_⟩
    have hcfg : cyclicCfg (by omega) (N + 2) (⟨1, by omega⟩ : Fin (N + 3))
        σ (Fin.cons a 0) = Fin.cons a σ := by
      rw [cyclicCfg_eq_contiguousCfg (by omega) (by omega) (by simp; omega)]
      funext k
      refine Fin.cases ?_ (fun j ↦ ?_) k
      · simp [contiguousCfg]
      · have hj := j.isLt
        simp [contiguousCfg]
        exact fun h ↦ absurd h (by omega)
    have hσ := hg σ
    change ψ (cyclicCfg (by omega) (N + 2) ⟨1, by omega⟩ σ (Fin.cons a 0)) = _ at hσ
    rwa [hcfg] at hσ
  have hraw := eq_zero_of_pvbsEdge_overlapping_sections q hq ψ.ofLp hleft hright
  apply PiLp.ext
  intro σ
  exact congrFun hraw σ

/-- Every periodic volume strictly larger than the pure particle window has
zero Hamiltonian kernel. This includes range seven at every volume at least
eight. Positivity supplies the actual local term equations, and restriction to
an interval of one site more than the range supplies the adjacent-window
obstruction. No local or spectator kernel conclusion is assumed.
Source: the PVBS adjacent-window obstruction, arXiv:1112.4097, Section II;
the finite-prefix question in SPWC10, Theorem 5, lines 850--880. -/
theorem eq_zero_of_pvbsPureWindowHamiltonian_eq_zero
    (q : ℂ) (hq : q ≠ 0) (N : ℕ) {M : ℕ} (hM : N + 3 ≤ M)
    (ψ : MPVSpace 2 M)
    (hzero : periodicInteractionHamiltonianES (pvbsPureWindowInteraction q (N + 2))
      M ψ = 0) : ψ = 0 := by
  have hterms := (WeightedPositiveKernel.apply_sum_eq_zero_iff
    (fun i : Fin M ↦ periodicLocalInteractionES_isPositive
      (pvbsPureWindowInteraction_isPositive q (N + 2)) i) ψ).mp hzero
  let s : Fin M := ⟨0, by omega⟩
  let U := cyclicActiveBlockConfigLinearIsometryEquiv 2 (N + 3) hM s
  have hfiber (τ : Cfg 2 (M - (N + 3))) :
      ContinuousLinearMap.rightFiber (U ψ) τ = 0 := by
    apply eq_zero_of_pvbsPureWindow_adjacent_terms_eq_zero q hq N
    · exact periodicLocalInteractionES_rightFiber_eq_zero_of_eq_zero
        (pvbsPureWindowInteraction q (N + 2)) (by omega) hM s
        ⟨0, by omega⟩ (by simp) ψ (hterms _) τ
    · exact periodicLocalInteractionES_rightFiber_eq_zero_of_eq_zero
        (pvbsPureWindowInteraction q (N + 2)) (by omega) hM s
        ⟨1, by omega⟩ (by simp; omega) ψ (hterms _) τ
  apply U.injective
  rw [map_zero]
  apply PiLp.ext
  rintro ⟨σ, τ⟩
  exact congrArg (fun v ↦ v σ) (hfiber τ)

/-- At every volume greater than its range, the actual periodic Hamiltonian of
the pure particle-line interaction has trivial kernel.
Source: the adjacent-window obstruction for the PVBS particle line. -/
theorem ker_pvbsPureWindowHamiltonian_eq_bot
    (q : ℂ) (hq : q ≠ 0) (N : ℕ) {M : ℕ} (hM : N + 3 ≤ M) :
    LinearMap.ker (periodicInteractionHamiltonianES (pvbsPureWindowInteraction q (N + 2))
      M) = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro ψ hψ
  exact eq_zero_of_pvbsPureWindowHamiltonian_eq_zero q hq N hM ψ hψ

end MPSTensor
