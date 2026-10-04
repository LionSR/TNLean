/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactMPSGappedPhase
import TNLean.MPS.Symmetry.IsometricParentInteraction
import TNLean.MPS.Core.PhysicalIndexMixing
import TNLean.MPS.SharedInfra.Scaling

/-!
# Gauge invariance of the independent exact MPS phase condition

A nonzero scalar rescaling and an invertible change of bond basis preserve
the canonical parent interactions and the positive-length periodic vector
rays. Consequently endpoint gauge preparation preserves the independent
physical phase condition, with the same blocking, endpoint characters,
orthogonal physical inclusions, interaction path, and ground-state family.

Source context: Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.B,
standard form and parent Hamiltonians, lines 325–380; Section II.C.2,
lines 440–466; and Section II.F.2, lines 886–929. The conclusion concerns
the independently defined physical relation, rather than equality of
virtual factor systems.
-/

open scoped Matrix

namespace MPSTensor

/-- Blocking a scalar rescaling raises the scalar to the block length.
Source context: arXiv:1010.3732, Section II.B, lines 325–355. -/
theorem blockTensor_smul {d D : ℕ} (c : ℂ) (A : MPSTensor d D) (k : ℕ) :
    blockTensor (c • A) k = c ^ k • blockTensor A k := by
  funext i
  simpa only [blockTensor, Kraus.blockTensor, Kraus.length_wordOfBlock, Pi.smul_def,
    Pi.smul_apply] using
    Kraus.evalWord_smul c A (Kraus.wordOfBlock d k i)

/-- Physical inclusion preserves an invertible bond gauge. Source context:
arXiv:1010.3732, Section II.C.2, lines 440–466. -/
theorem GaugeEquiv.rotatePhysical {d m D : ℕ} {A B : MPSTensor d D}
    (h : GaugeEquiv A B) (E : Matrix (Fin m) (Fin d) ℂ) :
    GaugeEquiv (rotatePhysical E A) (rotatePhysical E B) := by
  exact h.sum_smul E

/-- Physical inclusion commutes with scalar rescaling of a tensor. Source
context: arXiv:1010.3732, Section II.C.2, lines 440–466. -/
theorem rotatePhysical_smul {d m D : ℕ} (E : Matrix (Fin m) (Fin d) ℂ)
    (c : ℂ) (A : MPSTensor d D) : rotatePhysical E (c • A) = c • rotatePhysical E A := by
  funext i
  simp only [rotatePhysical, Pi.smul_apply, Finset.smul_sum, smul_comm c]

/-- Nonzero rescaling and a bond gauge preserve every positive-length
periodic vector ray. Source context: arXiv:1010.3732, Section II.B,
lines 325–380. -/
theorem samePositiveMpvRay_of_smul_gaugeEquiv {d D : ℕ} {A B : MPSTensor d D}
    (c : ℂ) (hc : c ≠ 0) (h : GaugeEquiv (c • A) B) : SamePositiveMpvRay A B := by
  intro N _hN
  have hmpv : (mpv B : (Fin N → Fin d) → ℂ) = c ^ N • mpv A :=
    funext fun σ => (h.sameMPV N σ).symm.trans (mpv_smul c A σ)
  simpa only [hmpv] using
    (Submodule.span_singleton_smul_eq (pow_ne_zero N hc).isUnit (mpv A)).symm

/-- The canonical parent of a physically included tensor is unchanged by
nonzero scalar rescaling and an invertible bond gauge. Source context:
arXiv:1010.3732, Section II.B, lines 325–380, and Section II.C.2,
lines 440–466. -/
theorem parentInteraction_matrix_rotatePhysical_eq_of_smul_gaugeEquiv
    {d m D : ℕ} {A B : MPSTensor d D}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (c : ℂ) (hc : c ≠ 0) (h : GaugeEquiv (c • A) B) :
    LinearMap.toMatrix' (parentInteraction (rotatePhysical E A) 2) =
      LinearMap.toMatrix' (parentInteraction (rotatePhysical E B) 2) := by
  have hParent : parentInteraction A 2 = parentInteraction B 2 :=
    parentInteraction_eq_of_groundSpace_eq
      ((groundSpace_smul_eq A c hc 2).symm.trans (h.groundSpace_eq 2))
  rw [parentInteraction_matrix_rotatePhysical_eq_isometricInteractionExtension E hE A,
    parentInteraction_matrix_rotatePhysical_eq_isometricInteractionExtension E hE B, hParent]

/-- Endpoint preparation by nonzero rescaling and bond gauge preserves the
independent exact MPS phase condition. The same physical inclusions and
characters witness the conclusion. Source context: arXiv:1010.3732,
Sections II.B and II.C.2, lines 325–380 and 440–466, and Section II.F.2,
lines 886–929. -/
theorem IsSameExactMPSGappedPhase.of_smul_gaugeEquiv
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ}
    {A₀ B₀ : MPSTensor d₀ D₀} {A₁ B₁ : MPSTensor d₁ D₁}
    {U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ}
    {U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ}
    (h : IsSameExactMPSGappedPhase B₀ B₁ U₀ U₁)
    (c₀ c₁ : ℂ) (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (h₀ : GaugeEquiv (c₀ • A₀) B₀) (h₁ : GaugeEquiv (c₁ • A₁) B₁) :
    IsSameExactMPSGappedPhase A₀ A₁ U₀ U₁ := by
  rcases h with ⟨k, hk, m, U, χ₀, χ₁, hχ₀, hχ₁, E₀, E₁,
    hE₀, hE₁, hEorth, hCov₀, hCov₁, P, Q, hQ₀, hQ₁⟩
  have hBlock₀ : GaugeEquiv (c₀ ^ k • blockTensor A₀ k) (blockTensor B₀ k) := by
    simpa only [blockTensor_smul] using h₀.blockTensor k
  have hBlock₁ : GaugeEquiv (c₁ ^ k • blockTensor A₁ k) (blockTensor B₁ k) := by
    simpa only [blockTensor_smul] using h₁.blockTensor k
  have hParent₀ := parentInteraction_matrix_rotatePhysical_eq_of_smul_gaugeEquiv
    E₀ hE₀ (c₀ ^ k) (pow_ne_zero k hc₀) hBlock₀
  have hParent₁ := parentInteraction_matrix_rotatePhysical_eq_of_smul_gaugeEquiv
    E₁ hE₁ (c₁ ^ k) (pow_ne_zero k hc₁) hBlock₁
  have hRotate₀ : GaugeEquiv (c₀ ^ k • rotatePhysical E₀ (blockTensor A₀ k))
      (rotatePhysical E₀ (blockTensor B₀ k)) := by
    simpa only [rotatePhysical_smul] using hBlock₀.rotatePhysical E₀
  have hRotate₁ : GaugeEquiv (c₁ ^ k • rotatePhysical E₁ (blockTensor A₁ k))
      (rotatePhysical E₁ (blockTensor B₁ k)) := by
    simpa only [rotatePhysical_smul] using hBlock₁.rotatePhysical E₁
  refine ⟨k, hk, m, U, χ₀, χ₁, hχ₀, hχ₁, E₀, E₁,
    hE₀, hE₁, hEorth, hCov₀, hCov₁, ?_⟩
  rw [hParent₀, hParent₁]
  exact ⟨P, Q,
    hQ₀.trans (samePositiveMpvRay_of_smul_gaugeEquiv _ (pow_ne_zero k hc₀) hRotate₀).symm,
    hQ₁.trans (samePositiveMpvRay_of_smul_gaugeEquiv _ (pow_ne_zero k hc₁) hRotate₁).symm⟩

end MPSTensor
