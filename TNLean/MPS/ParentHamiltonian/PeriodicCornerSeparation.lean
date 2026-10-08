/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicGroundSpaceIndependence
import TNLean.MPS.ParentHamiltonian.PrimitiveSectorRepresentatives
import TNLean.MPS.ParentHamiltonian.BlockedGroundSpaceTransport

/-!
# Separation of corners belonging to distinct periodic tensors

An isometric corner with a letter intertwiner has its boundary spaces
contained in those of the original tensor. If two primitive blocked corners
were equivalent up to gauge and phase, their boundary spaces would agree.
A nonzero vector in this common space, reindexed into the original site
coordinates, would then belong to both original boundary spaces. The
vanishing original-chain angle for inequivalent periodic tensors excludes
this possibility.

The result concerns arbitrary common positive blocking lengths and literal
isometric corners. It does not infer corner separation from the names of the
blocks or from inequivalence at a single finite volume.

Sources: arXiv:1708.00029, Lemma bdcf;
Nachtergaele, arXiv:cond-mat/9410110, proof of Lemma disjoint, equations
C1C2 and limP12.
-/

open scoped Matrix BigOperators InnerProductSpace Matrix.Norms.Frobenius ComplexOrder
open Filter
namespace MPSTensor
variable {d D E D₂ F L : ℕ}

/-- An isometric virtual embedding with the adjoint letter intertwiner
places every sector boundary vector in the original boundary space.
Source: arXiv:1708.00029, Lemma bdcf and equation Aoffdiag. -/
theorem groundSpaceES_le_of_isometric_cointertwiner
    (A : MPSTensor d D) (B : MPSTensor d E) (V : Matrix (Fin D) (Fin E) ℂ)
    (hV : Vᴴ * V = 1) (hInt : ∀ i, Vᴴ * A i = B i * Vᴴ) (N : ℕ) :
    groundSpaceES B N ≤ groundSpaceES A N := by
  have hEmbed (Y : Matrix (Fin E) (Fin E) ℂ) :
      groundSpaceMap A N (V * Y * Vᴴ) = groundSpaceMap B N Y := by
    ext σ
    simp only [groundSpaceMap_apply]
    have hWord := Kraus.evalWord_intertwine B A Vᴴ (fun i => (hInt i).symm) (List.ofFn σ)
    calc
      _ = Matrix.trace (Vᴴ * (Kraus.evalWord A (List.ofFn σ) * V * Y)) := by
        simpa only [Matrix.mul_assoc] using
          Matrix.trace_mul_comm (Kraus.evalWord A (List.ofFn σ) * V * Y) Vᴴ
      _ = _ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hWord, Matrix.mul_assoc,
          Matrix.mul_assoc (Kraus.evalWord B (List.ofFn σ)) Vᴴ (V * Y),
          ← Matrix.mul_assoc Vᴴ V Y, hV, Matrix.one_mul]
  rw [← range_groundSpaceMapES, ← range_groundSpaceMapES]
  rintro _ ⟨u, rfl⟩
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)).surjective u
  refine ⟨Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) (V * Y * Vᴴ), ?_⟩
  change groundSpaceMapES A N (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
    (V * Y * Vᴴ)) = groundSpaceMapES B N (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E) Y)
  rw [groundSpaceMapES_frobeniusEquivEuclidean_apply,
    groundSpaceMapES_frobeniusEquivEuclidean_apply, hEmbed]

/-- Primitive corners of gauge-phase inequivalent normalized periodic
original tensors cannot be gauge-phase equivalent at a common positive
blocking length. Only one corner requires a primitive faithful witness.
Source: arXiv:1708.00029, Lemma bdcf;
Nachtergaele, arXiv:cond-mat/9410110, proof of Lemma disjoint, equations
C1C2 and limP12. The proof uses original-chain boundary-space separation,
not an unproved separation assumption on compressed sectors. -/
theorem IsPeriodic.not_gaugePhaseEquiv_of_primitive_corners
    [NeZero E] {m m₂ : ℕ} {A : MPSTensor d D} {A' : MPSTensor d D₂}
    (hA : IsPeriodic m A) (hA' : IsPeriodic m₂ A')
    (hDistinct : ∀ e : D₂ = D, ¬ GaugePhaseEquiv (e ▸ A') A)
    (hL : 0 < L) (B : MPSTensor (blockPhysDim d L) E)
    (C : MPSTensor (blockPhysDim d L) F)
    (V : Matrix (Fin D) (Fin E) ℂ) (W : Matrix (Fin D₂) (Fin F) ℂ)
    {ρ : Matrix (Fin E) (Fin E) ℂ} (hB : IsPrimitiveMPS B ρ) (hρ : ρ.PosDef)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (hInt : ∀ i, Vᴴ * blockTensor A L i = B i * Vᴴ)
    (hInt' : ∀ i, Wᴴ * blockTensor A' L i = C i * Wᴴ) :
    ∀ e : F = E, ¬ GaugePhaseEquiv (e ▸ C) B := by
  intro e hGauge
  subst F
  have hCLength : Tendsto (fun n : ℕ => n * L) atTop atTop :=
    tendsto_id.atTop_mul_one_le (fun _ => hL)
  have hAngle := hCLength.eventually
    (hA.eventually_norm_inner_groundSpaceES_le_of_inequivalent hA' hDistinct
      (show (0 : ℝ) < 1 / 2 by norm_num))
  have hInject := hB.eventually_groundSpaceMapES_injective_and_inverseGram_bound hρ
    (a := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨N, hN, hInj, hInverse⟩ := (hAngle.and hInject).exists
  let u : EuclideanSpace ℂ (Fin E × Fin E) :=
    Matrix.frobeniusEquivEuclidean (Fin E) (Fin E) 1
  let x := groundSpaceMapES B N u
  have hx : x ∈ groundSpaceES B N := by
    rw [← range_groundSpaceMapES]
    exact ⟨u, rfl⟩
  have hxne : x ≠ 0 := by
    intro hz
    have hu : u = 0 := hInj (by simpa only [map_zero, x] using hz)
    have h1 : (1 : Matrix (Fin E) (Fin E) ℂ) = 0 :=
      (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)).injective (by
        simpa only [map_zero, u] using hu)
    exact one_ne_zero h1
  have hxC : x ∈ groundSpaceES C N := by
    have hGauge' : GaugePhaseEquiv C B := by simpa using hGauge
    rw [hGauge'.groundSpaceES_eq N]
    exact hx
  let U := blockedConfigLinearIsometryEquiv d N L
  have hxA : U x ∈ groundSpaceES A (N * L) := by
    rw [← groundSpaceES_blockTensor_map A L N]
    exact ⟨x, groundSpaceES_le_of_isometric_cointertwiner
      (blockTensor A L) B V hV hInt N hx, rfl⟩
  have hxA' : U x ∈ groundSpaceES A' (N * L) := by
    rw [← groundSpaceES_blockTensor_map A' L N]
    exact ⟨x, groundSpaceES_le_of_isometric_cointertwiner
      (blockTensor A' L) C W hW hInt' N hxC, rfl⟩
  have h := hN (U x) hxA (U x) hxA'
  rw [U.inner_map_map, U.norm_map] at h
  simp only [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg x)] at h
  nlinarith [norm_pos_iff.mpr hxne]

end MPSTensor
