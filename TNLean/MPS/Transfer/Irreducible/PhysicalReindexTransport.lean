/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Transfer.Irreducible.BlockingInfrastructure
import QICLean.Kraus.PrimitiveFixedPoint.Blocking

/-!
# Physical reindexing along alphabet equivalences

This file proves that changing physical letters by a bijection preserves the
basic tensor properties used by blocking and canonical-form arguments.

## Main statements

* `reindexPhysical_cast_dim` — physical reindexing commutes with bond-dimension casts.
* `isPrimitive_transferMap_reindexPhysical_equiv` — transfer-map primitivity is preserved,
  since the transfer map is unchanged (`Kraus.transferMap_reindexPhysical_equiv`; trace
  preservation is `Kraus.isTP_reindexPhysical_iff`).
* `isInjective_reindexPhysical_equiv` and `isNormal_reindexPhysical_equiv` — one-site injectivity
  and normality are preserved (invariant projections and irreducibility:
  `Kraus.hasInvariantProj_reindexPhysical_equiv`, `Kraus.isIrreducibleFamily_reindexPhysical_equiv`).
* `gaugePhaseEquiv_reindexPhysical_equiv` — gauge-phase equivalence is preserved
  when both tensors are reindexed by the same physical alphabet bijection.
* `linearIndependent_mpvState_of_configEquiv` transports linear independence of MPV state
  vectors through an arbitrary equivalence of configuration spaces.
* `mpvOverlap_reindexPhysical_equiv` and
  `linearIndependent_mpvState_reindexPhysical_equiv` — closed overlaps and
  linear independence of MPV states are preserved.
-/

open MPTensor

open scoped Matrix BigOperators

namespace MPSTensor

/-- Physical reindexing commutes with bond-dimension casts. -/
theorem reindexPhysical_cast_dim {α₁ α₂ : Type*} {D₁ D₂ : ℕ} (e : α₁ ≃ α₂)
    (h : D₁ = D₂) (A : MPTensor α₂ (Fin D₁)) :
    Kraus.reindexPhysical e (cast (congr_arg (fun n ↦ MPTensor α₂ (Fin n)) h) A) =
      cast (congr_arg (fun n ↦ MPTensor α₁ (Fin n)) h) (Kraus.reindexPhysical e A) := by
  subst h
  rfl

/-- Reindexing by a physical-index equivalence preserves transfer-map primitivity. -/
theorem isPrimitive_transferMap_reindexPhysical_equiv {α₁ α₂ β : Type*} [Fintype α₁]
    [Fintype α₂] [Fintype β] [DecidableEq β] (e : α₁ ≃ α₂) (A : MPTensor α₂ β) :
    _root_.IsPrimitive (Kraus.transferMap (Kraus.reindexPhysical e A)) ↔
      _root_.IsPrimitive (Kraus.transferMap A) := by
  rw [Kraus.transferMap_reindexPhysical_equiv e A]

/-- Reindexing by a physical-index equivalence preserves algebraic injectivity. -/
theorem isInjective_reindexPhysical_equiv {α₁ α₂ : Type*} {D : ℕ} (e : α₁ ≃ α₂)
    (A : MPTensor α₂ (Fin D)) :
    Kraus.IsInjective (Kraus.reindexPhysical e A) ↔ Kraus.IsInjective A := by
  have hRange : Set.range (Kraus.reindexPhysical e A) = Set.range A := by
    ext X
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp [Kraus.reindexPhysical]⟩
  simp [Kraus.IsInjective, hRange]

/-- Reindexing by a physical-index equivalence preserves normality: the words of each length
range over the same matrices. -/
theorem isNormal_reindexPhysical_equiv {α₁ α₂ : Type*} {D : ℕ} (e : α₁ ≃ α₂)
    (A : MPTensor α₂ (Fin D)) :
    Kraus.IsNormal (Kraus.reindexPhysical e A) ↔ Kraus.IsNormal A := by
  have hr : ∀ N : ℕ, Set.range (fun σ : Fin N → α₁ ↦
      Kraus.evalWord (Kraus.reindexPhysical e A) (List.ofFn σ)) =
      Set.range (fun σ : Fin N → α₂ ↦ Kraus.evalWord A (List.ofFn σ)) := by
    intro N
    ext X
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨fun i ↦ e (σ i), by
        simp [Kraus.evalWord_reindexPhysical, List.map_ofFn, Function.comp_def]⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨fun i ↦ e.symm (σ i), by
        simp [Kraus.evalWord_reindexPhysical, List.map_ofFn, Function.comp_def]⟩
  simp only [Kraus.IsNormal, Kraus.IsNBlkInjective, Kraus.wordSpan, hr]

/-- Reindexing both tensors by a physical-index equivalence preserves gauge-phase equivalence. -/
theorem gaugePhaseEquiv_reindexPhysical_equiv {α₁ α₂ : Type*} {D : ℕ}
    (e : α₁ ≃ α₂) (A B : MPTensor α₂ (Fin D)) :
    GaugePhaseEquiv (Kraus.reindexPhysical e A) (Kraus.reindexPhysical e B) ↔
      GaugePhaseEquiv A B := by
  constructor
  · rintro ⟨X, ζ, hζ, hXB⟩
    refine ⟨X, ζ, hζ, ?_⟩
    intro i
    simpa [Kraus.reindexPhysical] using hXB (e.symm i)
  · rintro ⟨X, ζ, hζ, hXB⟩
    refine ⟨X, ζ, hζ, ?_⟩
    intro i
    simpa [Kraus.reindexPhysical] using hXB (e i)

/-- Reindexing both tensors by a physical-index equivalence preserves their
closed MPV overlap.

Source context: arXiv:1606.00608, the physical-basis identifications used in
canonical-form blocking at lines 317--345. -/
theorem mpvOverlap_reindexPhysical_equiv {α₁ α₂ : Type*} [Fintype α₁] [Fintype α₂]
    {D₁ D₂ N : ℕ}
    (e : α₁ ≃ α₂) (A : MPTensor α₂ (Fin D₁)) (B : MPTensor α₂ (Fin D₂)) :
    mpvOverlap (Kraus.reindexPhysical e A) (Kraus.reindexPhysical e B) N =
      mpvOverlap A B N := by
  classical
  let E : (Fin N → α₁) ≃ (Fin N → α₂) :=
    Equiv.arrowCongr (Equiv.refl (Fin N)) e
  simp only [mpvOverlap, mpv_reindexPhysical]
  exact Fintype.sum_equiv E
    (fun σ : Fin N → α₁ ↦
      mpv A (fun n ↦ e (σ n)) * star (mpv B (fun n ↦ e (σ n))))
    (fun σ : Fin N → α₂ ↦ mpv A σ * star (mpv B σ))
    (fun σ ↦ by
      have hσ : (fun n ↦ e (σ n)) = E σ := by
        funext n
        rfl
      rw [hσ])

/-- An equivalence of finite configuration spaces transports linear
independence between MPV families whose coefficients correspond under that
equivalence.  The families are the coefficient vectors `σ ↦ mpv (A j) σ` in the `ℓ²` spaces over
the configurations; on the alphabet `Fin d` these are the states `mpvState (A j) N`.

Source context: arXiv:1606.00608, the blocking and physical-basis
identifications used at lines 317--345 and in Appendix C.4, lines 1951--1956. -/
theorem linearIndependent_mpvState_of_configEquiv
    {α₁ α₂ : Type*} [Fintype α₁] [Fintype α₂] {N₁ N₂ : ℕ} {ι : Type*} {dim : ι → ℕ}
    (e : (Fin N₁ → α₁) ≃ (Fin N₂ → α₂))
    (A : (j : ι) → MPTensor α₁ (Fin (dim j)))
    (B : (j : ι) → MPTensor α₂ (Fin (dim j)))
    (hAB : ∀ (j : ι) (σ : Fin N₂ → α₂),
      mpv (A j) (e.symm σ) = mpv (B j) σ)
    (hLI : LinearIndependent ℂ (fun j ↦
      (EuclideanSpace.equiv (ι := Fin N₂ → α₂) (𝕜 := ℂ)).symm fun σ ↦ mpv (B j) σ)) :
    LinearIndependent ℂ (fun j ↦
      (EuclideanSpace.equiv (ι := Fin N₁ → α₁) (𝕜 := ℂ)).symm fun σ ↦ mpv (A j) σ) := by
  let F : EuclideanSpace ℂ (Fin N₁ → α₁) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin N₂ → α₂) :=
    (EuclideanSpace.equiv (Fin N₁ → α₁) ℂ).toLinearEquiv |>.trans
      (LinearEquiv.piCongrLeft' ℂ (fun _ : Fin N₁ → α₁ ↦ ℂ) e) |>.trans
      (EuclideanSpace.equiv (Fin N₂ → α₂) ℂ).symm.toLinearEquiv
  have hF : ∀ j : ι, F ((EuclideanSpace.equiv (ι := Fin N₁ → α₁) (𝕜 := ℂ)).symm
      fun σ ↦ mpv (A j) σ) =
        (EuclideanSpace.equiv (ι := Fin N₂ → α₂) (𝕜 := ℂ)).symm fun σ ↦ mpv (B j) σ := by
    intro j
    ext σ
    exact hAB j σ
  have hMapped : LinearIndependent ℂ
      (fun j ↦ F ((EuclideanSpace.equiv (ι := Fin N₁ → α₁) (𝕜 := ℂ)).symm
        fun σ ↦ mpv (A j) σ)) := by
    simpa only [hF] using hLI
  exact LinearIndependent.of_comp F.toLinearMap hMapped

/-- A physical-index equivalence preserves linear independence of a family
of MPV states at a fixed chain length.

Source context: arXiv:1606.00608, the physical-basis identifications used in
canonical-form blocking at lines 317--345. -/
theorem linearIndependent_mpvState_reindexPhysical_equiv
    {α₁ α₂ : Type*} [Fintype α₁] [Fintype α₂] {r N : ℕ} {dim : Fin r → ℕ}
    (e : α₁ ≃ α₂) (A : (j : Fin r) → MPTensor α₂ (Fin (dim j)))
    (hLI : LinearIndependent ℂ (fun j ↦
      (EuclideanSpace.equiv (ι := Fin N → α₂) (𝕜 := ℂ)).symm fun σ ↦ mpv (A j) σ)) :
    LinearIndependent ℂ (fun j ↦
      (EuclideanSpace.equiv (ι := Fin N → α₁) (𝕜 := ℂ)).symm
        fun σ ↦ mpv (Kraus.reindexPhysical e (A j)) σ) := by
  let E : (Fin N → α₁) ≃ (Fin N → α₂) :=
    Equiv.arrowCongr (Equiv.refl (Fin N)) e
  apply linearIndependent_mpvState_of_configEquiv E
    (fun j ↦ Kraus.reindexPhysical e (A j)) A
  · intro j σ
    rw [mpv_reindexPhysical]
    congr 1
    funext n
    simp [E, Equiv.arrowCongr]
  · exact hLI

end MPSTensor
