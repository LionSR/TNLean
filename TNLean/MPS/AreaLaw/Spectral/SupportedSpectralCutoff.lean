/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Projection.SpectralCutoff
import QICLean.ManyBody.Replica.Symbol.RegionPowerSymbol
import QICLean.ManyBody.Entropy.Filter.Power

/-!
# Spectral cut-offs of operators supported on a region

Step 4 of the proof of Hastings' Lemma 1 projects the localized filtered terms `M_L` and `M_R`
onto their eigenvalues of absolute value at most a threshold `θ`, by the spectral cut-off
`Matrix.spectralCutoff` of QICLean. The cut-off of an operator lifted from a region is the lift
of the regional cut-off, so it is supported on that region, and cut-offs supported on disjoint
regions commute. This places `O_L` left of the cut and `O_R` right of it, and makes them commute.

Source: Hastings, *An area law for one-dimensional quantum systems*, arXiv:0705.2024v4,
appendix, lines 829–842.

## Main statements

* `TNLean.MPS.AreaLaw.Hastings.spectralCutoff_localLift`: the cut-off of a lift is the lift of
  the cut-off.
* `TNLean.MPS.AreaLaw.Hastings.commute_spectralCutoff_localLift_of_disjoint`: cut-offs of
  operators lifted from disjoint regions commute.
* `TNLean.MPS.AreaLaw.Hastings.isSupportedOn_spectralCutoff`,
  `TNLean.MPS.AreaLaw.Hastings.commute_spectralCutoff_of_isSupportedOn`: the same for operators
  given by their supports, through `ManyBody.IsSupportedOn.exists_localLift_isHermitian`.
-/

open Matrix

namespace TNLean.MPS.AreaLaw.Hastings

section Lift

open Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- The local lift as a star-algebra homomorphism. -/
private noncomputable def localLiftStarAlgHom (D : Finset V) :
    Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D) ℂ →⋆ₐ[ℂ]
      Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ where
  toFun := ManyBody.place D
  map_one' := ManyBody.place_one
  map_mul' K K' := ManyBody.place_mul K K'
  map_zero' := ManyBody.place_zero
  map_add' := ManyBody.place_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, ManyBody.place_smul, ManyBody.place_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' K := ManyBody.place_conjTranspose K

/-- **Support of the cut-off.** The spectral cut-off of an operator lifted from a region `D`
is the lift of the regional cut-off; in particular it is supported on `D`.
Hastings, arXiv:0705.2024v4, line 841. -/
theorem spectralCutoff_localLift {D : Finset V}
    {K : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D) ℂ} (hK : K.IsHermitian) (θ : ℝ) :
    spectralCutoff (ManyBody.place D K) θ = ManyBody.place D (spectralCutoff K θ) := by
  have hcont : Continuous (localLiftStarAlgHom (n := n) D) :=
    LinearMap.continuous_of_finiteDimensional (localLiftStarAlgHom (n := n) D).toLinearMap
  have hK' : IsSelfAdjoint (ManyBody.place D K) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, ← ManyBody.place_conjTranspose, hK.eq]
  exact ((localLiftStarAlgHom D).map_cfc (fun t : ℝ ↦ if |t| ≤ θ then 1 else 0) K
    (hf := K.finite_real_spectrum.continuousOn _) (hφ := hcont) (ha := hK.isSelfAdjoint)
    (hφa := hK')).symm

/-- **Commuting cut-offs.** Spectral cut-offs of Hermitian operators lifted from disjoint
regions commute. With `M_L` supported on the sites left of the cut and `M_R` on the sites
right of it, this is the commutation of `O_L` and `O_R` used in Hastings' Lemma 1. -/
theorem commute_spectralCutoff_localLift_of_disjoint {X Y : Finset V} (hXY : Disjoint X Y)
    {K : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) X)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) X) ℂ}
    {K' : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) Y)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) Y) ℂ}
    (hK : K.IsHermitian) (hK' : K'.IsHermitian) (θ θ' : ℝ) :
    Commute (spectralCutoff (ManyBody.place X K) θ) (spectralCutoff (ManyBody.place Y K') θ') := by
  rw [spectralCutoff_localLift hK, spectralCutoff_localLift hK']
  exact commute_localLift_of_disjoint hXY _ _

/-- A Hermitian operator supported on `D` is the local lift of a Hermitian operator on `D`. -/
theorem _root_.ManyBody.IsSupportedOn.exists_localLift_isHermitian {D : Finset V}
    {M : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ} (hM : ManyBody.IsSupportedOn M D)
        (hMh : M.IsHermitian)
    (σ₀ : (∀ v, Fin (n v))) :
    ∃ K : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D) ℂ, K.IsHermitian ∧ M
        = ManyBody.place D K := by
  obtain ⟨K, rfl⟩ := ManyBody.exists_eq_place_of_mem_supportedOperators hM
  refine ⟨K, localLift_injective D σ₀ ?_, rfl⟩
  rw [ManyBody.place_conjTranspose, hMh.eq]

/-- The spectral cut-off of a Hermitian operator supported on `D` is supported on `D`. With
`M_L` supported left of the cut, this places `O_L` there, as Hastings' Lemma 1 requires
(arXiv:0705.2024v4, `law16.tex`, lines 829–842). -/
theorem isSupportedOn_spectralCutoff {D : Finset V}
    {M : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ} (hM : M.IsHermitian)
        (hMD : ManyBody.IsSupportedOn M D)
    (σ₀ : (∀ v, Fin (n v))) (θ : ℝ) : ManyBody.IsSupportedOn (spectralCutoff M θ) D := by
  obtain ⟨K, hK, rfl⟩ := hMD.exists_localLift_isHermitian hM σ₀
  rw [spectralCutoff_localLift hK]
  exact ManyBody.place_mem_supportedOperators _

/-- The spectral cut-offs of Hermitian operators supported on disjoint regions commute: the
commutation of `O_L` and `O_R` in Hastings' Lemma 1 (arXiv:0705.2024v4, `law16.tex`,
lines 829–842), stated for supports. -/
theorem commute_spectralCutoff_of_isSupportedOn {X Y : Finset V} (hXY : Disjoint X Y)
    {M M' : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ} (hM : M.IsHermitian) (hM' : M'.IsHermitian)
    (hMX : ManyBody.IsSupportedOn M X) (hM'Y : ManyBody.IsSupportedOn M' Y) (σ₀ : (∀ v, Fin (n v)))
        (θ θ' : ℝ) :
    Commute (spectralCutoff M θ) (spectralCutoff M' θ') := by
  obtain ⟨K, hK, rfl⟩ := hMX.exists_localLift_isHermitian hM σ₀
  obtain ⟨K', hK', rfl⟩ := hM'Y.exists_localLift_isHermitian hM' σ₀
  exact commute_spectralCutoff_localLift_of_disjoint hXY hK hK' θ θ'

end Lift

end TNLean.MPS.AreaLaw.Hastings
