/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointOpenSectors
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointSwap

/-!
# Actual open-Hamiltonian transport between the mixed endpoints

A bijection of the physical alphabet commutes with taking a local window
and with extending a local operator by the spectator identity. Consequently
the actual nonwrapping Hamiltonian is conjugated by the full-chain physical
reindexing isometry whenever its local interaction is conjugated by the
corresponding local isometry.

The explicit sector exchange therefore identifies the actual second
endpoint open Hamiltonian with the first endpoint of the reversed tensor
pair. No support, kernel, reduction, or spectral-gap hypothesis is used.
Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped BigOperators

namespace MPSTensor

noncomputable section

open ManyBody.Interaction (translationInvariant chainTranslates)

variable {d₁ d₂ R N : ℕ}

/-- Reindexing physical letters commutes with replacement of a cyclic
window, including the unchanged spectator sites. -/
theorem reindex_cyclicCfg
    (e : Fin d₁ ≃ Fin d₂) (i : Fin N) (ω : Cfg d₁ R) (τ : Cfg d₁ N) :
    (fun k => e (cyclicCfg (Fin.pos i) R i ω τ k)) =
      cyclicCfg (Fin.pos i) R i (fun r => e (ω r)) (fun k => e (τ k)) := by
  funext k
  simp only [cyclicCfg]
  split_ifs <;> rfl

/-- The actual cyclic window restriction intertwines physical alphabet
reindexing with its shorter-window counterpart. -/
theorem cyclicRestrictES_physicalReindex
    (e : Fin d₁ ≃ Fin d₂) (i : Fin N) (τ : Cfg d₁ N)
    (v : EuclideanSpace ℂ (Cfg d₂ N)) :
    cyclicRestrictES (Fin.pos i) R i τ (physicalReindexLinearIsometryEquiv e N v) =
      physicalReindexLinearIsometryEquiv e R
        (cyclicRestrictES (Fin.pos i) R i (fun k => e (τ k)) v) := by
  apply PiLp.ext
  intro ω
  change v (fun k => e (cyclicCfg (Fin.pos i) R i ω τ k)) =
    v (cyclicCfg (Fin.pos i) R i (fun r => e (ω r)) (fun k => e (τ k)))
  rw [reindex_cyclicCfg]

/-- If a local matrix is the conjugate of another by the physical reindexing isometry, each
term of its translates on the ring intertwines with the corresponding term of the other under
the full-chain physical reindexing isometry. -/
theorem toEuclideanLin_translationInvariant_term_physicalReindex_apply
    (e : Fin d₁ ≃ Fin d₂)
    {h' : Matrix (Cfg d₁ R) (Cfg d₁ R) ℂ} {h : Matrix (Cfg d₂ R) (Cfg d₂ R) ℂ}
    (hh : Matrix.toEuclideanLin h' =
      (physicalReindexLinearIsometryEquiv e R).toLinearEquiv.conj (Matrix.toEuclideanLin h))
    (i : Fin N) (v : EuclideanSpace ℂ (Cfg d₂ N)) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Matrix.toEuclideanLin ((translationInvariant N h').term i)
        (physicalReindexLinearIsometryEquiv e N v) =
      physicalReindexLinearIsometryEquiv e N
        (Matrix.toEuclideanLin ((translationInvariant N h).term i) v) := by
  have : NeZero N := NeZero.of_pos i.pos
  by_cases hRN : R ≤ N
  · apply PiLp.ext
    intro σ
    rw [toEuclideanLin_translationInvariant_term_apply hRN, hh,
      cyclicRestrictES_physicalReindex]
    change physicalReindexLinearIsometryEquiv e R
        (Matrix.toEuclideanLin h ((physicalReindexLinearIsometryEquiv e R).symm
          (physicalReindexLinearIsometryEquiv e R
            (cyclicRestrictES (Fin.pos i) R i (fun k => e (σ k)) v))))
        (extractWindow R i σ) =
      Matrix.toEuclideanLin ((translationInvariant N h).term i) v (fun k => e (σ k))
    rw [LinearIsometryEquiv.symm_apply_apply,
      physicalReindexLinearIsometryEquiv_apply_apply,
      toEuclideanLin_translationInvariant_term_apply hRN]
    rfl
  · rw [ManyBody.Interaction.translationInvariant_term_of_not_le _ hRN,
      ManyBody.Interaction.translationInvariant_term_of_not_le _ hRN]
    simp

/-- Physical alphabet reindexing conjugates the terms of the translates on the ring. This also
covers interaction lengths exceeding the chain length, where both terms are zero. -/
theorem toEuclideanLin_translationInvariant_term_physicalReindex_conj
    (e : Fin d₁ ≃ Fin d₂)
    {h' : Matrix (Cfg d₁ R) (Cfg d₁ R) ℂ} {h : Matrix (Cfg d₂ R) (Cfg d₂ R) ℂ}
    (hh : Matrix.toEuclideanLin h' =
      (physicalReindexLinearIsometryEquiv e R).toLinearEquiv.conj (Matrix.toEuclideanLin h))
    (i : Fin N) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Matrix.toEuclideanLin ((translationInvariant N h').term i) =
      (physicalReindexLinearIsometryEquiv e N).toLinearEquiv.conj
        (Matrix.toEuclideanLin ((translationInvariant N h).term i)) := by
  have : NeZero N := NeZero.of_pos i.pos
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (physicalReindexLinearIsometryEquiv e N).surjective v
  change Matrix.toEuclideanLin ((translationInvariant N h').term i)
      (physicalReindexLinearIsometryEquiv e N w) =
    physicalReindexLinearIsometryEquiv e N
      (Matrix.toEuclideanLin ((translationInvariant N h).term i)
        ((physicalReindexLinearIsometryEquiv e N).symm
          (physicalReindexLinearIsometryEquiv e N w)))
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact toEuclideanLin_translationInvariant_term_physicalReindex_apply e hh i w

private theorem chainTranslates_zero_term {d : ℕ} (K : Matrix (Cfg d 0) (Cfg d 0) ℂ)
    (i : Fin (N + 1 - 0)) : (chainTranslates 0 N K).term i = K default default • 1 := by
  have hK : K = K default default • 1 := by
    ext a b
    rw [Subsingleton.elim a default, Subsingleton.elim b default]
    simp
  rw [ManyBody.Interaction.chainTranslates, ManyBody.Interaction.ofPlaceAlong_term]
  conv_lhs => rw [hK]
  rw [ManyBody.placeAlong_smul, ManyBody.placeAlong_one]

private theorem apply_default_eq_of_physicalReindex_conj (e : Fin d₁ ≃ Fin d₂)
    {h' : Matrix (Cfg d₁ 0) (Cfg d₁ 0) ℂ} {h : Matrix (Cfg d₂ 0) (Cfg d₂ 0) ℂ}
    (hh : Matrix.toEuclideanLin h' =
      (physicalReindexLinearIsometryEquiv e 0).toLinearEquiv.conj (Matrix.toEuclideanLin h)) :
    h' default default = h default default := by
  have h1 := congrArg (fun T => T (physicalReindexLinearIsometryEquiv e 0
    (WithLp.toLp 2 fun _ => 1)) default) hh
  have h2 : h' default default = h (fun i ↦ e ((default : Cfg d₁ 0) i)) default := by
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      LinearEquiv.conj_apply] using h1
  rwa [Subsingleton.elim (fun i ↦ e ((default : Cfg d₁ 0) i)) default] at h2

/-- The open-chain Hamiltonian of the translates of a local matrix is conjugated by the
full-chain physical isometry when the local matrix is conjugated by the local physical
isometry. This holds for every range, including range zero, where every window carries the
same scalar. -/
theorem toEuclideanLin_hamiltonian_chainTranslates_physicalReindex_conj
    (e : Fin d₁ ≃ Fin d₂)
    {h' : Matrix (Cfg d₁ R) (Cfg d₁ R) ℂ} {h : Matrix (Cfg d₂ R) (Cfg d₂ R) ℂ}
    (hh : Matrix.toEuclideanLin h' =
      (physicalReindexLinearIsometryEquiv e R).toLinearEquiv.conj (Matrix.toEuclideanLin h))
    (N : ℕ) :
    Matrix.toEuclideanLin (chainTranslates R N h').hamiltonian =
      (physicalReindexLinearIsometryEquiv e N).toLinearEquiv.conj
        (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp only [ManyBody.Interaction.hamiltonian, chainTranslates_zero_term,
      apply_default_eq_of_physicalReindex_conj e hh, map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    ext v σ
    simp [LinearEquiv.conj_apply]
  by_cases hRN : R ≤ N
  · have : NeZero N := ⟨by omega⟩
    simp only [ManyBody.Interaction.hamiltonian_chainTranslates_eq_sum_nonwrappingStart _ hR,
      map_sum]
    exact Fintype.sum_congr _ _ fun i ↦
      toEuclideanLin_translationInvariant_term_physicalReindex_conj e hh i.1
  · have : IsEmpty (Fin (N + 1 - R)) := ⟨fun i ↦ hRN (by have := i.isLt; omega)⟩
    simp only [ManyBody.Interaction.hamiltonian, Finset.univ_eq_empty, Finset.sum_empty,
      map_zero]

namespace MPOSymmetry

variable {D₀ D₁ : ℕ}

/-- Every actual second-endpoint local term is the sector-exchanged actual
first-endpoint term for the reversed pair, on the same physical window. -/
theorem mixedEndpoint_localInteraction_one_eq_conj_swap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (i : Fin N) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Matrix.toEuclideanLin ((translationInvariant N
        (mixedEndpointParentInteraction A₀ A₁ 1)).term i) =
      (physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N).toLinearEquiv.conj
        (Matrix.toEuclideanLin ((translationInvariant N
            (mixedEndpointParentInteraction A₁ A₀ 0)).term i)) := by
  exact toEuclideanLin_translationInvariant_term_physicalReindex_conj _
    (mixedEndpointParentInteraction_one_eq_conj_swap A₀ A₁) i

/-- The actual second-endpoint open Hamiltonian is the conjugate of the
actual first-endpoint open Hamiltonian for the reversed tensor pair. -/
theorem mixedEndpoint_hamiltonian_chainTranslates_one_eq_conj_swap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ) :
    Matrix.toEuclideanLin (chainTranslates 2 N
        (mixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian =
      (physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N).toLinearEquiv.conj
        (Matrix.toEuclideanLin (chainTranslates 2 N
            (mixedEndpointParentInteraction A₁ A₀ 0)).hamiltonian) := by
  exact toEuclideanLin_hamiltonian_chainTranslates_physicalReindex_conj _
    (mixedEndpointParentInteraction_one_eq_conj_swap A₀ A₁) N

/-- Pointwise intertwining of the actual endpoint open Hamiltonians under
the concrete sector-exchange isometry. -/
theorem mixedEndpoint_hamiltonian_chainTranslates_one_apply_swap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ)
    (v : EuclideanSpace ℂ (Cfg ((D₁ + D₀) * (D₁ + D₀)) N)) :
    Matrix.toEuclideanLin
        (chainTranslates 2 N (mixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian
        (physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N v) =
      physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N
        (Matrix.toEuclideanLin (chainTranslates 2 N
            (mixedEndpointParentInteraction A₁ A₀ 0)).hamiltonian v) := by
  rw [mixedEndpoint_hamiltonian_chainTranslates_one_eq_conj_swap]
  change physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N
    (Matrix.toEuclideanLin (chainTranslates 2 N
        (mixedEndpointParentInteraction A₁ A₀ 0)).hamiltonian
      ((physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N).symm
        (physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N v))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

end MPOSymmetry

end

end MPSTensor
