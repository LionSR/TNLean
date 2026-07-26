/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.LocalizedKrausCPTP
import TNLean.Channel.Stinespring
import TNLean.Channel.TensorMap
import TNLean.Entropy.MutualInformation

/-!
# Data processing for bipartite mutual information

This file proves that applying a finite-dimensional trace-preserving completely
positive map to one factor of a bipartite density matrix cannot increase its
mutual information.  The proof uses the rectangular Stinespring isometry of a
Kraus family.  Entropy is invariant under this isometry, while discarding its
environment is the tripartite monotonicity theorem obtained from strong
subadditivity.

## Main results

* `IsKrausCPTP.mutualInformation_tensorMapId_le`: mutual-information data
  processing for a local rectangular channel on the first tensor factor.
* `IsKrausCPTP.mutualInformation_idTensorMap_le`: mutual-information data
  processing for a local rectangular channel on the second tensor factor.
* `IsKrausCPTP.mutualInformation_tensorMapBoth_le`: mutual-information data
  processing for independent local rectangular channels on both factors.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 2.2 and
  Chapter 8][Wolf2012QChannels]
* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C, lines 1338--1340
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix Finset

/-- Sandwiching a Hermitian matrix by a rectangular isometry preserves its
von Neumann entropy.  The added zero eigenvalues make no contribution. -/
private theorem vonNeumannEntropy_sandwich_isometry
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (V : Matrix β α ℂ)
    (hV : Vᴴ * V = 1) (ρ : Matrix α α ℂ) (hρ : ρ.IsHermitian) :
    vonNeumannEntropy (V * ρ * Vᴴ)
        (Matrix.isHermitian_mul_mul_conjTranspose V hρ) =
      vonNeumannEntropy ρ hρ := by
  have hABeq : V * ρ * Vᴴ = V * (ρ * Vᴴ) := Matrix.mul_assoc V ρ Vᴴ
  have hAB : (V * (ρ * Vᴴ)).IsHermitian := hABeq ▸
    Matrix.isHermitian_mul_mul_conjTranspose V hρ
  have hBAeq : (ρ * Vᴴ) * V = ρ := by
    rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  have hBA : ((ρ * Vᴴ) * V).IsHermitian := hBAeq.symm ▸ hρ
  calc
    vonNeumannEntropy (V * ρ * Vᴴ)
        (Matrix.isHermitian_mul_mul_conjTranspose V hρ) =
        vonNeumannEntropy (V * (ρ * Vᴴ)) hAB :=
      vonNeumannEntropy_congr hABeq
        (Matrix.isHermitian_mul_mul_conjTranspose V hρ) hAB
    _ = vonNeumannEntropy ((ρ * Vᴴ) * V) hBA :=
      vonNeumannEntropy_mul_comm V (ρ * Vᴴ) hAB hBA
    _ = vonNeumannEntropy ρ hρ :=
      vonNeumannEntropy_congr hBAeq hBA hρ

/-- Tracing the Stinespring environment gives the original local Kraus map,
with the untouched factor moved to the first position. -/
private theorem traceC_stinespring_eq_tensorMapId_swap
    {dIn dOut dR r : ℕ}
    (S : Matrix (Fin dIn) (Fin dIn) ℂ →ₗ[ℂ]
      Matrix (Fin dOut) (Fin dOut) ℂ)
    (A : Fin r → Matrix (Fin dOut) (Fin dIn) ℂ)
    (hA : ∀ X, S X = ∑ i, A i * X * (A i)ᴴ)
    (ρ : Matrix (Fin dIn × Fin dR) (Fin dIn × Fin dR) ℂ) :
    Matrix.traceC_ABC
        ((localStinespringV (δ := Fin dR) (stinespringV A) * ρ *
            (localStinespringV (δ := Fin dR) (stinespringV A))ᴴ).submatrix
          (Equiv.prodComm (Fin dOut × Fin r) (Fin dR)).symm
          (Equiv.prodComm (Fin dOut × Fin r) (Fin dR)).symm) =
      (Matrix.tensorMapId S ρ).submatrix Prod.swap Prod.swap := by
  ext p q
  rcases p with ⟨x, b⟩
  rcases q with ⟨y, c⟩
  change _ = S (Matrix.bipartiteSlice ρ x y) b c
  rw [hA]
  simp only [Matrix.traceC_ABC, Matrix.submatrix_apply,
    localStinespringV, Matrix.kroneckerMap_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.bipartiteSlice_apply, Matrix.sum_apply,
    Matrix.one_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hzy
    simp [Ne.symm hzy]
  · simp

/-- The retained Stinespring output and environment have reduced state
`V ρ_A V†`. -/
private theorem traceA_localStinespring_eq_sandwich
    {dIn dOut dR r : ℕ}
    (V : Matrix (Fin dOut × Fin r) (Fin dIn) ℂ)
    (ρ : Matrix (Fin dIn × Fin dR) (Fin dIn × Fin dR) ℂ) :
    Matrix.traceA_ABC
        ((localStinespringV (δ := Fin dR) V * ρ *
            (localStinespringV (δ := Fin dR) V)ᴴ).submatrix
          (Equiv.prodComm (Fin dOut × Fin r) (Fin dR)).symm
          (Equiv.prodComm (Fin dOut × Fin r) (Fin dR)).symm) =
      V * Matrix.traceRight ρ * Vᴴ := by
  ext p q
  rcases p with ⟨b, i⟩
  rcases q with ⟨c, j⟩
  simp only [Matrix.traceA_ABC, Matrix.submatrix_apply, localStinespringV,
    Matrix.kroneckerMap_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.traceRight_apply, Matrix.one_apply, Fintype.sum_prod_type]
  simp only [Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ,
    ↓reduceIte, RCLike.star_def]
  have hcollapse (a : Fin dIn) (x : Fin dR) :
      (∑ z : Fin dR,
          (∑ a' : Fin dIn, V (b, i) a' * ρ (a', x) (a, z)) *
            (starRingEnd ℂ) (if x = z then V (c, j) a else 0)) =
        (∑ a' : Fin dIn, V (b, i) a' * ρ (a', x) (a, x)) *
          (starRingEnd ℂ) (V (c, j) a) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro z _ hzx
      simp [Ne.symm hzx]
    · simp
  conv_lhs => rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun x _ => hcollapse a x]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]

/-- A trace-preserving map on the first factor leaves the second marginal
unchanged. -/
private theorem traceLeft_tensorMapId
    {dIn dOut dR : ℕ}
    {S : Matrix (Fin dIn) (Fin dIn) ℂ →ₗ[ℂ]
      Matrix (Fin dOut) (Fin dOut) ℂ} (hS : IsKrausCPTP S)
    (ρ : Matrix (Fin dIn × Fin dR) (Fin dIn × Fin dR) ℂ) :
    Matrix.traceLeft (Matrix.tensorMapId S ρ) = Matrix.traceLeft ρ := by
  ext x y
  have htrace := hS.trace_map (Matrix.bipartiteSlice ρ x y)
  simpa only [Matrix.traceLeft_apply, Matrix.tensorMapId_apply, Matrix.trace,
    Matrix.diag, Matrix.bipartiteSlice_apply] using htrace

/-- A completely positive map on the first factor preserves positive
semidefiniteness of a bipartite matrix. -/
theorem IsKrausCPTP.tensorMapId_posSemidef
    {dIn dOut dR : ℕ}
    {S : Matrix (Fin dIn) (Fin dIn) ℂ →ₗ[ℂ]
      Matrix (Fin dOut) (Fin dOut) ℂ} (hS : IsKrausCPTP S)
    {ρ : Matrix (Fin dIn × Fin dR) (Fin dIn × Fin dR) ℂ}
    (hρ : ρ.PosSemidef) : (Matrix.tensorMapId S ρ).PosSemidef :=
  (Matrix.tensorMapIdLM_isKrausCPTP hS).map_posSemidef hρ

/-- Swapping the tensor factors exchanges the right and left partial traces. -/
private theorem traceRight_submatrix_swap
    {dA dB : ℕ}
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    Matrix.traceRight (ρ.submatrix Prod.swap Prod.swap) =
      Matrix.traceLeft ρ := by
  ext i j
  simp only [Matrix.traceRight_apply, Matrix.traceLeft_apply,
    Matrix.submatrix_apply, Prod.swap_prod_mk]

/-- Swapping the tensor factors exchanges the left and right partial traces. -/
private theorem traceLeft_submatrix_swap
    {dA dB : ℕ}
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    Matrix.traceLeft (ρ.submatrix Prod.swap Prod.swap) =
      Matrix.traceRight ρ := by
  ext i j
  simp only [Matrix.traceLeft_apply, Matrix.traceRight_apply,
    Matrix.submatrix_apply, Prod.swap_prod_mk]

/-- Mutual information is independent of the proof of Hermiticity and is
congruent under equality of the underlying bipartite matrices. -/
private theorem mutualInformation_congr
    {dA dB : ℕ}
    {ρ σ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    (h : ρ = σ) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    Entropy.mutualInformation ρ hρ = Entropy.mutualInformation σ hσ := by
  subst σ
  rfl

/-- Bipartite mutual information is invariant under exchanging the two tensor
factors. -/
private theorem mutualInformation_submatrix_swap
    {dA dB : ℕ}
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ : ρ.IsHermitian) :
    Entropy.mutualInformation (ρ.submatrix Prod.swap Prod.swap)
        (hρ.submatrix Prod.swap) =
      Entropy.mutualInformation ρ hρ := by
  have hright := traceRight_submatrix_swap ρ
  have hleft := traceLeft_submatrix_swap ρ
  have eright :
      vonNeumannEntropy
          (Matrix.traceRight (ρ.submatrix Prod.swap Prod.swap))
          (Matrix.traceRight_isHermitian (hρ.submatrix Prod.swap)) =
        vonNeumannEntropy (Matrix.traceLeft ρ)
          (Matrix.traceLeft_isHermitian hρ) :=
    vonNeumannEntropy_congr hright _ _
  have eleft :
      vonNeumannEntropy
          (Matrix.traceLeft (ρ.submatrix Prod.swap Prod.swap))
          (Matrix.traceLeft_isHermitian (hρ.submatrix Prod.swap)) =
        vonNeumannEntropy (Matrix.traceRight ρ)
          (Matrix.traceRight_isHermitian hρ) :=
    vonNeumannEntropy_congr hleft _ _
  have ejoint :
      vonNeumannEntropy (ρ.submatrix Prod.swap Prod.swap)
          (hρ.submatrix Prod.swap) =
        vonNeumannEntropy ρ hρ := by
    let e := Equiv.prodComm (Fin dB) (Fin dA)
    have hswap : ρ.submatrix Prod.swap Prod.swap = ρ.submatrix e e := by
      ext i j
      rfl
    calc
      vonNeumannEntropy (ρ.submatrix Prod.swap Prod.swap)
          (hρ.submatrix Prod.swap) =
          vonNeumannEntropy (ρ.submatrix e e)
            ((Matrix.isHermitian_submatrix_equiv e).mpr hρ) :=
        vonNeumannEntropy_congr hswap _ _
      _ = vonNeumannEntropy ρ hρ :=
        vonNeumannEntropy_submatrix_equiv e ρ hρ
  change
    vonNeumannEntropy
          (Matrix.traceRight (ρ.submatrix Prod.swap Prod.swap))
          (Matrix.traceRight_isHermitian (hρ.submatrix Prod.swap)) +
        vonNeumannEntropy
          (Matrix.traceLeft (ρ.submatrix Prod.swap Prod.swap))
          (Matrix.traceLeft_isHermitian (hρ.submatrix Prod.swap)) -
        vonNeumannEntropy (ρ.submatrix Prod.swap Prod.swap)
          (hρ.submatrix Prod.swap) =
      vonNeumannEntropy (Matrix.traceRight ρ)
          (Matrix.traceRight_isHermitian hρ) +
        vonNeumannEntropy (Matrix.traceLeft ρ)
          (Matrix.traceLeft_isHermitian hρ) -
        vonNeumannEntropy ρ hρ
  rw [eright, eleft, ejoint]
  ring

/-- **Data processing for bipartite mutual information.**  Applying a
rectangular trace-preserving completely positive map to the first factor of a
bipartite density matrix cannot increase its mutual information.

This is the local-channel inequality used in arXiv:1606.00608, Appendix C,
lines 1338--1340. -/
theorem IsKrausCPTP.mutualInformation_tensorMapId_le
    {dIn dOut dR : ℕ}
    {S : Matrix (Fin dIn) (Fin dIn) ℂ →ₗ[ℂ]
      Matrix (Fin dOut) (Fin dOut) ℂ} (hS : IsKrausCPTP S)
    (ρ : Matrix (Fin dIn × Fin dR) (Fin dIn × Fin dR) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    Entropy.mutualInformation (Matrix.tensorMapId S ρ)
        (hS.tensorMapId_posSemidef hρ).isHermitian ≤
      Entropy.mutualInformation ρ hρ.isHermitian := by
  have hS' := hS
  obtain ⟨r, A, hA, hAres⟩ := hS
  let V : Matrix (Fin dOut × Fin r) (Fin dIn) ℂ := stinespringV A
  have hV : Vᴴ * V = 1 := by
    change (stinespringV A)ᴴ * stinespringV A = 1
    rw [stinespringV_conjTranspose_mul, hAres]
  let W : Matrix ((Fin dOut × Fin r) × Fin dR) (Fin dIn × Fin dR) ℂ :=
    localStinespringV V
  have hW : Wᴴ * W = 1 := by
    exact localStinespringV_conjTranspose_mul V hV
  let ω : Matrix ((Fin dOut × Fin r) × Fin dR)
      ((Fin dOut × Fin r) × Fin dR) ℂ := W * ρ * Wᴴ
  let e := Equiv.prodComm (Fin dOut × Fin r) (Fin dR)
  let τ : Matrix (Fin dR × Fin dOut × Fin r)
      (Fin dR × Fin dOut × Fin r) ℂ := ω.submatrix e.symm e.symm
  have hω : ω.PosSemidef := by
    exact hρ.mul_mul_conjTranspose_same W
  have hτ : τ.PosSemidef := by
    exact hω.submatrix e.symm
  have hτtr : τ.trace = 1 := by
    change (ω.submatrix e.symm e.symm).trace = 1
    rw [Matrix.trace_submatrix_equiv]
    change (W * ρ * Wᴴ).trace = 1
    calc
      (W * ρ * Wᴴ).trace = (W * (ρ * Wᴴ)).trace := by
        rw [Matrix.mul_assoc]
      _ = ((ρ * Wᴴ) * W).trace := Matrix.trace_mul_comm W (ρ * Wᴴ)
      _ = 1 := by rw [Matrix.mul_assoc, hW, Matrix.mul_one, htr]
  have hmono := Entropy.mutualInformation_monotone_tripartite τ ⟨hτ, hτtr⟩
  have hC : Matrix.traceC_ABC τ =
      (Matrix.tensorMapId S ρ).submatrix Prod.swap Prod.swap := by
    change Matrix.traceC_ABC
        ((localStinespringV (δ := Fin dR) (stinespringV A) * ρ *
            (localStinespringV (δ := Fin dR) (stinespringV A))ᴴ).submatrix
          (Equiv.prodComm (Fin dOut × Fin r) (Fin dR)).symm
          (Equiv.prodComm (Fin dOut × Fin r) (Fin dR)).symm) = _
    exact traceC_stinespring_eq_tensorMapId_swap S A hA ρ
  have hδ : Matrix.traceRight (Matrix.traceC_ABC τ) = Matrix.traceLeft ρ := by
    calc
      Matrix.traceRight (Matrix.traceC_ABC τ) =
          Matrix.traceRight
            ((Matrix.tensorMapId S ρ).submatrix Prod.swap Prod.swap) :=
        congrArg Matrix.traceRight hC
      _ = Matrix.traceLeft (Matrix.tensorMapId S ρ) :=
        traceRight_submatrix_swap (Matrix.tensorMapId S ρ)
      _ = Matrix.traceLeft ρ := traceLeft_tensorMapId hS' ρ
  have hAτ : Matrix.traceA_ABC τ = V * Matrix.traceRight ρ * Vᴴ := by
    change Matrix.traceA_ABC
        ((localStinespringV (δ := Fin dR) V * ρ *
            (localStinespringV (δ := Fin dR) V)ᴴ).submatrix
          (Equiv.prodComm (Fin dOut × Fin r) (Fin dR)).symm
          (Equiv.prodComm (Fin dOut × Fin r) (Fin dR)).symm) = _
    exact traceA_localStinespring_eq_sandwich V ρ
  have eδ :
      Entropy.vonNeumannEntropy
          (Matrix.traceRight (Matrix.traceC_ABC τ))
          (Matrix.traceRight_isHermitian
            (Matrix.traceC_ABC_isHermitian hτ.isHermitian)) =
        Entropy.vonNeumannEntropy (Matrix.traceLeft ρ)
          (Matrix.traceLeft_isHermitian hρ.isHermitian) :=
    vonNeumannEntropy_congr hδ _ _
  have eA :
      Entropy.vonNeumannEntropy (Matrix.traceA_ABC τ)
          (Matrix.traceA_ABC_isHermitian hτ.isHermitian) =
        Entropy.vonNeumannEntropy (Matrix.traceRight ρ)
          (Matrix.traceRight_isHermitian hρ.isHermitian) := by
    calc
      Entropy.vonNeumannEntropy (Matrix.traceA_ABC τ)
          (Matrix.traceA_ABC_isHermitian hτ.isHermitian) =
          vonNeumannEntropy (V * Matrix.traceRight ρ * Vᴴ)
            (Matrix.isHermitian_mul_mul_conjTranspose V
              (Matrix.traceRight_isHermitian hρ.isHermitian)) :=
        vonNeumannEntropy_congr hAτ _ _
      _ = Entropy.vonNeumannEntropy (Matrix.traceRight ρ)
          (Matrix.traceRight_isHermitian hρ.isHermitian) :=
        vonNeumannEntropy_sandwich_isometry V hV (Matrix.traceRight ρ)
          (Matrix.traceRight_isHermitian hρ.isHermitian)
  have eτ :
      Entropy.vonNeumannEntropy τ hτ.isHermitian =
        Entropy.vonNeumannEntropy ρ hρ.isHermitian := by
    calc
      Entropy.vonNeumannEntropy τ hτ.isHermitian =
          vonNeumannEntropy ω hω.isHermitian := by
        change vonNeumannEntropy (ω.submatrix e.symm e.symm) _ = _
        simpa only using
          vonNeumannEntropy_submatrix_equiv e.symm ω hω.isHermitian
      _ = Entropy.vonNeumannEntropy ρ hρ.isHermitian := by
        change vonNeumannEntropy (W * ρ * Wᴴ) _ = _
        exact vonNeumannEntropy_sandwich_isometry W hW ρ hρ.isHermitian
  have hσ : (Matrix.tensorMapId S ρ).PosSemidef :=
    hS'.tensorMapId_posSemidef hρ
  have hleft :
      Entropy.mutualInformation (Matrix.traceC_ABC τ)
          (Matrix.traceC_ABC_isHermitian hτ.isHermitian) =
        Entropy.mutualInformation (Matrix.tensorMapId S ρ)
          hσ.isHermitian := by
    calc
      Entropy.mutualInformation (Matrix.traceC_ABC τ)
          (Matrix.traceC_ABC_isHermitian hτ.isHermitian) =
          Entropy.mutualInformation
            ((Matrix.tensorMapId S ρ).submatrix Prod.swap Prod.swap)
            (hσ.isHermitian.submatrix Prod.swap) := by
        exact mutualInformation_congr hC _ _
      _ = Entropy.mutualInformation (Matrix.tensorMapId S ρ)
          hσ.isHermitian :=
        mutualInformation_submatrix_swap
          (Matrix.tensorMapId S ρ) hσ.isHermitian
  have hright :
      Entropy.vonNeumannEntropy
            (Matrix.traceRight (Matrix.traceC_ABC τ))
            (Matrix.traceRight_isHermitian
              (Matrix.traceC_ABC_isHermitian hτ.isHermitian)) +
          Entropy.vonNeumannEntropy (Matrix.traceA_ABC τ)
            (Matrix.traceA_ABC_isHermitian hτ.isHermitian) -
          Entropy.vonNeumannEntropy τ hτ.isHermitian =
        Entropy.mutualInformation ρ hρ.isHermitian := by
    change
      Entropy.vonNeumannEntropy
            (Matrix.traceRight (Matrix.traceC_ABC τ))
            (Matrix.traceRight_isHermitian
              (Matrix.traceC_ABC_isHermitian hτ.isHermitian)) +
          Entropy.vonNeumannEntropy (Matrix.traceA_ABC τ)
            (Matrix.traceA_ABC_isHermitian hτ.isHermitian) -
          Entropy.vonNeumannEntropy τ hτ.isHermitian =
        Entropy.vonNeumannEntropy (Matrix.traceRight ρ)
            (Matrix.traceRight_isHermitian hρ.isHermitian) +
          Entropy.vonNeumannEntropy (Matrix.traceLeft ρ)
            (Matrix.traceLeft_isHermitian hρ.isHermitian) -
          Entropy.vonNeumannEntropy ρ hρ.isHermitian
    rw [eδ, eA, eτ]
    ring
  calc
    Entropy.mutualInformation (Matrix.tensorMapId S ρ)
        (hS'.tensorMapId_posSemidef hρ).isHermitian =
        Entropy.mutualInformation (Matrix.tensorMapId S ρ)
          hσ.isHermitian := rfl
    _ = Entropy.mutualInformation (Matrix.traceC_ABC τ)
          (Matrix.traceC_ABC_isHermitian hτ.isHermitian) := hleft.symm
    _ ≤ Entropy.vonNeumannEntropy
            (Matrix.traceRight (Matrix.traceC_ABC τ))
            (Matrix.traceRight_isHermitian
              (Matrix.traceC_ABC_isHermitian hτ.isHermitian)) +
          Entropy.vonNeumannEntropy (Matrix.traceA_ABC τ)
            (Matrix.traceA_ABC_isHermitian hτ.isHermitian) -
          Entropy.vonNeumannEntropy τ hτ.isHermitian := hmono
    _ = Entropy.mutualInformation ρ hρ.isHermitian := hright

namespace Matrix

/-- Apply one linear map to each factor of a bipartite matrix. -/
noncomputable def tensorMapBoth
    {dA dA' dB dB' : ℕ}
    (S : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ]
      Matrix (Fin dA') (Fin dA') ℂ)
    (T : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ]
      Matrix (Fin dB') (Fin dB') ℂ)
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    Matrix (Fin dA' × Fin dB') (Fin dA' × Fin dB') ℂ :=
  idTensorMap T (tensorMapId S ρ)

end Matrix

/-- A completely positive map on the second factor preserves positive
semidefiniteness of a bipartite matrix. -/
theorem IsKrausCPTP.idTensorMap_posSemidef
    {dL dIn dOut : ℕ}
    {S : Matrix (Fin dIn) (Fin dIn) ℂ →ₗ[ℂ]
      Matrix (Fin dOut) (Fin dOut) ℂ} (hS : IsKrausCPTP S)
    {ρ : Matrix (Fin dL × Fin dIn) (Fin dL × Fin dIn) ℂ}
    (hρ : ρ.PosSemidef) : (Matrix.idTensorMap S ρ).PosSemidef := by
  have h := (hS.tensorMapId_posSemidef
    (hρ.submatrix Prod.swap)).submatrix Prod.swap
  have heq : Matrix.idTensorMap S ρ =
      (Matrix.tensorMapId S (ρ.submatrix Prod.swap Prod.swap)).submatrix
        Prod.swap Prod.swap := by
    ext ⟨i, a⟩ ⟨j, b⟩
    rfl
  rw [heq]
  exact h

/-- Applying completely positive maps to both factors preserves positive
semidefiniteness. -/
theorem IsKrausCPTP.tensorMapBoth_posSemidef
    {dA dA' dB dB' : ℕ}
    {S : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ]
      Matrix (Fin dA') (Fin dA') ℂ}
    {T : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ]
      Matrix (Fin dB') (Fin dB') ℂ}
    (hS : IsKrausCPTP S) (hT : IsKrausCPTP T)
    {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    (hρ : ρ.PosSemidef) : (Matrix.tensorMapBoth S T ρ).PosSemidef :=
  hT.idTensorMap_posSemidef (hS.tensorMapId_posSemidef hρ)

/-- Data processing for a rectangular trace-preserving completely positive
map acting on the second factor of a bipartite density matrix. -/
theorem IsKrausCPTP.mutualInformation_idTensorMap_le
    {dL dIn dOut : ℕ}
    {S : Matrix (Fin dIn) (Fin dIn) ℂ →ₗ[ℂ]
      Matrix (Fin dOut) (Fin dOut) ℂ} (hS : IsKrausCPTP S)
    (ρ : Matrix (Fin dL × Fin dIn) (Fin dL × Fin dIn) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    Entropy.mutualInformation (Matrix.idTensorMap S ρ)
        (hS.idTensorMap_posSemidef hρ).isHermitian ≤
      Entropy.mutualInformation ρ hρ.isHermitian := by
  let ρ' := ρ.submatrix Prod.swap Prod.swap
  have hρ' : ρ'.PosSemidef := hρ.submatrix Prod.swap
  have htr' : ρ'.trace = 1 := by
    change (ρ.submatrix Prod.swap Prod.swap).trace = 1
    let e := Equiv.prodComm (Fin dIn) (Fin dL)
    have hswap : ρ.submatrix Prod.swap Prod.swap = ρ.submatrix e e := by
      ext i j
      rfl
    rw [hswap, Matrix.trace_submatrix_equiv, htr]
  have hσ : (Matrix.tensorMapId S ρ').PosSemidef :=
    hS.tensorMapId_posSemidef hρ'
  calc
    Entropy.mutualInformation (Matrix.idTensorMap S ρ)
        (hS.idTensorMap_posSemidef hρ).isHermitian =
        Entropy.mutualInformation
          ((Matrix.tensorMapId S ρ').submatrix Prod.swap Prod.swap)
          (hσ.isHermitian.submatrix Prod.swap) := rfl
    _ = Entropy.mutualInformation (Matrix.tensorMapId S ρ')
          hσ.isHermitian :=
      mutualInformation_submatrix_swap
        (Matrix.tensorMapId S ρ') hσ.isHermitian
    _ ≤ Entropy.mutualInformation ρ' hρ'.isHermitian :=
      hS.mutualInformation_tensorMapId_le ρ' hρ' htr'
    _ = Entropy.mutualInformation ρ hρ.isHermitian :=
      mutualInformation_submatrix_swap ρ hρ.isHermitian

/-- Data processing for independent rectangular trace-preserving completely
positive maps acting on the two factors of a bipartite density matrix.  This
is the two-channel form used in arXiv:1606.00608, Appendix C, lines
1338--1340. -/
theorem IsKrausCPTP.mutualInformation_tensorMapBoth_le
    {dA dA' dB dB' : ℕ}
    {S : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ]
      Matrix (Fin dA') (Fin dA') ℂ}
    {T : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ]
      Matrix (Fin dB') (Fin dB') ℂ}
    (hS : IsKrausCPTP S) (hT : IsKrausCPTP T)
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    Entropy.mutualInformation (Matrix.tensorMapBoth S T ρ)
        (hS.tensorMapBoth_posSemidef hT hρ).isHermitian ≤
      Entropy.mutualInformation ρ hρ.isHermitian := by
  have hσ : (Matrix.tensorMapId S ρ).PosSemidef :=
    hS.tensorMapId_posSemidef hρ
  have hσtr : (Matrix.tensorMapId S ρ).trace = 1 := by
    calc
      (Matrix.tensorMapId S ρ).trace = ρ.trace :=
        (Matrix.tensorMapIdLM_isKrausCPTP hS).trace_map ρ
      _ = 1 := htr
  calc
    Entropy.mutualInformation (Matrix.tensorMapBoth S T ρ)
        (hS.tensorMapBoth_posSemidef hT hρ).isHermitian =
        Entropy.mutualInformation
          (Matrix.idTensorMap T (Matrix.tensorMapId S ρ))
          (hT.idTensorMap_posSemidef hσ).isHermitian := rfl
    _ ≤ Entropy.mutualInformation (Matrix.tensorMapId S ρ)
          hσ.isHermitian :=
      hT.mutualInformation_idTensorMap_le
        (Matrix.tensorMapId S ρ) hσ hσtr
    _ ≤ Entropy.mutualInformation ρ hρ.isHermitian :=
      hS.mutualInformation_tensorMapId_le ρ hρ htr
