/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.HayashiSectorComparison

/-!
# Sector factorization of an injective simple MPDO tensor

This file derives the sector factorization of an injective simple MPO tensor
from the sectorwise inverse-map comparison, following Appendix C.2 of
arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete), Lemma `propSN`.

The sectorwise comparison `MPOTensor.inverseMap_hayashi_sector_comparison`
computes the diagonal Hayashi sectors of the transformed physical slice. Here
we complete the passage to equation `formK` (lines 1435--1448): the
off-diagonal sectors vanish, and once outer indices with a nonzero tail entry
are selected, the transformed physical slice splits as a direct sum over
sectors of tensor products $l_k \otimes r_k$.

## Main declarations

- `MPOTensor.isThreeSiteClosure_reducedBlockState`: the three-site marginal of
  the normalized four-site chain is a three-site closure against the
  normalized fourth-site tail.
- `MPOTensor.inverseMap_hayashi_sector_offdiagonal`: the tail entry times any
  off-diagonal Hayashi sector of the transformed physical slice vanishes.
- `MPOTensor.sectorTensorL` and `MPOTensor.sectorTensorR`: the sector tensors
  $l_k$ and $r_k$ of equation `formK`.
- `MPOTensor.physicalSlice_sector_factorization`: equation `formK` — the
  transformed physical slice is the direct sum over sectors of
  $l_k \otimes r_k$ once a nonzero tail entry is selected.
- `MPOTensor.exists_physicalSlice_sector_factorization`: the existence form of
  equation `formK` for a closure against the normalized fourth-site tail,
  with the nonzero tail entry supplied by the nonzero four-site trace.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Lemma C.4 (`propSN`), lines 1407--1448
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- **The four-site marginal is a three-site closure.** Carried onto the
tripartite site index, the three-site marginal of the normalized four-site
chain is the three-site closure of ${\cal K}$ against the normalized
fourth-site tail $R_4$.

Source: arXiv:1606.00608, Appendix C.2, lines 1343--1348, with the
normalization convention at lines 792--793. -/
theorem isThreeSiteClosure_reducedBlockState (K : MPOTensor d D) :
    IsThreeSiteClosure K (normalizedFourSiteTail K)
      ((K.reducedBlockState 4 3 (by omega)).submatrix
        (fun p : Fin d × Fin d × Fin d => ![p.1, p.2.1, p.2.2])
        (fun p : Fin d × Fin d × Fin d => ![p.1, p.2.1, p.2.2])) := by
  intro i₁ i₂ i₃ j₁ j₂ j₃
  rw [Matrix.submatrix_apply, reducedBlockState_four_three_apply]
  simp [List.ofFn_succ, Matrix.mul_assoc]

/-- **Vanishing of the off-diagonal Hayashi sectors.** In the basis selected
by the middle-site unitary, the tail entry times every off-diagonal sector of
the transformed physical slice vanishes:

\[
  R_{\beta_3,\alpha_1}
  \bigl(U_B\,\kappa_{\beta_1,\alpha_3}\,U_B^\dagger\bigr)_{(k;l,r),(k';l',r')}
  = 0 \qquad (k \ne k').
\]

Together with the diagonal identity
`MPOTensor.inverseMap_hayashi_sector_comparison`, this gives the direct-sum
structure of equation `formK`: the direct sum is inherited from the splitting
of the middle site.

Source: arXiv:1606.00608, Appendix C.2, lines 1422--1448. -/
theorem inverseMap_hayashi_sector_offdiagonal
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ)
    (hρ : IsThreeSiteClosure K R ρ) (hη : EtaStructure ρ)
    (α₁ β₁ α₃ β₃ : Fin D) {k k' : Fin hη.m} (hkk' : k ≠ k')
    (l : Fin (hη.dL k)) (r : Fin (hη.dR k))
    (l' : Fin (hη.dL k')) (r' : Fin (hη.dR k')) :
    R β₃ α₁ * Matrix.reindex hη.decompB hη.decompB
        ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β₁ α₃ *
          (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
        ⟨k, (l, r)⟩ ⟨k', (l', r')⟩ = 0 := by
  classical
  let b : Fin d := hη.decompB.symm ⟨k, (l, r)⟩
  let b' : Fin d := hη.decompB.symm ⟨k', (l', r')⟩
  let U : Matrix (Fin d) (Fin d) ℂ := hη.U_B
  let A : Fin d → Fin d → ℂ := fun i j ↦
    inverseTensor K hK (finProdFinEquiv (i, j)) α₁ β₁
  let B : Fin d → Fin d → ℂ := fun i j ↦
    inverseTensor K hK (finProdFinEquiv (i, j)) α₃ β₃
  have hsector (i₁ j₁ i₃ j₃ : Fin d) :
      ∑ i₂ : Fin d, ∑ j₂ : Fin d,
        U b i₂ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃) *
          (starRingEnd ℂ) (U b' j₂) = 0 := by
    have hs := congrFun (congrFun hη.h_state
      (i₁, (⟨k, (l, r)⟩, i₃))) (j₁, (⟨k', (l', r')⟩, j₃))
    rw [Matrix.reindex_apply, Matrix.submatrix_apply] at hs
    have hleft : (HayashiMarkov.abcEquiv hη.decompB).symm
        (i₁, (⟨k, (l, r)⟩, i₃)) = (i₁, b, i₃) := by
      simp [HayashiMarkov.abcEquiv, b]
    have hright : (HayashiMarkov.abcEquiv hη.decompB).symm
        (j₁, (⟨k', (l', r')⟩, j₃)) = (j₁, b', j₃) := by
      simp [HayashiMarkov.abcEquiv, b']
    rw [hleft, hright] at hs
    rw [HayashiMarkov.liftB_conj_apply] at hs
    rw [HayashiMarkov.blockState_apply, dif_neg hkk'] at hs
    simpa [U] using hs
  have hcollapse (i₂ j₂ : Fin d) :
      ∑ i₁ : Fin d, ∑ j₁ : Fin d, ∑ i₃ : Fin d, ∑ j₃ : Fin d,
        A i₁ j₁ * B i₃ j₃ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃) =
        K i₂ j₂ β₁ α₃ * R β₃ α₁ := by
    rw [show (∑ i₁ : Fin d, ∑ j₁ : Fin d, ∑ i₃ : Fin d, ∑ j₃ : Fin d,
        A i₁ j₁ * B i₃ j₃ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) =
      inverseMapThreeSiteContraction K hK R α₁ β₁ α₃ β₃
        (finProdFinEquiv (i₂, j₂)) from by
          rw [inverseMapThreeSiteContraction]
          simp_rw [← Equiv.sum_comp finProdFinEquiv
            (fun p ↦ ∑ p₃,
              inverseTensor K hK p α₁ β₁ * inverseTensor K hK p₃ α₃ β₃ *
                Matrix.trace (K.toMPSTensor p * K.toMPSTensor (finProdFinEquiv (i₂, j₂)) *
                  K.toMPSTensor p₃ * R))]
          simp_rw [← Equiv.sum_comp finProdFinEquiv
            (fun p ↦
              inverseTensor K hK (finProdFinEquiv _) α₁ β₁ *
                inverseTensor K hK p α₃ β₃ *
                Matrix.trace (K.toMPSTensor (finProdFinEquiv _) *
                  K.toMPSTensor (finProdFinEquiv (i₂, j₂)) * K.toMPSTensor p * R))]
          simp_rw [Fintype.sum_prod_type]
          congr 1 with i₁
          congr 1 with j₁
          congr 1 with i₃
          congr 1 with j₃
          rw [hρ i₁ i₂ i₃ j₁ j₂ j₃]
          simp [A, B, MPOTensor.toMPSTensor]]
    simpa [MPOTensor.toMPSTensor] using inverseMapThreeSiteContraction_eq K hK R
      α₁ β₁ α₃ β₃ (finProdFinEquiv (i₂, j₂))
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  simp_rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Complex.star_def]
  simp_rw [Finset.sum_mul]
  change R β₃ α₁ * (∑ j₂, ∑ i₂, U b i₂ * physicalSlice K β₁ α₃ i₂ j₂ *
    (starRingEnd ℂ) (U b' j₂)) = 0
  rw [Finset.sum_comm]
  let rotate :
      (Fin d × Fin d × Fin d × Fin d × Fin d × Fin d) ≃
        (Fin d × Fin d × Fin d × Fin d × Fin d × Fin d) := {
    toFun := fun x ↦ (x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.1, x.2.1)
    invFun := fun x ↦ (x.2.2.2.2.1, x.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1)
    left_inv := by intro x; rcases x with ⟨a, b, c, e, f, g⟩; rfl
    right_inv := by intro x; rcases x with ⟨a, b, c, e, f, g⟩; rfl }
  let G : Fin d × Fin d × Fin d × Fin d × Fin d × Fin d → ℂ := fun x ↦
    U b x.1 * (A x.2.2.1 x.2.2.2.1 * B x.2.2.2.2.1 x.2.2.2.2.2 *
      ρ (x.2.2.1, x.1, x.2.2.2.2.1) (x.2.2.2.1, x.2.1, x.2.2.2.2.2)) *
        (starRingEnd ℂ) (U b' x.2.1)
  have hperm :
      (∑ i₂, ∑ j₂, ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃,
        U b i₂ * (A i₁ j₁ * B i₃ j₃ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) *
          (starRingEnd ℂ) (U b' j₂)) =
      ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃, ∑ i₂, ∑ j₂,
        U b i₂ * (A i₁ j₁ * B i₃ j₃ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) *
          (starRingEnd ℂ) (U b' j₂) := by
    have hflat : (∑ x, G x) =
        ∑ i₂, ∑ j₂, ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃,
          U b i₂ * (A i₁ j₁ * B i₃ j₃ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) *
            (starRingEnd ℂ) (U b' j₂) := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      rfl
    have hflat' : (∑ x, G (rotate.symm x)) =
        ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃, ∑ i₂, ∑ j₂,
          U b i₂ * (A i₁ j₁ * B i₃ j₃ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) *
            (starRingEnd ℂ) (U b' j₂) := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      rfl
    rw [← hflat, ← hflat']
    exact (Equiv.sum_comp rotate.symm G).symm
  calc
    R β₃ α₁ * (∑ i₂, ∑ j₂, U b i₂ * physicalSlice K β₁ α₃ i₂ j₂ *
        (starRingEnd ℂ) (U b' j₂)) =
      ∑ i₂, ∑ j₂, U b i₂ *
        (∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃,
          A i₁ j₁ * B i₃ j₃ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) *
        (starRingEnd ℂ) (U b' j₂) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i₂ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j₂ _ => ?_
          calc
            R β₃ α₁ * (U b i₂ * physicalSlice K β₁ α₃ i₂ j₂ *
                (starRingEnd ℂ) (U b' j₂)) =
              U b i₂ * (K i₂ j₂ β₁ α₃ * R β₃ α₁) *
                (starRingEnd ℂ) (U b' j₂) := by simp [physicalSlice]; ring
            _ = _ := by rw [← hcollapse]
    _ = ∑ i₂, ∑ j₂, ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃,
        U b i₂ * (A i₁ j₁ * B i₃ j₃ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) *
          (starRingEnd ℂ) (U b' j₂) := by
      refine Finset.sum_congr rfl fun i₂ _ => Finset.sum_congr rfl fun j₂ _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i₁ _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j₁ _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i₃ _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃, ∑ i₂, ∑ j₂,
        U b i₂ * (A i₁ j₁ * B i₃ j₃ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) *
          (starRingEnd ℂ) (U b' j₂) := hperm
    _ = ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃, A i₁ j₁ * B i₃ j₃ *
        (∑ i₂, ∑ j₂, U b i₂ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃) *
          (starRingEnd ℂ) (U b' j₂)) := by
      refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun j₁ _ =>
        Finset.sum_congr rfl fun i₃ _ => Finset.sum_congr rfl fun j₃ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i₂ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j₂ _ => ?_
      ring
    _ = 0 := by
      simp_rw [hsector]
      simp

/-- The sector tensor $l_k$ of equation `formK`: for each left virtual index,
the left Hayashi inverse factor at the selected outer indices, weighted by the
sector weight and the inverse of the selected tail entry. The tail entry and
its inverse are attached to $l_k$; the source leaves this distribution between
$l_k$ and $r_k$ unspecified.

Source: arXiv:1606.00608, Appendix C.2, lines 1435--1448. -/
noncomputable def sectorTensorL
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
    (R : Matrix (Fin D) (Fin D) ℂ) (α₁ β₃ : Fin D) (k : Fin hη.m)
    (β₁ : Fin D) : Matrix (Fin (hη.dL k)) (Fin (hη.dL k)) ℂ :=
  Matrix.of fun l l' =>
    (R β₃ α₁)⁻¹ * (hη.p k : ℂ) * hayashiInverseLeft K hK hη α₁ β₁ k l l'

/-- The sector tensor $r_k$ of equation `formK`: for each right virtual index,
the right Hayashi inverse factor at the selected outer indices.

Source: arXiv:1606.00608, Appendix C.2, lines 1435--1448. -/
noncomputable def sectorTensorR
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
    (β₃ : Fin D) (k : Fin hη.m) (α₃ : Fin D) :
    Matrix (Fin (hη.dR k)) (Fin (hη.dR k)) ℂ :=
  Matrix.of fun r r' => hayashiInverseRight K hK hη α₃ β₃ k r r'

/-- **Equation `formK`: the sector factorization of an injective simple
tensor.** Once outer indices with a nonzero tail entry are selected, the
transformed physical slice splits as a direct sum over Hayashi sectors of
tensor products: for all virtual indices $\beta_1$ and $\alpha_3$,

\[
  U_B\,\kappa_{\beta_1,\alpha_3}\,U_B^\dagger
  = \bigoplus_k\,(l_k)_{\beta_1} \otimes (r_k)_{\alpha_3}.
\]

The direct sum refers to the physical indices and is inherited from the
splitting of the middle site. The diagonal sectors are supplied by
`MPOTensor.inverseMap_hayashi_sector_comparison` and the off-diagonal sectors
vanish by `MPOTensor.inverseMap_hayashi_sector_offdiagonal`; dividing by the
selected tail entry yields the factorization.

Source: arXiv:1606.00608, Appendix C.2, lines 1429--1448. -/
theorem physicalSlice_sector_factorization
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ)
    (hρ : IsThreeSiteClosure K R ρ) (hη : EtaStructure ρ)
    {α₁ β₃ : Fin D} (hm : R β₃ α₁ ≠ 0) (β₁ α₃ : Fin D) :
    Matrix.reindex hη.decompB hη.decompB
        ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β₁ α₃ *
          (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
      = Matrix.blockDiagonal' fun k =>
          Matrix.kroneckerMap (· * ·)
            (sectorTensorL K hK hη R α₁ β₃ k β₁)
            (sectorTensorR K hK hη β₃ k α₃) := by
  classical
  ext s t
  obtain ⟨k, l, r⟩ := s
  obtain ⟨k', l', r'⟩ := t
  by_cases hkk' : k = k'
  · subst hkk'
    rw [Matrix.blockDiagonal'_apply_eq]
    have h := inverseMap_hayashi_sector_comparison K hK R ρ hρ hη
      α₁ β₁ α₃ β₃ k l l' r r'
    have h2 : Matrix.reindex hη.decompB hη.decompB
        ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β₁ α₃ *
          (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
        ⟨k, (l, r)⟩ ⟨k, (l', r')⟩
        = (R β₃ α₁)⁻¹ *
            ((hη.p k : ℂ) * hayashiInverseLeft K hK hη α₁ β₁ k l l' *
              hayashiInverseRight K hK hη α₃ β₃ k r r') := by
      rw [← h, inv_mul_cancel_left₀ hm]
    rw [h2]
    simp only [Matrix.kroneckerMap_apply, sectorTensorL, sectorTensorR,
      Matrix.of_apply]
    ring
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkk']
    have h0 := inverseMap_hayashi_sector_offdiagonal K hK R ρ hρ hη
      α₁ β₁ α₃ β₃ hkk' l r l' r'
    exact (mul_eq_zero.mp h0).resolve_left hm

/-- **Existence form of equation `formK`.** For a three-site closure against
the normalized fourth-site tail, a nonzero four-site trace supplies the outer
indices, and the sector tensors $l_k$ and $r_k$ factorize every transformed
physical slice:

\[
  U_B\,\kappa_{\beta_1,\alpha_3}\,U_B^\dagger
  = \bigoplus_k\,(l_k)_{\beta_1} \otimes (r_k)_{\alpha_3}
  \qquad\text{for all } \beta_1,\alpha_3.
\]

This is the statement of Lemma `propSN` up to equation `formK` for the
four-site normalized chain; the neighboring operators $\eta_{k,h}$ and their
all-length identity are the subsequent steps.

Source: arXiv:1606.00608, Appendix C.2, lines 1407--1448. -/
theorem exists_physicalSlice_sector_factorization
    (K : MPOTensor d D) (hK : K.IsInjective)
    (htrace : (mpo K 4).trace ≠ 0)
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (hρ : IsThreeSiteClosure K (normalizedFourSiteTail K) ρ)
    (hη : EtaStructure ρ) :
    ∃ (l : (k : Fin hη.m) → Fin D →
        Matrix (Fin (hη.dL k)) (Fin (hη.dL k)) ℂ)
      (r : (k : Fin hη.m) → Fin D →
        Matrix (Fin (hη.dR k)) (Fin (hη.dR k)) ℂ),
      ∀ β₁ α₃ : Fin D,
        Matrix.reindex hη.decompB hη.decompB
            ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β₁ α₃ *
              (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
          = Matrix.blockDiagonal' fun k =>
              Matrix.kroneckerMap (· * ·) (l k β₁) (r k α₃) := by
  obtain ⟨β₃, α₁, hm⟩ := exists_normalizedFourSiteTail_entry_ne_zero K htrace
  exact ⟨fun k β₁ => sectorTensorL K hK hη (normalizedFourSiteTail K) α₁ β₃ k β₁,
    fun k α₃ => sectorTensorR K hK hη β₃ k α₃,
    fun β₁ α₃ => physicalSlice_sector_factorization K hK
      (normalizedFourSiteTail K) ρ hρ hη hm β₁ α₃⟩

end MPOTensor
