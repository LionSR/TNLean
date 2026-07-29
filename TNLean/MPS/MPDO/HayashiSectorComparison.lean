/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.SimpleLocalStructure

/-!
# Hayashi-sector comparison for simple MPDO tensors

This file compares the contraction obtained by applying the inverse tensor at
the two outer sites of a three-site MPO closure with the diagonal sectors of a
chosen Hayashi quantum-Markov decomposition. It formalizes the comparison
immediately preceding the sector factorization in Appendix C.2 of
arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete).

## Main declarations

- `MPOTensor.IsThreeSiteClosure`: closure of three local tensors against a
  virtual tail.
- `MPOTensor.hayashiInverseLeft` and `MPOTensor.hayashiInverseRight`: the two
  outer inverse-map factors in a fixed Hayashi sector.
- `MPOTensor.inverseMap_threeSite_closure_collapse`: the outer inverse-map
  contraction of a closure collapses to the middle physical slice times one
  tail entry.
- `MPOTensor.inverseMap_conj_physicalSlice_expansion`: one tail entry times an
  entry of the conjugated physical slice expands into the outer inverse-map
  contraction of the conjugated state.
- `MPOTensor.inverseMap_hayashi_sector_comparison`: equality between the
  transformed physical slice and the product of the two sector factors.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1343--1438
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

/-! ### Comparison with the injective inverse map -/

/-- A tripartite state is the three-site closure of an MPO tensor against a
virtual tail when its entries are obtained by closing three consecutive local
tensors against that tail.

Source: arXiv:1606.00608, Appendix C.2, equation `sigma3bka`, lines
1343--1348; its use in the inverse-map contraction is at lines 1422--1433. -/
def IsThreeSiteClosure {d D : ℕ} (K : MPOTensor d D)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ) : Prop :=
  ∀ i₁ i₂ i₃ j₁ j₂ j₃,
    ρ (i₁, i₂, i₃) (j₁, j₂, j₃) =
      Matrix.trace (K i₁ j₁ * K i₂ j₂ * K i₃ j₃ * R)

/-- The left outer factor obtained by applying the inverse tensor to the left
density matrix in a Hayashi sector.

Source: arXiv:1606.00608, Appendix C.2, equation `Qketc`, lines 1415--1428. -/
noncomputable def hayashiInverseLeft {d D : ℕ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
    (α β : Fin D) (k : Fin hη.m) (l l' : Fin (hη.dL k)) : ℂ :=
  ∑ i : Fin d, ∑ j : Fin d,
    inverseTensor K hK (finProdFinEquiv (i, j)) α β *
      hη.ρ_left k (i, l) (j, l')

/-- The right outer factor obtained by applying the inverse tensor to the right
density matrix in a Hayashi sector.

Source: arXiv:1606.00608, Appendix C.2, equation `Qketc`, lines 1415--1428. -/
noncomputable def hayashiInverseRight {d D : ℕ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
    (α β : Fin D) (k : Fin hη.m) (r r' : Fin (hη.dR k)) : ℂ :=
  ∑ i : Fin d, ∑ j : Fin d,
    inverseTensor K hK (finProdFinEquiv (i, j)) α β *
      hη.ρ_right k (r, i) (r', j)

/-- Expanding a three-site closure identifies its contraction against the two
outer inverse tensors with the corresponding three-site inverse-map
contraction. This is the contraction used in arXiv:1606.00608, Appendix C.2,
lines 1421--1430. -/
private lemma sum_inverseTensor_threeSiteClosure_eq {d D : ℕ}
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ)
    (hρ : IsThreeSiteClosure K R ρ) (α₁ β₁ α₃ β₃ : Fin D) (i₂ j₂ : Fin d) :
    (∑ i₁ : Fin d, ∑ j₁ : Fin d, ∑ i₃ : Fin d, ∑ j₃ : Fin d,
      inverseTensor K hK (finProdFinEquiv (i₁, j₁)) α₁ β₁ *
        inverseTensor K hK (finProdFinEquiv (i₃, j₃)) α₃ β₃ *
          ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) =
      inverseMapThreeSiteContraction K hK R α₁ β₁ α₃ β₃
        (finProdFinEquiv (i₂, j₂)) := by
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
  simp [MPOTensor.toMPSTensor]

/-- The cyclic permutation of six indices given by
\((a,b,c,d,e,f) \mapsto (c,d,e,f,a,b)\). -/
private def rotateSixEquiv (ι : Type) :
    (ι × ι × ι × ι × ι × ι) ≃ (ι × ι × ι × ι × ι × ι) := {
  toFun := fun ⟨a, b, c, d, e, f⟩ ↦ (c, d, e, f, a, b)
  invFun := fun ⟨a, b, c, d, e, f⟩ ↦ (e, f, a, b, c, d)
  left_inv := by rintro ⟨a, b, c, d, e, f⟩; rfl
  right_inv := by rintro ⟨a, b, c, d, e, f⟩; rfl }

/-- **Collapse of the outer inverse-map contraction of a closure.** Applying
the inverse tensor at the two outer sites of a three-site closure leaves one
entry of the middle physical slice and one entry of the virtual tail:

\[
  \sum_{i_1,j_1,i_3,j_3}
  ({\cal K}^{-1})^{\alpha_1,\beta_1}_{(i_1,j_1)}
  ({\cal K}^{-1})^{\alpha_3,\beta_3}_{(i_3,j_3)}
  \rho_{i_1i_2i_3,j_1j_2j_3}
  = {\cal K}^{i_2j_2}_{\beta_1,\alpha_3}\,R_{\beta_3,\alpha_1}.
\]

**Local fix (tail index):** the tail entry is
$R_{\beta_3,\alpha_1}$, as in `inverseMapThreeSiteContraction_eq`, rather than
the entry printed in the source display.  The correction is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1422--1434. -/
theorem inverseMap_threeSite_closure_collapse {d D : ℕ}
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ)
    (hρ : IsThreeSiteClosure K R ρ) (α₁ β₁ α₃ β₃ : Fin D) (i₂ j₂ : Fin d) :
    ∑ i₁ : Fin d, ∑ j₁ : Fin d, ∑ i₃ : Fin d, ∑ j₃ : Fin d,
      inverseTensor K hK (finProdFinEquiv (i₁, j₁)) α₁ β₁ *
        inverseTensor K hK (finProdFinEquiv (i₃, j₃)) α₃ β₃ *
        ρ (i₁, i₂, i₃) (j₁, j₂, j₃) =
      K i₂ j₂ β₁ α₃ * R β₃ α₁ := by
  calc
    _ = inverseMapThreeSiteContraction K hK R α₁ β₁ α₃ β₃
        (finProdFinEquiv (i₂, j₂)) :=
      sum_inverseTensor_threeSiteClosure_eq K hK R ρ hρ α₁ β₁ α₃ β₃ i₂ j₂
    _ = _ := by
      simpa [MPOTensor.toMPSTensor] using inverseMapThreeSiteContraction_eq
        K hK R α₁ β₁ α₃ β₃ (finProdFinEquiv (i₂, j₂))

/-- **Expansion of the conjugated physical slice against a closure.** For any
matrix $U$ on the middle site, one tail entry times an entry of the conjugated
physical slice expands into the outer inverse-map contraction of the state
conjugated by $U$ on the middle site. The finite-sum reordering needed for
both the diagonal and off-diagonal sector computations reduces to this
identity.

**Local fix (tail index):** the tail entry is
$R_{\beta_3,\alpha_1}$, as in `inverseMapThreeSiteContraction_eq`, rather than
the entry printed in the source display.  The correction is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1422--1434. -/
theorem inverseMap_conj_physicalSlice_expansion {d D : ℕ}
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ)
    (hρ : IsThreeSiteClosure K R ρ) (α₁ β₁ α₃ β₃ : Fin D)
    (U : Matrix (Fin d) (Fin d) ℂ) (b b' : Fin d) :
    R β₃ α₁ * (U * physicalSlice K β₁ α₃ * Uᴴ) b b'
      = ∑ i₁ : Fin d, ∑ j₁ : Fin d, ∑ i₃ : Fin d, ∑ j₃ : Fin d,
          inverseTensor K hK (finProdFinEquiv (i₁, j₁)) α₁ β₁ *
            inverseTensor K hK (finProdFinEquiv (i₃, j₃)) α₃ β₃ *
            (∑ i₂ : Fin d, ∑ j₂ : Fin d,
              U b i₂ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃) *
                (starRingEnd ℂ) (U b' j₂)) := by
  classical
  let A : Fin d → Fin d → ℂ := fun i j ↦
    inverseTensor K hK (finProdFinEquiv (i, j)) α₁ β₁
  let B : Fin d → Fin d → ℂ := fun i j ↦
    inverseTensor K hK (finProdFinEquiv (i, j)) α₃ β₃
  have hcollapse (i₂ j₂ : Fin d) :
      ∑ i₁ : Fin d, ∑ j₁ : Fin d, ∑ i₃ : Fin d, ∑ j₃ : Fin d,
        A i₁ j₁ * B i₃ j₃ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃) =
        K i₂ j₂ β₁ α₃ * R β₃ α₁ :=
    inverseMap_threeSite_closure_collapse K hK R ρ hρ α₁ β₁ α₃ β₃ i₂ j₂
  simp_rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Complex.star_def]
  simp_rw [Finset.sum_mul]
  change R β₃ α₁ * (∑ j₂, ∑ i₂, U b i₂ * physicalSlice K β₁ α₃ i₂ j₂ *
    (starRingEnd ℂ) (U b' j₂)) = _
  rw [Finset.sum_comm]
  let rotate := rotateSixEquiv (Fin d)
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
      simp only [Fintype.sum_prod_type, G]
    have hflat' : (∑ x, G (rotate.symm x)) =
        ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃, ∑ i₂, ∑ j₂,
          U b i₂ * (A i₁ j₁ * B i₃ j₃ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) *
            (starRingEnd ℂ) (U b' j₂) := by
      simp [Fintype.sum_prod_type, G, rotate, rotateSixEquiv]
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

/-- Applying the inverse tensor at the two outer sites of a three-site closure
identifies each diagonal Hayashi sector with a transformed physical slice of
the middle MPO tensor:

\[
 R_{\beta_3,\alpha_1}
 \bigl(U K_{\beta_1,\alpha_3} U^*\bigr)_{k;l,r;l',r'}
 = p_k A^{(k)}_{\alpha_1,\beta_1}(l,l')
   B^{(k)}_{\alpha_3,\beta_3}(r,r').
\]

This is the sectorwise comparison immediately preceding the factorization of
the simple tensor in Appendix C.2. The proof uses only injectivity, the
three-site closure identity, and the state equality in the chosen Hayashi
decomposition. In particular, it does not use the positivity hypotheses of that
decomposition, the saturated area law, or zero correlation length.

**Local fix (tail index):** the tail entry is
$R_{\beta_3,\alpha_1}$, as in `inverseMapThreeSiteContraction_eq`, rather than
the entry printed in the source display.  The correction is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equation `Qketc` and lines 1415--1438. -/
theorem inverseMap_hayashi_sector_comparison {d D : ℕ}
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ)
    (hρ : IsThreeSiteClosure K R ρ) (hη : EtaStructure ρ)
    (α₁ β₁ α₃ β₃ : Fin D) (k : Fin hη.m)
    (l l' : Fin (hη.dL k)) (r r' : Fin (hη.dR k)) :
    R β₃ α₁ * Matrix.reindex hη.decompB hη.decompB
        ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β₁ α₃ *
          (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
        ⟨k, (l, r)⟩ ⟨k, (l', r')⟩ =
      (hη.p k : ℂ) * hayashiInverseLeft K hK hη α₁ β₁ k l l' *
        hayashiInverseRight K hK hη α₃ β₃ k r r' := by
  classical
  let b : Fin d := hη.decompB.symm ⟨k, (l, r)⟩
  let b' : Fin d := hη.decompB.symm ⟨k, (l', r')⟩
  let U : Matrix (Fin d) (Fin d) ℂ := hη.U_B
  have hsector (i₁ j₁ i₃ j₃ : Fin d) :
      ∑ i₂ : Fin d, ∑ j₂ : Fin d,
        U b i₂ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃) *
          (starRingEnd ℂ) (U b' j₂) =
        (hη.p k : ℂ) * hη.ρ_left k (i₁, l) (j₁, l') *
          hη.ρ_right k (r, i₃) (r', j₃) := by
    have hs := congrFun (congrFun hη.h_state
      (i₁, (⟨k, (l, r)⟩, i₃))) (j₁, (⟨k, (l', r')⟩, j₃))
    rw [Matrix.reindex_apply, Matrix.submatrix_apply] at hs
    have hleft : (HayashiMarkov.abcEquiv hη.decompB).symm
        (i₁, (⟨k, (l, r)⟩, i₃)) = (i₁, b, i₃) := by
      simp [HayashiMarkov.abcEquiv, b]
    have hright : (HayashiMarkov.abcEquiv hη.decompB).symm
        (j₁, (⟨k, (l', r')⟩, j₃)) = (j₁, b', j₃) := by
      simp [HayashiMarkov.abcEquiv, b']
    rw [hleft, hright] at hs
    rw [HayashiMarkov.liftB_conj_apply] at hs
    rw [HayashiMarkov.blockState_apply] at hs
    simpa [b, b', U] using hs
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  change R β₃ α₁ * (U * physicalSlice K β₁ α₃ * Uᴴ) b b' = _
  rw [inverseMap_conj_physicalSlice_expansion K hK R ρ hρ α₁ β₁ α₃ β₃ U b b']
  simp_rw [hsector]
  simp only [hayashiInverseLeft, hayashiInverseRight]
  rw [show (hη.p k : ℂ) *
      (∑ i₁, ∑ j₁, inverseTensor K hK (finProdFinEquiv (i₁, j₁)) α₁ β₁ *
        hη.ρ_left k (i₁, l) (j₁, l')) *
      (∑ i₃, ∑ j₃, inverseTensor K hK (finProdFinEquiv (i₃, j₃)) α₃ β₃ *
        hη.ρ_right k (r, i₃) (r', j₃)) =
    (hη.p k : ℂ) *
      (∑ i₃, ∑ j₃, inverseTensor K hK (finProdFinEquiv (i₃, j₃)) α₃ β₃ *
        hη.ρ_right k (r, i₃) (r', j₃)) *
      (∑ i₁, ∑ j₁, inverseTensor K hK (finProdFinEquiv (i₁, j₁)) α₁ β₁ *
        hη.ρ_left k (i₁, l) (j₁, l')) by ring]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j₁ _ => ?_
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i₃ _ => Finset.sum_congr rfl fun j₃ _ => ?_
  ring

end MPOTensor
