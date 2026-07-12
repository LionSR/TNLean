/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.HayashiSectorComparison

/-!
# Sector factorization of an injective simple MPDO tensor

This file derives the sector factorization of an injective simple MPO tensor
from the sectorwise inverse-map comparison, following Appendix C.2 of
arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete), Lemma C.4.

The sectorwise comparison computes the diagonal Hayashi sectors of the
transformed physical slice. Here we complete the passage to the factorization
identity at lines 1435--1448:
the off-diagonal sectors vanish, and once outer indices with a nonzero tail entry
are selected, the transformed physical slice splits as a direct sum over
sectors of tensor products $l_k \otimes r_k$.

## Main declarations

- `MPOTensor.isThreeSiteClosure_reducedBlockState`: the three-site marginal of
  the normalized four-site chain is a three-site closure against the
  normalized fourth-site tail.
- `MPOTensor.inverseMap_hayashi_sector_offdiagonal`: the tail entry times any
  off-diagonal Hayashi sector of the transformed physical slice vanishes.
- `MPOTensor.sectorTensorL` and `MPOTensor.sectorTensorR`: the sector tensors
  $l_k$ and $r_k$ of the factorization at lines 1435--1448.
- `MPOTensor.physicalSlice_sector_factorization`: the sector factorization —
  the transformed physical slice is the direct sum over sectors of
  $l_k \otimes r_k$ once a nonzero tail entry is selected.
- `MPOTensor.exists_physicalSlice_sector_factorization`: the existence form
  of the sector factorization for a closure against the normalized
  fourth-site tail, with the nonzero tail entry supplied by the nonzero four-site trace.
- `MPOTensor.sectorEta`: the neighboring operators $\eta_{k,h}$, contracting
  the right sector tensor of one site with the left sector tensor of the next
  site over the shared virtual bond.
- `MPOTensor.physicalSlice_neighboring_contraction`: the bond contraction of
  two neighboring factorized slices exhibits $\eta_{k,h}$ between the outer
  sector tensors.
- `MPOTensor.closedSectorL` and `MPOTensor.closedSectorR`: the closed sector
  tensors $|l_k)$ and $(r_k|$ obtained by tracing the physical legs.
- `MPOTensor.trace_sectorEta`: the trace identity
  $T_{k,h} = \operatorname{tr}(\eta_{k,h}) = (r_k|l_h)$.
- `MPOTensor.ExplicitEtaOperators.ofSectorTensors`: the neighboring operator
  family forming explicit $\eta$-data under the positivity hypothesis.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Lemma C.4, lines 1407--1481
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
by the middle-site unitary, for all $k \ne k'$, the tail entry times every
off-diagonal sector of the transformed physical slice vanishes:

\[
  R_{\beta_3,\alpha_1}
  \bigl(U_B\,\kappa_{\beta_1,\alpha_3}\,U_B^\dagger\bigr)_{(k;l,r),(k';l',r')}
  = 0.
\]

Together with the diagonal identity
`MPOTensor.inverseMap_hayashi_sector_comparison`, this gives the direct-sum
structure of the sector factorization: the direct sum is inherited from the
splitting of the middle site.

**Local fix (tail index):** the tail entry is
$R_{\beta_3,\alpha_1}$, as in `inverseMapThreeSiteContraction_eq`, rather than
the entry printed in the source display.  The correction is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

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
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  change R β₃ α₁ * (U * physicalSlice K β₁ α₃ * Uᴴ) b b' = 0
  rw [inverseMap_conj_physicalSlice_expansion K hK R ρ hρ α₁ β₁ α₃ β₃ U b b']
  simp_rw [hsector]
  simp

/-- The sector tensor $l_k$ of the sector factorization: for each left
virtual index, the left Hayashi inverse factor at the selected outer indices, weighted
by the
sector weight and the inverse of the selected tail entry. The tail entry and
its inverse are attached to $l_k$; the source leaves this distribution between
$l_k$ and $r_k$ unspecified.

**Local fix (tail index):** the selected tail entry is
$R_{\beta_3,\alpha_1}$, as in `inverseMapThreeSiteContraction_eq`, rather than
the entry printed in the source display.  The correction is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1435--1448. -/
noncomputable def sectorTensorL
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
    (R : Matrix (Fin D) (Fin D) ℂ) (α₁ β₃ : Fin D) (k : Fin hη.m)
    (β₁ : Fin D) : Matrix (Fin (hη.dL k)) (Fin (hη.dL k)) ℂ :=
  Matrix.of fun l l' =>
    (R β₃ α₁)⁻¹ * (hη.p k : ℂ) * hayashiInverseLeft K hK hη α₁ β₁ k l l'

/-- The sector tensor $r_k$ of the sector factorization: for each right
virtual index, the right Hayashi inverse factor at the selected outer
indices.

Source: arXiv:1606.00608, Appendix C.2, lines 1435--1448. -/
noncomputable def sectorTensorR
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
    (β₃ : Fin D) (k : Fin hη.m) (α₃ : Fin D) :
    Matrix (Fin (hη.dR k)) (Fin (hη.dR k)) ℂ :=
  Matrix.of fun r r' => hayashiInverseRight K hK hη α₃ β₃ k r r'

/-- **The sector factorization of an injective simple tensor.** Once
outer indices with a nonzero tail entry are selected, the transformed
physical slice splits as a direct sum over Hayashi sectors of
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

**Local fix (tail index):** the nonzero entry is selected at the pair
$(\beta_3,\alpha_1)$, as in `inverseMapThreeSiteContraction_eq`, rather than
at the pair printed in the source display.  The correction is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

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

/-- **Existence form of the sector factorization.** For a three-site closure
against the normalized fourth-site tail, a nonzero four-site trace supplies
the outer
indices, and the sector tensors $l_k$ and $r_k$ factorize every transformed
physical slice. For all virtual indices $\beta_1,\alpha_3$,

\[
  U_B\,\kappa_{\beta_1,\alpha_3}\,U_B^\dagger
  = \bigoplus_k\,(l_k)_{\beta_1} \otimes (r_k)_{\alpha_3}.
\]

This is the statement of Lemma C.4 up to the factorization at lines
1435--1448 for the four-site normalized chain; the neighboring operators
$\eta_{k,h}$ and their all-length identity are the subsequent steps.

**Local fix (tail index):** the selected nonzero entry of the normalized tail
is $(R_4)_{\beta_3,\alpha_1}$, rather than the entry printed in the source
display. The correction is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

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

/-! ### The neighboring operators $\eta_{k,h}$ -/

/-- **The neighboring operator $\eta_{k,h}$.** The right sector tensor $r_k$
of one site and the left sector tensor $l_h$ of the following site are
contracted over the virtual bond they share:

\[
  \eta_{k,h} = \sum_{\gamma}\,(r_k)_{\gamma} \otimes (l_h)_{\gamma}.
\]

It acts on the neighboring bond space $B_k^R \otimes B_h^L$, the row and
column index type of `MPOTensor.etaOperators`. The scalar
$R_{\beta_3,\alpha_1}^{-1}\,p_h$ attached to the left sector tensor in
`MPOTensor.sectorTensorL` rides along, so the convention matches the
factorization `MPOTensor.physicalSlice_sector_factorization`.

**Local fix (tail index):** the selected tail entry carried by the left
sector tensor is $R_{\beta_3,\alpha_1}$, as in
`inverseMapThreeSiteContraction_eq`, rather than the entry printed in the
source display.  The correction is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equation `etarl`, lines 1441--1445. -/
noncomputable def sectorEta
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
    (R : Matrix (Fin D) (Fin D) ℂ) (α₁ β₃ : Fin D) (k h : Fin hη.m) :
    Matrix (Fin (hη.dR k) × Fin (hη.dL h)) (Fin (hη.dR k) × Fin (hη.dL h)) ℂ :=
  ∑ γ : Fin D,
    Matrix.kroneckerMap (· * ·) (sectorTensorR K hK hη β₃ k γ)
      (sectorTensorL K hK hη R α₁ β₃ h γ)

/-- **The neighboring bond contraction.** In the setting of the sector
factorization, contracting the shared virtual bond of two neighboring
factorized physical slices leaves the neighboring operator between the outer
sector tensors: for all sectors $k, h$ and virtual indices
$\beta_1, \alpha_3$,

\[
  \sum_{\gamma}
    \bigl[U_B\,\kappa_{\beta_1,\gamma}\,U_B^\dagger\bigr]^{(k)}
    \bigl[U_B\,\kappa_{\gamma,\alpha_3}\,U_B^\dagger\bigr]^{(h)}
  = (l_k)_{\beta_1} \otimes \eta_{k,h} \otimes (r_h)_{\alpha_3},
\]

stated entrywise on the sector blocks. This is the single-bond step of the
identity assembling $\bigotimes_{n} \eta_{k_n,k_{n+1}}$ from the factorized
chain.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1449. -/
theorem physicalSlice_neighboring_contraction
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ)
    (hρ : IsThreeSiteClosure K R ρ) (hη : EtaStructure ρ)
    {α₁ β₃ : Fin D} (hm : R β₃ α₁ ≠ 0) (β₁ α₃ : Fin D) (k h : Fin hη.m)
    (l₁ l₁' : Fin (hη.dL k)) (r₁ r₁' : Fin (hη.dR k))
    (l₂ l₂' : Fin (hη.dL h)) (r₂ r₂' : Fin (hη.dR h)) :
    ∑ γ : Fin D,
      Matrix.reindex hη.decompB hη.decompB
          ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β₁ γ *
            (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
          ⟨k, (l₁, r₁)⟩ ⟨k, (l₁', r₁')⟩ *
        Matrix.reindex hη.decompB hη.decompB
          ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K γ α₃ *
            (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
          ⟨h, (l₂, r₂)⟩ ⟨h, (l₂', r₂')⟩ =
      sectorTensorL K hK hη R α₁ β₃ k β₁ l₁ l₁' *
        sectorEta K hK hη R α₁ β₃ k h (r₁, l₂) (r₁', l₂') *
        sectorTensorR K hK hη β₃ h α₃ r₂ r₂' := by
  have hslice : ∀ (β α : Fin D) (k₀ : Fin hη.m) (l l' : Fin (hη.dL k₀))
      (r r' : Fin (hη.dR k₀)),
      Matrix.reindex hη.decompB hη.decompB
          ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β α *
            (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ) ⟨k₀, (l, r)⟩ ⟨k₀, (l', r')⟩ =
        sectorTensorL K hK hη R α₁ β₃ k₀ β l l' *
          sectorTensorR K hK hη β₃ k₀ α r r' := by
    intro β α k₀ l l' r r'
    rw [physicalSlice_sector_factorization K hK R ρ hρ hη hm β α,
      Matrix.blockDiagonal'_apply_eq]
    rfl
  simp_rw [hslice, sectorEta, Matrix.sum_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun γ _ => ?_
  simp only [Matrix.kroneckerMap_apply]
  ring

/-- **The closed sector tensor $(r_k|$.** Tracing the two physical legs of the
right sector tensor leaves a vector over the virtual bond:
$(r_k|_{\gamma} = \operatorname{tr}[(r_k)_{\gamma}]$.

Source: arXiv:1606.00608, Appendix C.2, equation `lkrk`, lines 1473--1477. -/
noncomputable def closedSectorR
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
    (β₃ : Fin D) (k : Fin hη.m) : Fin D → ℂ :=
  fun γ => (sectorTensorR K hK hη β₃ k γ).trace

/-- **The closed sector tensor $|l_k)$.** Tracing the two physical legs of the
left sector tensor leaves a vector over the virtual bond:
$|l_k)_{\gamma} = \operatorname{tr}[(l_k)_{\gamma}]$.

Source: arXiv:1606.00608, Appendix C.2, equation `lkrk`, lines 1473--1477. -/
noncomputable def closedSectorL
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
    (R : Matrix (Fin D) (Fin D) ℂ) (α₁ β₃ : Fin D) (k : Fin hη.m) :
    Fin D → ℂ :=
  fun γ => (sectorTensorL K hK hη R α₁ β₃ k γ).trace

/-- **The sector trace pairing.** The trace of the neighboring operator is the
pairing of the closed sector tensors:

\[
  T_{k,h} = \operatorname{tr}(\eta_{k,h}) = (r_k|l_h).
\]

Source: arXiv:1606.00608, Appendix C.2, equation `StochT`, lines 1452--1455,
and equation `Tkn`, lines 1478--1481. -/
theorem trace_sectorEta
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
    (R : Matrix (Fin D) (Fin D) ℂ) (α₁ β₃ : Fin D) (k h : Fin hη.m) :
    (sectorEta K hK hη R α₁ β₃ k h).trace =
      closedSectorR K hK hη β₃ k ⬝ᵥ closedSectorL K hK hη R α₁ β₃ h := by
  simp only [sectorEta]
  rw [Matrix.trace_sum]
  simp [closedSectorR, closedSectorL, Matrix.trace_kronecker, dotProduct]

/-- **The neighboring operator family as explicit $\eta$-data.** Once every
neighboring operator built from the sector tensors is positive semidefinite,
the family constitutes the explicit $\eta$-data consumed by the sector trace
matrix and the rank-one step.

The source obtains the positivity from the projected chain identity

\[
  0 \le \bigl[Q_{k_1}\otimes\cdots\otimes Q_{k_N}\bigr]\,\tilde\sigma\,
    \bigl[Q_{k_1}\otimes\cdots\otimes Q_{k_N}\bigr]
  = \bigotimes_{n=1}^{N} \eta_{k_n,k_{n+1}}
\]

at lines 1446--1450, and asserts that the $\eta$'s *can be chosen* positive
semidefinite; the choice is a rescaling of the sector tensors. The all-length
sector identity (arXiv:1606.00608, Appendix C.2, lines 1446--1450) is now
formalized, but it does not by itself provide a coherent positive choice of
representatives.
Positive semidefiniteness of the representatives fixed by
`MPOTensor.sectorTensorL` and `MPOTensor.sectorTensorR` therefore enters here
as a hypothesis; the remaining choice problem is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.
For an MPDO the diagonal operators are positive semidefinite
(`MPOTensor.sectorEta_self_posSemidef`), each pair `η_{k,h} ⊗ η_{h,k}` is
positive semidefinite (`MPOTensor.sectorEta_kronecker_posSemidef`), and a
rescaled positive family exists once the nonzero neighboring operators occur
in symmetric pairs (`MPOTensor.exists_explicitEtaOperators_sectorEta`).

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1455. -/
noncomputable def ExplicitEtaOperators.ofSectorTensors
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
    (R : Matrix (Fin D) (Fin D) ℂ) (α₁ β₃ : Fin D)
    (hpos : ∀ k h, (sectorEta K hK hη R α₁ β₃ k h).PosSemidef) :
    ExplicitEtaOperators hη where
  eta k h := sectorEta K hK hη R α₁ β₃ k h
  eta_pos := hpos

/-- The trace matrix of the neighboring operator family is the pairing of the
closed sector tensors: $T_{k,h} = (r_k|l_h)$, entrywise on the sector trace
matrix consumed by the rank-one step.

Source: arXiv:1606.00608, Appendix C.2, equation `Tkn`, lines 1478--1481. -/
@[simp] theorem ExplicitEtaOperators.traceMatrix_ofSectorTensors
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
    (R : Matrix (Fin D) (Fin D) ℂ) (α₁ β₃ : Fin D)
    (hpos : ∀ k h, (sectorEta K hK hη R α₁ β₃ k h).PosSemidef)
    (k h : Fin hη.m) :
    (ExplicitEtaOperators.ofSectorTensors K hK hη R α₁ β₃ hpos).traceMatrix k h =
      closedSectorR K hK hη β₃ k ⬝ᵥ closedSectorL K hK hη R α₁ β₃ h := by
  rw [ExplicitEtaOperators.traceMatrix_apply]
  exact trace_sectorEta K hK hη R α₁ β₃ k h

end MPOTensor
