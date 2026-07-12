/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.KroneckerFactorPositivity
import TNLean.MPS.MPDO.SectorEtaOperator

/-!
# Positivity of the neighboring operators of a simple MPDO

For an MPDO every finite-chain operator is positive semidefinite.  In the
sector-adapted coordinates of the Hayashi decomposition each diagonal sector
block of the basis-conjugated chain is a compression of a positive operator,
and by the sector-adapted decomposition it is the cyclic tensor product of
the neighboring operators:
\[
  0 \le \bigl[Q_{k_1}\otimes\cdots\otimes Q_{k_N}\bigr]\,\tilde\sigma\,
  \bigl[Q_{k_1}\otimes\cdots\otimes Q_{k_N}\bigr]
  = \bigotimes_{n=1}^{N}\eta_{k_n,k_{n+1}} .
\]
The chain of length one gives $\eta_{k,k}\ge 0$.  The chain of length two
gives $\eta_{k,h}\otimes\eta_{h,k}\ge 0$, and rescaling the two factors of a
nonzero positive semidefinite Kronecker product yields a scalar $c\ne 0$ with
$c\,\eta_{k,h}\ge 0$ and $c^{-1}\eta_{h,k}\ge 0$.

Choosing one such scalar for every pair of sectors produces a positive
semidefinite family of neighboring operators which agrees with the raw family
on the diagonal and differs from it by reciprocal scalars within each pair.
This realizes the positivity choice at lines 1446--1450 of the source from
the chains of length at most two.  The choice made here requires the nonzero
neighboring operators to appear in symmetric pairs; the coherence of a single
choice across longer cycles is the remaining gap recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1434--1455
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}
variable {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}

/-! ### The conjugated chain is a congruence of the original chain -/

/-- The closed-chain matrix entry as a cyclic sum over bond configurations. -/
private theorem mpo_apply_eq_sum_cyclic (M : MPOTensor d D) {N : ℕ}
    [NeZero N] (σ τ : Fin N → Fin d) :
    mpo M N σ τ =
      ∑ g : Fin N → Fin D, ∏ n : Fin N, M (σ n) (τ n) (g n) (g (n + 1)) := by
  have h := MPSTensor.trace_evalWord_eq_sum_cyclic
    (fun n : Fin N => M (σ n) (τ n)) id
  rw [MPSTensor.evalWord_ofFn_eq_prod] at h
  rw [mpo_apply, mpoMatrixEntry, MPOTensor.evalWord_ofFn]
  simpa only [id_eq] using h

/-- Expansion of one basis-conjugated local entry over the physical indices. -/
private theorem conjugatePhysical_entry_expand (K : MPOTensor d D)
    (U : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) (β α : Fin D) :
    conjugatePhysical K U a b β α =
      ∑ p : Fin d × Fin d, U a p.1 * K p.1 p.2 β α * star (U b p.2) := by
  simp only [conjugatePhysical, Matrix.mul_apply, Matrix.conjTranspose_apply,
    physicalSlice, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **The conjugated chain is a congruence.** The operator family of the
physically conjugated tensor is the congruence of the original family by the
sitewise product matrix of `U`:
\[
  \rho^{(N)}(\widetilde{\mathcal K})
  = U^{\otimes N}\,\rho^{(N)}({\mathcal K})\,\bigl(U^{\otimes N}\bigr)^\dagger.
\]

Source: arXiv:1606.00608, Appendix C.2, lines 1434--1448 (the basis change
defining $\tilde\sigma$). -/
theorem mpo_conjugatePhysical_eq (K : MPOTensor d D)
    (U : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} [NeZero N] :
    mpo (conjugatePhysical K U) N =
      Matrix.of (fun σ σ' : Fin N → Fin d => ∏ n, U (σ n) (σ' n)) *
        mpo K N *
        (Matrix.of (fun σ σ' : Fin N → Fin d => ∏ n, U (σ n) (σ' n)))ᴴ := by
  ext σ τ
  rw [mpo_apply_eq_sum_cyclic]
  have hexp : ∀ g : Fin N → Fin D,
      (∏ n : Fin N, conjugatePhysical K U (σ n) (τ n) (g n) (g (n + 1))) =
      ∑ P : Fin N → Fin d × Fin d, ∏ n : Fin N,
        (U (σ n) (P n).1 * K (P n).1 (P n).2 (g n) (g (n + 1)) *
          star (U (τ n) (P n).2)) := by
    intro g
    simp_rw [conjugatePhysical_entry_expand]
    rw [Finset.prod_univ_sum
      (fun _ : Fin N => (Finset.univ : Finset (Fin d × Fin d)))
      (fun n p => U (σ n) p.1 * K p.1 p.2 (g n) (g (n + 1)) *
        star (U (τ n) p.2))]
    simp only [Fintype.piFinset_univ]
  simp_rw [hexp]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  simp_rw [mpo_apply_eq_sum_cyclic K, star_prod, Finset.mul_sum,
    Finset.sum_mul]
  simp_rw [← Finset.prod_mul_distrib]
  rw [Finset.sum_comm_cycle]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_comm]
  exact Eq.trans
    (Fintype.sum_equiv
      (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Fin d)
        (fun _ => Fin d))
      _ (fun pr : (Fin N → Fin d) × (Fin N → Fin d) => ∏ n : Fin N,
        U (σ n) (pr.1 n) * K (pr.1 n) (pr.2 n) (g n) (g (n + 1)) *
          star (U (τ n) (pr.2 n)))
      fun P => rfl)
    (Fintype.sum_prod_type
      (f := fun pr : (Fin N → Fin d) × (Fin N → Fin d) => ∏ n : Fin N,
        U (σ n) (pr.1 n) * K (pr.1 n) (pr.2 n) (g n) (g (n + 1)) *
          star (U (τ n) (pr.2 n))))

/-- The chain operators of the physically conjugated tensor inherit positive
semidefiniteness from the chain operators of the original tensor. -/
theorem mpo_conjugatePhysical_posSemidef (K : MPOTensor d D)
    (U : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} [NeZero N]
    (hN : (mpo K N).PosSemidef) :
    (mpo (conjugatePhysical K U) N).PosSemidef := by
  rw [mpo_conjugatePhysical_eq]
  exact hN.mul_mul_conjTranspose_same _

/-! ### Positivity of the cyclic sector blocks -/

/-- **Positivity of the projected chain blocks.** For an MPDO with a sector
factorization of its physical slices, every cyclic tensor product of the
neighboring operators is positive semidefinite: it is a diagonal sector block
of the positive basis-conjugated chain,
\[
  0 \le \bigl[Q_{k_1}\otimes\cdots\otimes Q_{k_N}\bigr]\,\tilde\sigma\,
  \bigl[Q_{k_1}\otimes\cdots\otimes Q_{k_N}\bigr]
  = \bigotimes_{n=1}^{N}\eta_{k_n,k_{n+1}} .
\]

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1450. -/
theorem cyclicEtaTensorProduct_posSemidef
    (K : MPOTensor d D) (hη : EtaStructure ρ)
    (l : (q : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dL q)) (Fin (hη.dL q)) ℂ)
    (r : (q : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dR q)) (Fin (hη.dR q)) ℂ)
    (hfactor : ∀ β α,
      Matrix.reindex hη.decompB hη.decompB
          ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β α *
            (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
        = Matrix.blockDiagonal' fun q =>
            Matrix.kroneckerMap (· * ·) (l q β) (r q α))
    {N : ℕ} [NeZero N] (hN : (mpo K N).PosSemidef)
    (k : Fin N → Fin hη.m) :
    (cyclicEtaTensorProduct hη (etaOfSectorTensors hη l r) k).PosSemidef := by
  rw [← mpo_submatrix_sector_eq_cyclicEtaTensorProduct K hη l r hfactor k]
  exact (mpo_conjugatePhysical_posSemidef K hη.U_B hN).submatrix _

/-- **The diagonal neighboring operators are positive semidefinite.** The
chain of length one projected to the sector `q` is the neighboring operator
`η_{q,q}` up to the exchange of its two factors.

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1450. -/
theorem etaOfSectorTensors_self_posSemidef
    (K : MPOTensor d D) (hη : EtaStructure ρ)
    (l : (q : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dL q)) (Fin (hη.dL q)) ℂ)
    (r : (q : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dR q)) (Fin (hη.dR q)) ℂ)
    (hfactor : ∀ β α,
      Matrix.reindex hη.decompB hη.decompB
          ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β α *
            (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
        = Matrix.blockDiagonal' fun q =>
            Matrix.kroneckerMap (· * ·) (l q β) (r q α))
    (h1 : (mpo K 1).PosSemidef) (q : Fin hη.m) :
    (etaOfSectorTensors hη l r q q).PosSemidef := by
  have hcyc := cyclicEtaTensorProduct_posSemidef K hη l r hfactor h1
    (fun _ : Fin 1 => q)
  have heq : (cyclicEtaTensorProduct hη (etaOfSectorTensors hη l r)
        (fun _ : Fin 1 => q)).submatrix
        (fun x : Fin (hη.dR q) × Fin (hη.dL q) =>
          (fun _ : Fin 1 => (x.2, x.1)))
        (fun x : Fin (hη.dR q) × Fin (hη.dL q) =>
          (fun _ : Fin 1 => (x.2, x.1))) =
      etaOfSectorTensors hη l r q q := by
    ext x y
    simp only [Matrix.submatrix_apply, cyclicEtaTensorProduct]
    rw [Fin.prod_univ_one]
  rw [← heq]
  exact hcyc.submatrix _

/-- **Positivity of the mixed neighboring pairs.** The chain of length two
projected to the sectors `(q, p)` is the Kronecker product
`η_{q,p} ⊗ η_{p,q}`, so this product is positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1450. -/
theorem etaOfSectorTensors_kronecker_posSemidef
    (K : MPOTensor d D) (hη : EtaStructure ρ)
    (l : (q : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dL q)) (Fin (hη.dL q)) ℂ)
    (r : (q : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dR q)) (Fin (hη.dR q)) ℂ)
    (hfactor : ∀ β α,
      Matrix.reindex hη.decompB hη.decompB
          ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β α *
            (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
        = Matrix.blockDiagonal' fun q =>
            Matrix.kroneckerMap (· * ·) (l q β) (r q α))
    (h2 : (mpo K 2).PosSemidef) (q p : Fin hη.m) :
    (Matrix.kroneckerMap (· * ·) (etaOfSectorTensors hη l r q p)
      (etaOfSectorTensors hη l r p q)).PosSemidef := by
  have hcyc := cyclicEtaTensorProduct_posSemidef K hη l r hfactor h2 ![q, p]
  have heq : (cyclicEtaTensorProduct hη (etaOfSectorTensors hη l r)
        ![q, p]).submatrix
        (fun z : (Fin (hη.dR q) × Fin (hη.dL p)) ×
            (Fin (hη.dR p) × Fin (hη.dL q)) =>
          Fin.cons (z.2.2, z.1.1) (Fin.cons (z.1.2, z.2.1) finZeroElim))
        (fun z : (Fin (hη.dR q) × Fin (hη.dL p)) ×
            (Fin (hη.dR p) × Fin (hη.dL q)) =>
          Fin.cons (z.2.2, z.1.1) (Fin.cons (z.1.2, z.2.1) finZeroElim)) =
      Matrix.kroneckerMap (· * ·) (etaOfSectorTensors hη l r q p)
        (etaOfSectorTensors hη l r p q) := by
    ext z w
    simp only [Matrix.submatrix_apply, cyclicEtaTensorProduct,
      Matrix.kroneckerMap_apply]
    rw [Fin.prod_univ_two]
    rfl
  rw [← heq]
  exact hcyc.submatrix _

/-! ### The neighboring operators of the sector tensors -/

/-- The `sectorEta` operator computed from the concrete sector-tensor
representatives `sectorTensorL` and `sectorTensorR` equals the generic
`etaOfSectorTensors` family applied to the same tensors.  This bridge lemma
transfers the abstract positivity results proved above for
`etaOfSectorTensors` to the concrete `sectorEta` operators used in the rest
of the development. -/
theorem sectorEta_eq_etaOfSectorTensors
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
    (R : Matrix (Fin D) (Fin D) ℂ) (α₁ β₃ : Fin D) (k h : Fin hη.m) :
    sectorEta K hK hη R α₁ β₃ k h =
      etaOfSectorTensors hη (fun q => sectorTensorL K hK hη R α₁ β₃ q)
        (fun q => sectorTensorR K hK hη β₃ q) k h := by
  ext x y
  simp [sectorEta, etaOfSectorTensors, Matrix.sum_apply]

/-- **The diagonal neighboring operators are positive semidefinite.** For an
MPDO, the chain of length one projected to the sector `k` realizes
`η_{k,k}` as a compression of a positive operator:
$0 \le [Q_k]\,\tilde\sigma^{(1)}\,[Q_k] = \eta_{k,k}$.

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1450. -/
theorem sectorEta_self_posSemidef
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (hρ : IsThreeSiteClosure K R ρ) (hη : EtaStructure ρ)
    {α₁ β₃ : Fin D} (hm : R β₃ α₁ ≠ 0) (hM : IsMPDO K) (k : Fin hη.m) :
    (sectorEta K hK hη R α₁ β₃ k k).PosSemidef := by
  rw [sectorEta_eq_etaOfSectorTensors]
  exact etaOfSectorTensors_self_posSemidef K hη _ _
    (fun β α => physicalSlice_sector_factorization K hK R ρ hρ hη hm β α)
    (hM 1) k

/-- **Positivity of the mixed neighboring pairs.** For an MPDO, the chain of
length two projected to the sectors `(k, h)` realizes
`η_{k,h} ⊗ η_{h,k}` as a compression of a positive operator:
$0 \le [Q_k \otimes Q_h]\,\tilde\sigma^{(2)}\,[Q_k \otimes Q_h]
= \eta_{k,h} \otimes \eta_{h,k}$.

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1450. -/
theorem sectorEta_kronecker_posSemidef
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (hρ : IsThreeSiteClosure K R ρ) (hη : EtaStructure ρ)
    {α₁ β₃ : Fin D} (hm : R β₃ α₁ ≠ 0) (hM : IsMPDO K) (k h : Fin hη.m) :
    (Matrix.kroneckerMap (· * ·) (sectorEta K hK hη R α₁ β₃ k h)
      (sectorEta K hK hη R α₁ β₃ h k)).PosSemidef := by
  rw [sectorEta_eq_etaOfSectorTensors K hK hη R α₁ β₃ k h,
    sectorEta_eq_etaOfSectorTensors K hK hη R α₁ β₃ h k]
  exact etaOfSectorTensors_kronecker_posSemidef K hη _ _
    (fun β α => physicalSlice_sector_factorization K hK R ρ hρ hη hm β α)
    (hM 2) k h

/-- **The pairwise positivity choice.** If the neighboring operators of a
pair of sectors are both nonzero, positivity of `η_{k,h} ⊗ η_{h,k}` yields a
scalar `c ≠ 0` with `c • η_{k,h}` and `c⁻¹ • η_{h,k}` positive semidefinite
and with the rescaled pair representing the same Kronecker product, so the
choice absorbs the scalar into the sector tensors as in the source.

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1450. -/
theorem exists_smul_posSemidef_sectorEta
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (hρ : IsThreeSiteClosure K R ρ) (hη : EtaStructure ρ)
    {α₁ β₃ : Fin D} (hm : R β₃ α₁ ≠ 0) (hM : IsMPDO K) (k h : Fin hη.m)
    (hkh : sectorEta K hK hη R α₁ β₃ k h ≠ 0)
    (hhk : sectorEta K hK hη R α₁ β₃ h k ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ (c • sectorEta K hK hη R α₁ β₃ k h).PosSemidef ∧
      (c⁻¹ • sectorEta K hK hη R α₁ β₃ h k).PosSemidef ∧
      Matrix.kroneckerMap (· * ·) (c • sectorEta K hK hη R α₁ β₃ k h)
          (c⁻¹ • sectorEta K hK hη R α₁ β₃ h k) =
        Matrix.kroneckerMap (· * ·) (sectorEta K hK hη R α₁ β₃ k h)
          (sectorEta K hK hη R α₁ β₃ h k) :=
  Matrix.exists_smul_posSemidef_of_kronecker_posSemidef
    (sectorEta_kronecker_posSemidef K hK R hρ hη hm hM k h) hkh hhk

/-- **The positivity choice for the neighboring operators.** Assume the MPDO
positivity of the chain operators and that the nonzero neighboring operators
occur in symmetric pairs.  Then there is an explicit positive semidefinite
`η`-family which agrees with the raw neighboring operators on the diagonal
and differs from them by a reciprocal pair of scalars within every pair of
sectors.  In particular each two-site block
`η_{k,h} ⊗ η_{h,k}` of the sector-adapted decomposition is unchanged.

This is the choice asserted at lines 1446--1450 of the source ("the η's can
be chosen positive semidefinite"), realized from the chains of length at
most two.

**Scope restriction (symmetric support):** the hypothesis `hsym` that
`η_{k,h} = 0` forces `η_{h,k} = 0` is not stated in the source.  Without it,
a nonzero neighboring operator whose reverse pair vanishes is constrained
only by cycles through at least three sectors, and a coherent choice for the
whole family need not exist; a four-sector scalar obstruction and the
sufficient recurrence hypothesis are recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1455. -/
theorem exists_explicitEtaOperators_sectorEta
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (hρ : IsThreeSiteClosure K R ρ) (hη : EtaStructure ρ)
    {α₁ β₃ : Fin D} (hm : R β₃ α₁ ≠ 0) (hM : IsMPDO K)
    (hsym : ∀ k h, sectorEta K hK hη R α₁ β₃ k h = 0 →
      sectorEta K hK hη R α₁ β₃ h k = 0) :
    ∃ data : ExplicitEtaOperators hη,
      (∀ k, data.eta k k = sectorEta K hK hη R α₁ β₃ k k) ∧
      (∀ k h, ∃ c : ℂ, c ≠ 0 ∧
        data.eta k h = c • sectorEta K hK hη R α₁ β₃ k h ∧
        data.eta h k = c⁻¹ • sectorEta K hK hη R α₁ β₃ h k) ∧
      ∀ k h, Matrix.kroneckerMap (· * ·) (data.eta k h) (data.eta h k) =
        Matrix.kroneckerMap (· * ·) (sectorEta K hK hη R α₁ β₃ k h)
          (sectorEta K hK hη R α₁ β₃ h k) := by
  classical
  have hpair : ∀ k h, ∃ c : ℂ, c ≠ 0 ∧
      (c • sectorEta K hK hη R α₁ β₃ k h).PosSemidef ∧
      (c⁻¹ • sectorEta K hK hη R α₁ β₃ h k).PosSemidef := by
    intro k h
    by_cases h0 : sectorEta K hK hη R α₁ β₃ k h = 0
    · refine ⟨1, one_ne_zero, ?_, ?_⟩
      · rw [h0, smul_zero]
        exact Matrix.PosSemidef.zero
      · rw [hsym k h h0, smul_zero]
        exact Matrix.PosSemidef.zero
    · obtain ⟨c, hc, hpos1, hpos2, -⟩ :=
        exists_smul_posSemidef_sectorEta K hK R hρ hη hm hM k h h0
          fun hz => h0 (hsym h k hz)
      exact ⟨c, hc, hpos1, hpos2⟩
  -- The scalar assigned to the ordered pair `(k, h)`, together with its
  -- defining equalities against both `sectorEta k h` and `sectorEta h k`.
  -- Proved once and reused for the pairwise-scalar and block-preservation
  -- conjuncts below, so both refer to the same witness `c`.
  have hexists : ∀ k h, ∃ c : ℂ, c ≠ 0 ∧
      (if k = h then 1 else if k ≤ h then (hpair k h).choose
        else ((hpair h k).choose)⁻¹) • sectorEta K hK hη R α₁ β₃ k h =
        c • sectorEta K hK hη R α₁ β₃ k h ∧
      (if h = k then 1 else if h ≤ k then (hpair h k).choose
        else ((hpair k h).choose)⁻¹) • sectorEta K hK hη R α₁ β₃ h k =
        c⁻¹ • sectorEta K hK hη R α₁ β₃ h k := by
    intro k h
    by_cases hkh : k = h
    · subst hkh
      exact ⟨1, one_ne_zero, by simp, by simp⟩
    · by_cases hle : k ≤ h
      · have hgt : ¬h ≤ k := fun hle' => hkh (le_antisymm hle hle')
        exact ⟨(hpair k h).choose, (hpair k h).choose_spec.1,
          by simp [hkh, hle], by simp [Ne.symm hkh, hgt]⟩
      · have hlt : h ≤ k := le_of_not_ge hle
        refine ⟨((hpair h k).choose)⁻¹, inv_ne_zero (hpair h k).choose_spec.1,
          by simp [hkh, hle], ?_⟩
        rw [inv_inv]
        simp [Ne.symm hkh, hlt]
  refine ⟨⟨fun k h =>
      (if k = h then 1 else if k ≤ h then (hpair k h).choose
        else ((hpair h k).choose)⁻¹) • sectorEta K hK hη R α₁ β₃ k h,
      ?_⟩, ?_, hexists, ?_⟩
  · intro k h
    by_cases hkh : k = h
    · subst hkh
      simpa using sectorEta_self_posSemidef K hK R hρ hη hm hM k
    · by_cases hle : k ≤ h
      · simpa [hkh, hle] using (hpair k h).choose_spec.2.1
      · simpa [hkh, hle] using (hpair h k).choose_spec.2.2
  · intro k
    simp
  · intro k h
    obtain ⟨c, hc, heq1, heq2⟩ := hexists k h
    dsimp only
    rw [heq1, heq2]
    exact Matrix.smul_kronecker_smul_inv_eq _ _ hc

end MPOTensor
