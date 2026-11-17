/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.CanonicalFormAncillaBlocking
import TNLean.MPS.MPU.ConjugationStrictEquivalence
import TNLean.MPS.MPU.PhysicalMatrixSymmetry
import TNLean.MPS.MPU.StandardFormDoubling
import TNLean.MPS.MPU.TwoSiteStandardFormSourceCuts

/-!
# Equivalence of conjugation-invariant MPUs when one rank is odd

Two conjugation-invariant MPUs in canonical form II whose standard forms have the
same ranks `ℓ, r`, one of them odd, are equivalent under conjugation symmetry
(arXiv:1703.09188, Corollary `cor:all-equivalent-under-conjugation`,
lines 1450--1460). The proof follows the source: after a gauge making both
standard forms real (Case I of Proposition `corconj`), the doubled block has the
standard form `u⁽²⁾, v⁽²⁾` of `MPOTensor.TwoSiteStandardFormData.doubled`. Its
determinants agree for both tensors, so Theorem `conjphs` (when `d` is odd) or
Theorem `prop:conjsym-strict-equiv` (when `d` is even) makes the blocks of four
sites strictly equivalent under conjugation.

## Main definitions and results

* `MPOTensor.conjugationSymmetryFamily`: entrywise complex conjugation at every
  physical dimension.
* `MPOTensor.equivalentUnderSymmetry_conjugation_of_odd`: the corollary.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D₁ D₂ ℓ r : ℕ}

/-- **Complex conjugation as a coherent symmetry family.** The action at every
physical dimension is entrywise complex conjugation of the finite-chain operator,
at every positive length. Conjugation is fixed by the computational basis alone
(arXiv:1703.09188, lines 1005--1010), so its component at an enlarged physical
dimension `d x` is again conjugation and it commutes with adjoining an identity
ancilla. Equivalence under this family is therefore exactly Definition
`def:equivalent-symmetry` (lines 1356--1366) for conjugation. -/
def conjugationSymmetryFamily : FiniteChainOperatorSymmetryFamily where
  applicable := {N | 0 < N}
  action := fun X ↦ X.map (starRingEnd ℂ)
  tensorPhysicalId_semiconj d x N := conjugationSymmetry_tensorPhysicalId_semiconj d x N

theorem conjugationSymmetryFamily_at (d : ℕ) :
    conjugationSymmetryFamily.at d = conjugationSymmetry d := rfl

/-- Physical relabelling preserves invariance under conjugation. -/
theorem isInvariantUnderSymmetry_conjugation_reindexPhysical {d' D : ℕ} (e : Fin d' ≃ Fin d)
    {U : MPOTensor d D} (hU : IsInvariantUnderSymmetry (conjugationSymmetry d) U) :
    IsInvariantUnderSymmetry (conjugationSymmetry d') (reindexPhysical e U) := by
  intro N hN
  change (mpo (reindexPhysical e U) N).map (starRingEnd ℂ) = mpo (reindexPhysical e U) N
  rw [mpo_reindexPhysical]
  nth_rewrite 2 [← hU hN]
  rfl

/-- **Strict equivalence under conjugation is preserved by physical relabelling**
of both endpoints, whenever the relabelled endpoints are in canonical form. -/
theorem StrictlyEquivalentUnderSymmetry.reindexPhysical_conjugation {d' D₁ D₂ : ℕ}
    (e : Fin d' ≃ Fin d) {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : MPSTensor.IsMPUCanonicalForm (reindexPhysical e U).toMPSTensor)
    (hV : MPSTensor.IsMPUCanonicalForm (reindexPhysical e V).toMPSTensor)
    (h : StrictlyEquivalentUnderSymmetry (conjugationSymmetry d) U V rfl) :
    StrictlyEquivalentUnderSymmetry (conjugationSymmetry d')
      (reindexPhysical e U) (reindexPhysical e V) rfl := by
  obtain ⟨-, -, D', ha, hb, hJ⟩ := h
  have hrefl : ∀ {n E : ℕ} (W : MPOTensor n E),
      reindexPhysical (finCongr (rfl : n = n)).symm W = W := fun W ↦ by
    funext i j
    simp [reindexPhysical]
  rw [hrefl] at hJ
  obtain ⟨γ, hγ⟩ := hJ
  refine ⟨hU, hV, D', ha, hb, ?_⟩
  rw [hrefl]
  exact ⟨γ.map (continuous_reindexPhysical e), fun t ↦
    ⟨(hγ t).1.reindexPhysical e,
      isInvariantUnderSymmetry_conjugation_reindexPhysical e (hγ t).2⟩⟩

/-- The physical identification of the twice-blocked two-site block with the block
of four sites. -/
private noncomputable def fourSiteEquiv (d : ℕ) :
    Fin (Kraus.blockPhysDim (d * d) 2) ≃ Fin (Kraus.blockPhysDim d 4) :=
  (twoSiteBlockEquiv (d * d)).symm.trans
    ((finProdFinEquiv.symm.trans ((Equiv.prodCongr (twoSiteBlockEquiv d)
      (twoSiteBlockEquiv d)).trans finProdFinEquiv)).trans
    ((twoSiteBlockEquiv (Kraus.blockPhysDim d 2)).trans
      (MPSTensor.directIteratedBlockEquiv d 2 2).symm))

private theorem reindexPhysical_symm_reindexPhysical {n n' E : ℕ} (σ : Fin n ≃ Fin n')
    (W : MPOTensor n' E) : reindexPhysical σ.symm (reindexPhysical σ W) = W := by
  funext i j
  simp [reindexPhysical]

private theorem blockTwo_eq_reindexPhysical {n E : ℕ} (W : MPOTensor n E) :
    blockTwo W = reindexPhysical (twoSiteBlockEquiv n) (blockTensor W 2) := by
  rw [blockTwo_eq_blockTensor_reindex]
  rfl

/-- The two-site block of the two-site block, blocked twice more, is the block of
four sites after a physical relabelling. -/
private theorem blockTensor_blockTwo_two {D : ℕ} (U : MPOTensor d D) :
    blockTensor (blockTwo U) 2 = reindexPhysical (fourSiteEquiv d) (blockTensor U 4) := by
  have hR : ∀ {n n' E : ℕ} (σ : Fin n' ≃ Fin n) (W : MPOTensor n E),
      blockTwo (reindexPhysical σ W) = reindexPhysical
        (finProdFinEquiv.symm.trans ((Equiv.prodCongr σ σ).trans finProdFinEquiv))
        (blockTwo W) := fun σ W ↦ by
    ext I J
    simp [blockTwo, reindexPhysical]
  have h4 : blockTensor (blockTensor U 2) 2 =
      reindexPhysical (MPSTensor.directIteratedBlockEquiv d 2 2).symm (blockTensor U (2 * 2)) := by
    rw [← reindexPhysical_blockTensor_blockTensor U 2 2, reindexPhysical_symm_reindexPhysical]
  have h0 : blockTensor (blockTwo U) 2 =
      reindexPhysical (twoSiteBlockEquiv (d * d)).symm (blockTwo (blockTwo U)) := by
    rw [blockTwo_eq_reindexPhysical (blockTwo U), reindexPhysical_symm_reindexPhysical]
  rw [h0, blockTwo_eq_reindexPhysical U, hR, blockTwo_eq_reindexPhysical (blockTensor U 2), h4]
  rfl

/-- A real unitary gate has determinant `±1` through every identification of its
coordinate spaces. -/
theorem det_submatrix_eq_one_or_neg_one_of_real {m n : Type*} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] {U : Matrix m n ℂ} (hU : U.IsUnitaryBetween)
    (hr : U.map (starRingEnd ℂ) = U) (e : m ≃ n) :
    (U.submatrix id e).det = 1 ∨ (U.submatrix id e).det = -1 :=
  Matrix.det_eq_one_or_neg_one_of_map_star_eq
    ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mp
      (by simpa [Matrix.reindex_apply] using hU.reindex _ (Equiv.refl _) e.symm))
    (by ext i j; exact congrFun (congrFun hr i) (e j))

/-- The doubled unshifted gate of real unitary gates has determinant
`det(v)^{rℓ}`, read through `doubledIdent e`. -/
theorem det_doubledU_submatrix_of_real {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ} (hu : u.IsUnitaryBetween)
    (hur : u.map (starRingEnd ℂ) = u) (e : Fin ℓ × Fin r ≃ Fin d × Fin d) :
    ((doubledU u v).submatrix id (doubledIdent e)).det =
      (v.submatrix id (e.symm.trans (Equiv.prodComm _ _))).det ^ (r * ℓ) := by
  rw [det_doubledU_submatrix, pow_mul]
  rcases det_submatrix_eq_one_or_neg_one_of_real hu hur e with h | h <;> simp [h]

/-- An identity ancilla of dimension one is a relabelling of the physical index. -/
private theorem tensorPhysicalId_one {D : ℕ} (U : MPOTensor d D) :
    tensorPhysicalId U 1 = reindexPhysical (finCongr (Nat.mul_one d)) U := by
  funext i j
  have hi : i.divNat = finCongr (Nat.mul_one d) i := Fin.ext (by simp [Fin.divNat])
  have hj : j.divNat = finCongr (Nat.mul_one d) j := Fin.ext (by simp [Fin.divNat])
  simp [tensorPhysicalId, reindexPhysical, hi, hj, Subsingleton.elim i.modNat j.modNat]

private theorem strictlyEquivalent_finCongr {n : ℕ} (h : n = d)
    {U₁ : MPOTensor d D₁} {U₂ : MPOTensor d D₂}
    (H : StrictlyEquivalentUnderSymmetry (conjugationSymmetry (Kraus.blockPhysDim d 4))
      (blockTensor U₁ 4) (blockTensor U₂ 4) rfl) :
    StrictlyEquivalentUnderSymmetry (conjugationSymmetry (Kraus.blockPhysDim n 4))
      (blockTensor (reindexPhysical (finCongr h) U₁) 4)
      (blockTensor (reindexPhysical (finCongr h) U₂) 4) rfl := by
  subst h
  have hrefl : ∀ {E : ℕ} (W : MPOTensor n E), reindexPhysical (finCongr rfl) W = W :=
    fun W ↦ by funext i j; simp [reindexPhysical]
  simpa only [hrefl] using H

/-- **Equivalence from the doubled blocks.** If the blocks of two sites of the
two-site blocks of `𝒰₁, 𝒰₂` are strictly equivalent under conjugation, then
`𝒰₁` and `𝒰₂` are equivalent under conjugation symmetry, with trivial ancillas
and blocking length four. Source: arXiv:1703.09188, Definition
`def:equivalent-symmetry`, lines 1356--1366, as used in the proofs of
Corollaries `cor:all-equivalent-under-conjugation` (lines 1450--1460) and
`cor:equiv-under-conjugation` (lines 1548--1567). -/
theorem equivalentUnderSymmetry_conjugation_of_blockTensor_blockTwo
    {𝒰₁ : MPOTensor d D₁} {𝒰₂ : MPOTensor d D₂}
    (h₁ : IsMPUCanonicalFormII 𝒰₁) (h₂ : IsMPUCanonicalFormII 𝒰₂)
    (H : StrictlyEquivalentUnderSymmetry
      (conjugationSymmetry (Kraus.blockPhysDim (d * d) 2))
      (blockTensor (blockTwo 𝒰₁) 2) (blockTensor (blockTwo 𝒰₂) 2) rfl) :
    EquivalentUnderSymmetry conjugationSymmetryFamily 𝒰₁ 𝒰₂ := by
  have : NeZero d := h₁.neZero_phys
  have hcf : ∀ {E : ℕ} {W : MPOTensor d E}, IsMPUCanonicalFormII W →
      MPSTensor.IsMPUCanonicalForm (reindexPhysical (fourSiteEquiv d).symm
        (blockTensor (blockTwo W) 2)).toMPSTensor := fun {E W} hW ↦ by
    rw [blockTensor_blockTwo_two, reindexPhysical_symm_reindexPhysical]
    exact (hW.blockTensor 4 (by norm_num)).isMPUCanonicalForm
  have H4 := H.reindexPhysical_conjugation (fourSiteEquiv d).symm (hcf h₁) (hcf h₂)
  rw [blockTensor_blockTwo_two, blockTensor_blockTwo_two, reindexPhysical_symm_reindexPhysical,
    reindexPhysical_symm_reindexPhysical] at H4
  refine ⟨h₁.isMPU, h₂.isMPU, 4, 1, 1, by norm_num, by norm_num, by norm_num,
    Nat.coprime_one_left 1, rfl, ?_⟩
  rw [conjugationSymmetryFamily_at, conjugationSymmetry_block (by norm_num),
    tensorPhysicalId_one, tensorPhysicalId_one]
  exact strictlyEquivalent_finCongr (Nat.mul_one d) H4

/-- **Conjugation-invariant MPUs with an odd source rank are equivalent.** Let
`𝒰₁, 𝒰₂` be MPUs in canonical form II, invariant under complex conjugation,
whose two-site blocks have standard forms of the same ranks `ℓ, r`. If `ℓ` or
`r` is odd, then `𝒰₁` and `𝒰₂` are equivalent under conjugation symmetry: the
blocks of four sites, with trivial ancillas, are strictly equivalent under
conjugation.

The common ranks `ℓ, r` and the common physical dimension `d` are the standing
convention of the subsection (lines 1388--1398). Since `ℓ r = d²` for both, the
ancilla dimensions `p_a = p_b = 1` of Definition `def:equivalent-symmetry` are
forced, not assumed. The hypothesis that `ℓ` or `r` is odd is the standing
hypothesis of the subsection containing the corollary (line 1401). It is used
only to place both standard forms in Case I of Proposition `corconj` with the
same rank parities: the identity and the shift on a single site are both in
Case I but have indices `0` and `1`, so they are not equivalent, and the ranks
cannot be dropped from the hypotheses.

Source: arXiv:1703.09188, Corollary `cor:all-equivalent-under-conjugation`,
lines 1450--1460, with the doubled gates of lines 1456--1458. -/
theorem equivalentUnderSymmetry_conjugation_of_odd
    {𝒰₁ : MPOTensor d D₁} {𝒰₂ : MPOTensor d D₂}
    (h₁ : IsMPUCanonicalFormII 𝒰₁) (h₂ : IsMPUCanonicalFormII 𝒰₂)
    (hc₁ : IsInvariantUnderSymmetry (conjugationSymmetry d) 𝒰₁)
    (hc₂ : IsInvariantUnderSymmetry (conjugationSymmetry d) 𝒰₂)
    {u₁ u₂ : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v₁ v₂ : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S₁ : TwoSiteStandardFormData (blockTwo 𝒰₁) u₁ v₁)
    (S₂ : TwoSiteStandardFormData (blockTwo 𝒰₂) u₂ v₂)
    (hodd : Odd ℓ ∨ Odd r) :
    EquivalentUnderSymmetry conjugationSymmetryFamily 𝒰₁ 𝒰₂ := by
  have : NeZero d := h₁.neZero_phys
  -- Invariance and canonical form II of two-site blocks.
  have hinvB : ∀ {n E : ℕ} {W : MPOTensor n E},
      IsInvariantUnderSymmetry (conjugationSymmetry n) W →
        IsInvariantUnderSymmetry (conjugationSymmetry (n * n)) (blockTwo W) := by
    intro n E W hW
    rw [blockTwo_eq_reindexPhysical]
    apply isInvariantUnderSymmetry_conjugation_reindexPhysical
    rw [← conjugationSymmetry_block (by norm_num)]
    exact hW.blockTensor 2
  have hcc : ∀ {n E : ℕ} {W : MPOTensor n E},
      IsInvariantUnderSymmetry (conjugationSymmetry n) W →
        ∀ N : ℕ, 0 < N → mpo (blockTwo W) N = (mpo (blockTwo W) N).map (starRingEnd ℂ) :=
    fun hW _ hN ↦ (hinvB hW hN).symm
  -- Real standard forms (Case I of `corconj`).
  obtain ⟨x₁, y₁, hU₁, hV₁⟩ := S₁.exists_real_gauge_of_conjugation (hcc hc₁) hodd
  obtain ⟨x₂, y₂, hU₂, hV₂⟩ := S₂.exists_real_gauge_of_conjugation (hcc hc₂) hodd
  set U₁ := ((x₁ : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y₁ : Matrix (Fin r) (Fin r) ℂ)) * u₁
  set V₁ := v₁ * (star (y₁ : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x₁ : Matrix (Fin ℓ) (Fin ℓ) ℂ))
  set U₂ := ((x₂ : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y₂ : Matrix (Fin r) (Fin r) ℂ)) * u₂
  set V₂ := v₂ * (star (y₂ : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x₂ : Matrix (Fin ℓ) (Fin ℓ) ℂ))
  let T₁ := S₁.ofGateGauges x₁ y₁
  let T₂ := S₂.ofGateGauges x₂ y₂
  -- One identification of `ℂ^ℓ ⊗ ℂ^r` with `ℂ^d ⊗ ℂ^d`.
  have hcard : Fintype.card (Fin ℓ × Fin r) = Fintype.card (Fin d × Fin d) := by
    have h1 := Matrix.IsIsometry.card_le u₁ S₁.u_unitary.1
    have h2 := Matrix.IsCoisometry.card_le u₁ S₁.u_unitary.2
    omega
  have hℓr : r * ℓ = d * d := by
    simpa [Fintype.card_prod, Nat.mul_comm] using hcard
  let e : Fin ℓ × Fin r ≃ Fin d × Fin d := Fintype.equivOfCardEq hcard
  set f := e.symm.trans (Equiv.prodComm (Fin ℓ) (Fin r))
  set e' := doubledIdent e
  set g := e'.symm.trans (Equiv.prodComm (Fin (ℓ * d)) (Fin (d * r)))
  set c : ℂ := (Equiv.Perm.sign (g.trans (doubledShiftIdent f).symm) : ℂ)
  have hdV : ∀ V : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ,
      ((doubledV V).submatrix id g).det = c * (V.submatrix id f).det ^ (d * d) := fun V ↦ by
    rw [det_submatrix_eq_sign_mul _ g (doubledShiftIdent f), det_doubledV_submatrix]
  have hs₁ := det_submatrix_eq_one_or_neg_one_of_real T₁.v_unitary hV₁ f
  have hs₂ := det_submatrix_eq_one_or_neg_one_of_real T₂.v_unitary hV₂ f
  have hreal : ∀ {U : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
      {V : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}, U.map (starRingEnd ℂ) = U →
        V.map (starRingEnd ℂ) = V → (doubledU U V).map (starRingEnd ℂ) = doubledU U V ∧
          (doubledV V).map (starRingEnd ℂ) = doubledV V := fun hU hV ↦
    ⟨by rw [doubledU_map_star, hU, hV], by rw [doubledV_map_star, hV]⟩
  -- Strict equivalence of the blocks of four sites, in doubled coordinates.
  have H : StrictlyEquivalentUnderSymmetry
      (conjugationSymmetry (Kraus.blockPhysDim (d * d) 2))
      (blockTensor (blockTwo 𝒰₁) 2) (blockTensor (blockTwo 𝒰₂) 2) rfl := by
    rcases Nat.even_or_odd d with hd | hd
    · -- `d` even: Theorem `prop:conjsym-strict-equiv`, Case I.
      have hev : ∀ s : ℂ, s = 1 ∨ s = -1 → s ^ (d * d) = 1 := by
        rintro s (rfl | rfl)
        · simp
        · exact (hd.mul_right d).neg_one_pow
      refine strictlyEquivalentUnderSymmetry_conjugation_of_det_eq_of_even h₁.blockTwo h₂.blockTwo
        T₁.doubled T₂.doubled (hd.mul_left ℓ) (hd.mul_right r)
        (Or.inl ⟨(hreal hU₁ hV₁).1, (hreal hU₁ hV₁).2, (hreal hU₂ hV₂).1,
          (hreal hU₂ hV₂).2⟩) e' ?_ ?_
      · rw [det_doubledU_submatrix_of_real T₁.u_unitary hU₁,
          det_doubledU_submatrix_of_real T₂.u_unitary hU₂, hℓr, hev _ hs₁, hev _ hs₂]
      · rw [hdV, hdV, hev _ hs₁, hev _ hs₂]
    · -- `d` odd: Theorem `conjphs`.
      have hodd' : Odd (ℓ * d) ∨ Odd (d * r) := by
        rcases hodd with h | h
        · exact Or.inl (h.mul hd)
        · exact Or.inr (hd.mul h)
      have hsq : ∀ s : ℂ, s = 1 ∨ s = -1 → s ^ (d * d) * (c * s ^ (d * d)) = c := by
        rintro s (rfl | rfl)
        · simp
        · rw [mul_left_comm, ← pow_add, ← two_mul, pow_mul]
          simp
      refine strictlyEquivalentUnderSymmetry_conjugation_of_det_mul_eq h₁.blockTwo h₂.blockTwo
        (hcc (hinvB hc₁)) (hcc (hinvB hc₂)) T₁.doubled T₂.doubled hodd' ?_
      rw [Matrix.det_mul_swap_eq _ _ e', Matrix.det_mul_swap_eq _ _ e',
        det_doubledU_submatrix_of_real T₁.u_unitary hU₁,
        det_doubledU_submatrix_of_real T₂.u_unitary hU₂, hdV, hdV, hℓr, hsq _ hs₁, hsq _ hs₂]
  exact equivalentUnderSymmetry_conjugation_of_blockTensor_blockTwo h₁ h₂ H

end MPOTensor
