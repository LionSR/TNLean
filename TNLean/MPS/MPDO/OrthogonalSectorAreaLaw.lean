/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.LocalOrthogonalSumAreaLaw
import TNLean.MPS.MPDO.GSNNCHOrthogonalSectors

/-!
# Saturated area law for orthogonal commuting sectors

This file supplies the local-support implication from orthogonally supported
commuting bond products to the entropy decomposition for a finite direct sum.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Definition 4.8, lines 838--850, and Appendix C.2, Proposition `prop4to2`,
  lines 1801--1808.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D g : ℕ} {dim : Fin g → ℕ}

private theorem firstSiteMatrix_mul_embed_twoSiteSectorProjection_zero
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P * P = P)
    (n : ℕ) (hn : 0 < n) :
    firstSiteMatrix P n *
        embedLocalOperator (d := d) 2 (n + 1) (by omega) (0 : Fin (n + 1))
          (twoSiteSectorProjection P) =
      embedLocalOperator (d := d) 2 (n + 1) (by omega) (0 : Fin (n + 1))
        (twoSiteSectorProjection P) := by
  classical
  ext σ τ
  rw [firstSiteMatrix_mul_apply]
  simp only [embedLocalOperator_apply]
  have hcons (x : Fin d) (k : Fin (n + 1))
      (hk : ¬ ((k.val + (n + 1) - (0 : Fin (n + 1)).val) % (n + 1) < 2)) :
      (Fin.cons x (fun j : Fin n ↦ σ j.succ) : Fin (n + 1) → Fin d) k = σ k := by
    have hk0 : k ≠ 0 := by
      intro hkzero
      subst k
      simp at hk
    exact Fin.cases (motive := fun k ↦ k ≠ 0 →
        (Fin.cons x (fun j : Fin n ↦ σ j.succ) : Fin (n + 1) → Fin d) k = σ k)
      (fun hkzero ↦ (hkzero rfl).elim) (fun j _ ↦ by simp) k hk0
  have hagree (x : Fin d) :
      AgreesOutsideWindow (d := d) 2 (by omega) (0 : Fin (n + 1))
          (Fin.cons x (σ ∘ Fin.succ)) τ ↔
        AgreesOutsideWindow (d := d) 2 (by omega) (0 : Fin (n + 1)) σ τ := by
    rw [agreesOutsideWindow_iff, agreesOutsideWindow_iff]
    constructor
    · intro h k hk
      rw [← hcons x k hk]
      exact h k hk
    · intro h k hk
      rw [h k hk]
      exact (hcons x k hk).symm
  by_cases hAgree :
      AgreesOutsideWindow (d := d) 2 (by omega) (0 : Fin (n + 1)) σ τ
  · simp_rw [if_pos ((hagree _).mpr hAgree)]
    rw [if_pos hAgree]
    simp only [twoSiteSectorProjection, MPSTensor.extractWindow,
      finTwoArrowEquiv, Matrix.reindex_apply]
    let i₁ : Fin (n + 1) :=
      ⟨1 % (n + 1), Nat.mod_lt _ (by omega)⟩
    change (∑ x : Fin d, P (σ 0) x *
        (P x (τ 0) *
          P ((Fin.cons x (σ ∘ Fin.succ) : Fin (n + 1) → Fin d) i₁) (τ i₁))) =
      P (σ 0) (τ 0) * P (σ i₁) (τ i₁)
    have hsecond (x : Fin d) :
        (Fin.cons x (σ ∘ Fin.succ) : Fin (n + 1) → Fin d) i₁ = σ i₁ := by
      let zero : Fin n := ⟨0, hn⟩
      have hi : i₁ = Fin.succ zero := by
        apply Fin.ext
        simp [i₁, zero, hn]
      rw [hi]
      simp
    simp_rw [hsecond]
    calc
      ∑ x : Fin d, P (σ 0) x *
          (P x (τ 0) * P (σ i₁) (τ i₁)) =
          (∑ x : Fin d, P (σ 0) x * P x (τ 0)) *
            P (σ i₁) (τ i₁) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = P (σ 0) (τ 0) * P (σ i₁) (τ i₁) := by
        rw [← Matrix.mul_apply, hP]
  · simp_rw [if_neg ((hagree _).not.mpr hAgree)]
    rw [if_neg hAgree]
    simp

private theorem OrthogonalCommutingSectorFamily.firstSiteMatrix_mul_mpo
    {K : (s : Fin g) → MPOTensor d (dim s)}
    (F : OrthogonalCommutingSectorFamily K) (s : Fin g)
    (n : ℕ) (hn : 0 < n) :
    firstSiteMatrix (F.projection s) n * mpo (K s) (n + 1) =
      mpo (K s) (n + 1) := by
  classical
  let hN : 2 ≤ n + 1 := by omega
  let Q := twoSiteSectorProjection (F.projection s)
  let B := (F.bondData s).bond
  let Q₀ := embedLocalOperator (d := d) 2 (n + 1) hN (0 : Fin (n + 1)) Q
  let B₀ := embedLocalOperator (d := d) 2 (n + 1) hN (0 : Fin (n + 1)) B
  have hP₀Q₀ : firstSiteMatrix (F.projection s) n * Q₀ = Q₀ := by
    exact firstSiteMatrix_mul_embed_twoSiteSectorProjection_zero
      (F.projection s) (F.projection_isOrthogonal s).2 n hn
  have hQ₀B₀Q₀ : Q₀ * B₀ * Q₀ = B₀ := by
    rw [← embedLocalOperator_mul, ← embedLocalOperator_mul,
      F.bond_supported s]
  have hP₀B₀ : firstSiteMatrix (F.projection s) n * B₀ = B₀ := by
    calc
      firstSiteMatrix (F.projection s) n * B₀ =
          firstSiteMatrix (F.projection s) n * (Q₀ * B₀ * Q₀) := by
        rw [hQ₀B₀Q₀]
      _ = (firstSiteMatrix (F.projection s) n * Q₀) * B₀ * Q₀ := by
        simp only [Matrix.mul_assoc]
      _ = Q₀ * B₀ * Q₀ := by rw [hP₀Q₀]
      _ = B₀ := hQ₀B₀Q₀
  simp only [F.realizes_mpo s (n + 1) hN, CommutingFormData.product,
    TranslationInvariantBondData.toCommutingFormData_bondAt]
  change firstSiteMatrix (F.projection s) n *
      (List.ofFn fun i : Fin (n + 1) ↦
        embedLocalOperator (d := d) 2 (n + 1) hN i B).prod = _
  rw [List.ofFn_succ, List.prod_cons, ← Matrix.mul_assoc]
  change firstSiteMatrix (F.projection s) n * B₀ *
      (List.ofFn fun i : Fin n ↦
        embedLocalOperator (d := d) 2 (n + 1) hN i.succ B).prod =
    B₀ * (List.ofFn fun i : Fin n ↦
      embedLocalOperator (d := d) 2 (n + 1) hN i.succ B).prod
  exact congrArg (fun X ↦ X *
    (List.ofFn fun i : Fin n ↦
      embedLocalOperator (d := d) 2 (n + 1) hN i.succ B).prod) hP₀B₀

private theorem firstSiteMatrix_mul_reducedBlockState_of_mul_normalizedMPO
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    {N' L : ℕ} (hL : L + 1 ≤ N' + 1)
    (hfull : firstSiteMatrix P N' * normalizedMPO M (N' + 1) =
      normalizedMPO M (N' + 1)) :
    firstSiteMatrix P L * reducedBlockState M (N' + 1) (L + 1) hL =
      reducedBlockState M (N' + 1) (L + 1) hL := by
  ext u v
  obtain ⟨a, u', rfl⟩ : ∃ a u', u = Fin.cons a u' :=
    ⟨u 0, u ∘ Fin.succ, (Fin.cons_self_tail u).symm⟩
  obtain ⟨b, v', rfl⟩ : ∃ b v', v = Fin.cons b v' :=
    ⟨v 0, v ∘ Fin.succ, (Fin.cons_self_tail v).symm⟩
  rw [firstSiteMatrix_mul_apply]
  simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ]
  simp_rw [reducedBlockState_eq_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  let z : Fin N' → Fin d :=
    Fin.append u' w ∘ Fin.cast (show N' = L + (N' + 1 - (L + 1)) by omega)
  let full (x : Fin d) : Fin (N' + 1) → Fin d :=
    Fin.append (Fin.cons x u') w ∘
      Fin.cast (show N' + 1 = L + 1 + (N' + 1 - (L + 1)) by omega)
  let full' : Fin (N' + 1) → Fin d :=
    Fin.append (Fin.cons b v') w ∘
      Fin.cast (show N' + 1 = L + 1 + (N' + 1 - (L + 1)) by omega)
  change (∑ x : Fin d, P a x * normalizedMPO M (N' + 1) (full x) full') =
    normalizedMPO M (N' + 1) (full a) full'
  have htail (x : Fin d) : full x ∘ Fin.succ = z := by
    funext i
    simp only [full, z, Function.comp_apply]
    by_cases hi : i.val < L
    · have hleft : Fin.cast
          (show N' + 1 = L + 1 + (N' + 1 - (L + 1)) by omega) i.succ =
          Fin.castAdd (N' + 1 - (L + 1)) (Fin.succ ⟨i.val, hi⟩) := by
        apply Fin.ext
        simp
      have hright : Fin.cast
          (show N' = L + (N' + 1 - (L + 1)) by omega) i =
          Fin.castAdd (N' + 1 - (L + 1)) ⟨i.val, hi⟩ := by
        apply Fin.ext
        simp
      rw [hleft, hright, Fin.append_left, Fin.append_left, Fin.cons_succ]
    · let k : Fin (N' + 1 - (L + 1)) := ⟨i.val - L, by omega⟩
      have hleft : Fin.cast
          (show N' + 1 = L + 1 + (N' + 1 - (L + 1)) by omega) i.succ =
          Fin.natAdd (L + 1) k := by
        apply Fin.ext
        simp [k]
        omega
      have hright : Fin.cast
          (show N' = L + (N' + 1 - (L + 1)) by omega) i =
          Fin.natAdd L k := by
        apply Fin.ext
        simp [k]
        omega
      rw [hleft, hright, Fin.append_right, Fin.append_right]
  have hfull_eq (x : Fin d) : full x = Fin.cons x z := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [full, Function.comp_apply]
      have hzero : Fin.cast
          (show N' + 1 = L + 1 + (N' + 1 - (L + 1)) by omega) 0 =
          Fin.castAdd (N' + 1 - (L + 1)) (0 : Fin (L + 1)) := by
        apply Fin.ext
        simp
      rw [hzero, Fin.append_left, Fin.cons_zero]
      simp
    · exact congrFun (htail x) j
  have hentry := congrFun (congrFun hfull (full a)) full'
  rw [firstSiteMatrix_mul_apply] at hentry
  simpa only [hfull_eq, Fin.cons_zero, Function.comp_def, Fin.cons_succ] using hentry

/-- A bond product supported on a one-site sector remains supported on that
sector after taking any nonempty prefix marginal of a chain of length at least
two.

The proof uses only projection idempotence, `bond_supported`, and
`realizes_mpo`; it does not use the saturated area law or zero correlation
length.  Thus it is independent of the BNT projectors whose current
construction uses saturated-area-law input.

Source: CPSV16, Definition 4.8, lines 838--850, and Appendix C.2,
Proposition `prop4to2`, lines 1801--1808. -/
theorem OrthogonalCommutingSectorFamily.firstSiteMatrix_mul_reducedBlockState
    {K : (s : Fin g) → MPOTensor d (dim s)}
    (F : OrthogonalCommutingSectorFamily K) (s : Fin g)
    {N L : ℕ} (hN : 2 ≤ N) (hL : L + 1 ≤ N) :
    firstSiteMatrix (F.projection s) L *
        reducedBlockState (K s) N (L + 1) hL =
      reducedBlockState (K s) N (L + 1) hL := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  apply firstSiteMatrix_mul_reducedBlockState_of_mul_normalizedMPO
  simp only [normalizedMPO, Matrix.mul_smul,
    F.firstSiteMatrix_mul_mpo s n (by omega)]

/-- The exact finite sum of orthogonally supported commuting sectors satisfies
the saturated area law when every sector does.

This is the final local direct-sum argument in CPSV16, Appendix C.2.
Sectorwise SAL is an explicit hypothesis: this theorem neither derives it from
the commuting-bond form nor invokes zero correlation length.  In particular,
the construction of the sector family must be independent of any SAL-derived
projectors.

**Scope restriction (exact local sum):** The full MPO is assumed to be the
exact all-positive-length sum of its sectors with positive multiplicities.
This is documented in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`.

Source: CPSV16, Definition 4.8, lines 838--850, and Appendix C.2,
Proposition `prop4to2`, lines 1801--1808. -/
theorem isSAL_of_orthogonalCommutingSectorFamily
    (M : MPOTensor d D) (K : (s : Fin g) → MPOTensor d (dim s))
    (multiplicity : Fin g → ℕ) [Nonempty (Fin g)]
    (hmultiplicity : ∀ s, 0 < multiplicity s)
    (F : OrthogonalCommutingSectorFamily K)
    (hM : ∀ (N : ℕ), 0 < N →
      mpo M N = ∑ s : Fin g, (multiplicity s : ℂ) • mpo (K s) N)
    (hSectorSAL : ∀ s, IsSAL (K s)) :
    IsSAL M := by
  exact isSAL_of_localOrthogonalSum M K multiplicity F.projection
    hmultiplicity F.projection_isOrthogonal
    (fun hst ↦ F.projection_orthogonal hst) hM
    (fun s _ _ hN hL ↦
      F.firstSiteMatrix_mul_reducedBlockState s hN hL)
    hSectorSAL

/-- The BNT all-positive-length decomposition satisfies the saturated area law
when its absorbed normal representatives do and an independently constructed
orthogonal commuting sector family realizes those representatives.

The exact sum is the established BNT identity, and positivity of its
multiplicities is `S.copies_pos`.  Sectorwise SAL remains an explicit
hypothesis.  In particular, this result does not derive single-sector SAL from
the commuting-bond form and does not construct the sector projections from
SAL; either step would make the outer argument circular.

**Scope restriction (conditional sector SAL):** This theorem proves only the
outer BNT implication.  It does not complete the single-sector implication in
Proposition `prop4to2`.  This is documented in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`.

Source: CPSV16, Appendix C.2, lines 1660--1665 and Proposition `prop4to2`,
lines 1801--1808. -/
theorem isSAL_of_commonWeightAbsorbedBasisMPOTensor_of_orthogonalCommutingSectorFamily
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    [Nonempty (Fin S.basisCount)]
    (F : OrthogonalCommutingSectorFamily
      (fun s ↦ commonWeightAbsorbedBasisMPOTensor S hWeight s))
    (hSectorSAL : ∀ s,
      IsSAL (commonWeightAbsorbedBasisMPOTensor S hWeight s)) :
    IsSAL M := by
  exact isSAL_of_orthogonalCommutingSectorFamily M
    (fun s ↦ commonWeightAbsorbedBasisMPOTensor S hWeight s)
    S.copies S.copies_pos F
    (fun _ hN ↦
      mpo_eq_sum_copies_smul_commonWeightAbsorbedBasisMPOTensor
        M S hM hWeight hN)
    hSectorSAL

end MPOTensor
