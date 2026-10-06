/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.PermutationGates
import TNLean.MPS.Preparation.QuantitativeUnitaryGates
import TNLean.MPS.Preparation.ArbitrarySiteGateEmbedding

/-!
# Reversible conjunction of zero-register tests

A register of `a` data sites is followed by `a` scratch sites. Starting
with zero scratch, controlled shifts successively record whether the
first one, two, and subsequent data sites are all zero. The shifts are
permutations on the entire configuration space, so their inverses are
valid on every logical input. This is the reversible conjunction used
in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix MPSTensor

namespace MPSPreparation

variable {d a : ℕ} [NeZero d]

/-- All data coordinates before the cutoff are zero. Source: the initialized
register reflection in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def zeroPrefixTest (x : Cfg d a) (k : ℕ) : Prop :=
  ∀ i : Fin a, i.val < k → x i = 0

/-- The Boolean value of a prefix zero test, encoded in levels zero and one.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def zeroPrefixBit (x : Cfg d a) (k : ℕ) : Fin d := by
  classical
  exact if zeroPrefixTest x k then 1 else 0

/-- The preceding scratch coordinate; at the first step it is unused.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def zeroConjunctionPrev (j : Fin a) : Fin a :=
  ⟨j.val - 1, (Nat.sub_le _ _).trans_lt j.isLt⟩

/-- The controlled increment at step `j` reads its data coordinate and,
except at the first step, the preceding scratch coordinate. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def zeroConjunctionIncrement (j : Fin a) (z : Cfg d (a + a)) : Fin d :=
  if z (Fin.castAdd a j) = 0 ∧
      (j.val = 0 ∨ z (Fin.natAdd a (zeroConjunctionPrev j)) = 1) then 1 else 0

private theorem castAdd_ne_natAdd (i j : Fin a) : Fin.castAdd a i ≠ Fin.natAdd a j := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

/-- The increment does not depend on the scratch coordinate it changes.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroConjunctionIncrement_update (j : Fin a) (z : Cfg d (a + a)) (c : Fin d) :
    zeroConjunctionIncrement j (Function.update z (Fin.natAdd a j) c) =
      zeroConjunctionIncrement j z := by
  classical
  by_cases hj : j.val = 0
  · simp only [zeroConjunctionIncrement, Function.update_of_ne (castAdd_ne_natAdd j j),
      hj, true_or, and_true]
  · have hprev : Fin.natAdd a (zeroConjunctionPrev j) ≠ Fin.natAdd a j := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_natAdd, zeroConjunctionPrev] at hval
      omega
    simp only [zeroConjunctionIncrement, Function.update_of_ne (castAdd_ne_natAdd j j),
      Function.update_of_ne hprev]

/-- One reversible controlled shift writes the next conjunction into its
scratch coordinate. It is defined on all configurations. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def zeroConjunctionStep (j : Fin a) : Equiv.Perm (Cfg d (a + a)) :=
  shiftPerm (Fin.natAdd a j) (zeroConjunctionIncrement j)
    (zeroConjunctionIncrement_update j)

/-- Forward composition of the first `k` controlled shifts. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def zeroConjunctionPerm : ℕ → Equiv.Perm (Cfg d (a + a))
  | 0 => 1
  | k + 1 => if h : k < a then zeroConjunctionStep ⟨k, h⟩ * zeroConjunctionPerm k
      else zeroConjunctionPerm k

/-- The expected configuration after the first `k` conjunction steps.
Data are retained, completed scratch sites hold their prefix tests, and
remaining scratch sites are zero. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def zeroConjunctionState (x : Cfg d a) (k : ℕ) : Cfg d (a + a) :=
  Fin.append x (fun j ↦ if j.val < k then zeroPrefixBit x (j.val + 1) else 0)

private theorem zeroPrefixTest_succ (x : Cfg d a) (j : Fin a) :
    zeroPrefixTest x (j.val + 1) ↔ zeroPrefixTest x j.val ∧ x j = 0 := by
  constructor
  · intro h
    exact ⟨fun i hi ↦ h i (by omega), h j (by omega)⟩
  · rintro ⟨h, hj⟩ i hi
    by_cases hij : i = j
    · simpa [hij] using hj
    · exact h i (by have := i.isLt; have := j.isLt; have := Fin.val_injective.ne hij; omega)

/-- The encoded prefix test equals one exactly when every tested input is
zero. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroPrefixBit_eq_one (hd : 2 ≤ d) (x : Cfg d a) (k : ℕ) :
    zeroPrefixBit x k = 1 ↔ zeroPrefixTest x k := by
  have hone : (1 : Fin d) ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega
  classical
  by_cases h : zeroPrefixTest x k <;> simp [zeroPrefixBit, h, hone.symm]

private theorem zeroConjunctionIncrement_state (hd : 2 ≤ d) (x : Cfg d a) (j : Fin a) :
    zeroConjunctionIncrement j (zeroConjunctionState x j.val) =
      zeroPrefixBit x (j.val + 1) := by
  classical
  have hcond : (j.val = 0 ∨
      (if (zeroConjunctionPrev j).val < j.val then
        zeroPrefixBit x ((zeroConjunctionPrev j).val + 1) else 0) = 1) ↔
      zeroPrefixTest x j.val := by
    by_cases hj : j.val = 0
    · simp [hj, zeroPrefixTest]
    · have hlt : (zeroConjunctionPrev j).val < j.val := by
        dsimp [zeroConjunctionPrev]
        omega
      have hsucc : (zeroConjunctionPrev j).val + 1 = j.val := by
        dsimp [zeroConjunctionPrev]
        omega
      simp [hj, hlt, hsucc, zeroPrefixBit_eq_one hd]
  simp only [zeroConjunctionIncrement, zeroConjunctionState, Fin.append_left,
    Fin.append_right]
  have hiff : (x j = 0 ∧ (j.val = 0 ∨
      (if (zeroConjunctionPrev j).val < j.val then
        zeroPrefixBit x ((zeroConjunctionPrev j).val + 1) else 0) = 1)) ↔
      zeroPrefixTest x (j.val + 1) := by
    rw [hcond, zeroPrefixTest_succ]
    exact and_comm
  by_cases h : zeroPrefixTest x (j.val + 1)
  · rw [ite_eq_left (hiff.mpr h)]
    simp only [zeroPrefixBit, h, ite_true]
  · rw [ite_eq_right (fun hc ↦ h (hiff.mp hc))]
    simp only [zeroPrefixBit, h, ite_false]

/-- Each controlled shift advances the conjunction invariant. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroConjunctionStep_state (hd : 2 ≤ d) (x : Cfg d a) (j : Fin a) :
    zeroConjunctionStep j (zeroConjunctionState x j.val) =
      zeroConjunctionState x (j.val + 1) := by
  classical
  funext p
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) p
  · change Function.update (zeroConjunctionState x j.val) (Fin.natAdd a j)
        ((zeroConjunctionState x j.val) (Fin.natAdd a j) +
          zeroConjunctionIncrement j (zeroConjunctionState x j.val)) (Fin.castAdd a i) = _
    rw [Function.update_of_ne (castAdd_ne_natAdd i j)]
    simp only [zeroConjunctionState, Fin.append_left]
  · by_cases hij : i = j
    · subst i
      change Function.update (zeroConjunctionState x j.val) (Fin.natAdd a j)
        ((zeroConjunctionState x j.val) (Fin.natAdd a j) +
          zeroConjunctionIncrement j (zeroConjunctionState x j.val)) (Fin.natAdd a j) = _
      rw [Function.update_self, zeroConjunctionIncrement_state hd]
      simp only [zeroConjunctionState, Fin.append_right, lt_self_iff_false,
        Nat.lt_succ_self, ite_false, ite_true, zero_add]
    · have hsites : Fin.natAdd a i ≠ Fin.natAdd a j := by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_natAdd] at hval
        exact hij (Fin.ext (by omega))
      have hcut : (i.val < j.val) ↔ i.val < j.val + 1 := by
        have := Fin.val_injective.ne hij
        omega
      change Function.update (zeroConjunctionState x j.val) (Fin.natAdd a j)
        ((zeroConjunctionState x j.val) (Fin.natAdd a j) +
          zeroConjunctionIncrement j (zeroConjunctionState x j.val)) (Fin.natAdd a i) = _
      rw [Function.update_of_ne hsites]
      simp only [zeroConjunctionState, Fin.append_right, hcut]

/-- On every data configuration with zero scratch, the controlled-shift
network computes all prefix conjunctions exactly. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroConjunctionPerm_apply_clean (hd : 2 ≤ d) (x : Cfg d a) :
    ∀ k, k ≤ a → zeroConjunctionPerm k (Fin.append x 0) = zeroConjunctionState x k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [zeroConjunctionPerm, Equiv.Perm.coe_one, id_eq, zeroConjunctionState,
      Nat.not_lt_zero, ite_false]
    rfl
  | succ k ih =>
    intro hk
    have hka : k < a := by omega
    simp only [zeroConjunctionPerm, hka, dite_true, Equiv.Perm.coe_mul,
      Function.comp_apply, ih (by omega)]
    exact zeroConjunctionStep_state hd x ⟨k, hka⟩


/-- The full register on which one conjunction step is supported. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def zeroConjunctionStepSites (j : Fin a) : Set (Fin (a + a)) :=
  {Fin.castAdd a j, Fin.natAdd a (zeroConjunctionPrev j), Fin.natAdd a j}

/-- Each controlled shift changes and reads at most three sites. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroConjunctionStep_isLocalPerm (j : Fin a) :
    IsLocalPerm (zeroConjunctionStepSites j) (zeroConjunctionStep (d := d) j) := by
  apply isLocalPerm_shiftPerm (by simp [zeroConjunctionStepSites])
  intro x y hxy
  simp only [zeroConjunctionIncrement,
    hxy (Fin.castAdd a j) (by simp [zeroConjunctionStepSites]),
    hxy (Fin.natAdd a (zeroConjunctionPrev j)) (by simp [zeroConjunctionStepSites])]

private theorem zeroConjunctionStep_isLocalPerm_first (j : Fin a) (hj : j.val = 0) :
    IsLocalPerm {Fin.castAdd a j, Fin.natAdd a j} (zeroConjunctionStep (d := d) j) := by
  apply isLocalPerm_shiftPerm (by simp)
  intro x y hxy
  simp only [zeroConjunctionIncrement, hj, true_or, and_true,
    hxy (Fin.castAdd a j) (by simp)]

/-- A uniform neighboring-pair gate budget for a three-site conjunction
step after routing. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def zeroConjunctionStepGateCount (d a : ℕ) : ℕ :=
  (38 * (d ^ 3) ^ 6 + 1) * (2 * (a + a))

/-- Each conjunction step admits an actual neighboring-pair circuit with
a gate budget linear in the full register size at fixed local dimension.
No circuit decomposition is supplied as a premise. Source: the synthesis
and reflection construction in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_zeroConjunctionStep (hd : 2 ≤ d) (j : Fin a) :
    IsPairProduct d (a + a) (zeroConjunctionStepGateCount d a)
      ((zeroConjunctionStep j).permMatrix ℂ) := by
  classical
  have hu := Equiv.Perm.permMatrix_mem_unitaryGroup (zeroConjunctionStep (d := d) j)
  by_cases hj : j.val = 0
  · have hs :=
      (zeroConjunctionStep_isLocalPerm_first (d := d) j hj).permMatrix_mem_supportedOperators
    have hpair := isPairProduct_of_mem_supportedOperators_pair (by omega)
      (castAdd_ne_natAdd j j) hu hs
    exact hpair.mono (by
      dsimp [zeroConjunctionStepGateCount]
      exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  · let e : Fin 3 → Fin (a + a) :=
      ![Fin.castAdd a j, Fin.natAdd a (zeroConjunctionPrev j), Fin.natAdd a j]
    have he : Function.Injective e := by
      intro u v huv
      fin_cases u <;> fin_cases v <;> try rfl
      all_goals
        have hval := congrArg Fin.val huv
        norm_num [e, zeroConjunctionPrev] at hval
        omega
    have hrange : Set.range e = zeroConjunctionStepSites j := by
      ext p
      simp only [e, zeroConjunctionStepSites, Matrix.range_cons, Matrix.range_empty,
        Set.union_empty, Set.singleton_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    have hs : (zeroConjunctionStep j).permMatrix ℂ ∈ supportedOperators d (Set.range e) := by
      rw [hrange]
      exact (zeroConjunctionStep_isLocalPerm j).permMatrix_mem_supportedOperators
    obtain ⟨X, hX⟩ := exists_embedOp_eq_of_mem_supportedOperators he hs
    have hXu := mem_unitary_of_embedOp_mem_unitary he (by omega) (hX ▸ hu)
    have hlocal := isPairProduct_le_hilbertDimension_pow hd (by omega : 2 ≤ 3) hXu
    rw [hX]
    exact (hlocal.embedOp_injective (by omega) he).mono (by
      dsimp [zeroConjunctionStepGateCount]
      exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _))

/-- The first `k` reversible conjunction steps have a circuit of at most
`k` times the one-step budget. This is an actual neighboring-pair circuit,
not a numerical recurrence assumption. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_zeroConjunctionPerm (hd : 2 ≤ d) :
    ∀ k, IsPairProduct d (a + a) (k * zeroConjunctionStepGateCount d a)
      ((zeroConjunctionPerm (d := d) (a := a) k).permMatrix ℂ) := by
  intro k
  induction k with
  | zero => simpa [zeroConjunctionPerm] using IsPairProduct.one (d := d) (n := a + a) 0
  | succ k ih =>
    rw [zeroConjunctionPerm]
    split_ifs with hk
    · rw [Matrix.permMatrix_mul]
      simpa only [Nat.succ_mul] using ih.mul (isPairProduct_zeroConjunctionStep hd ⟨k, hk⟩)
    · exact ih.mono (Nat.mul_le_mul_right _ (by omega))

end MPSPreparation
