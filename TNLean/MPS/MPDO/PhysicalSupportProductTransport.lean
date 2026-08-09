/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.KroneckerFactorPositivity
import TNLean.MPS.MPDO.PhysicalSupportBondCommutativity

/-!
# Finite-chain products on an isometric physical support

This file transports the complete periodic product of a restricted two-site
bond through its physical-support isometry.  All statements concern chains of
length at least two.  In particular, multiplicativity is needed only for a
nonempty bond list; the single-Kraus map of a rectangular isometry is not
incorrectly treated as unital.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Proposition C.8 and equation `generateMPDO`, lines 1571--1593
  and 1733--1770
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor

variable {d e D : ℕ}

open PhysicalSectorFactorization

private theorem singleKrausMap_kronecker
    {a b c f : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype f]
    (A : Matrix a b ℂ) (C : Matrix c f ℂ)
    (X : Matrix b b ℂ) (Y : Matrix f f ℂ) :
    singleKrausMap (A ⊗ₖ C) (X ⊗ₖ Y) =
      singleKrausMap A X ⊗ₖ singleKrausMap C Y := by
  simp only [singleKrausMap_apply, Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

private theorem singleKrausMap_mul_isometry
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (V : Matrix a b ℂ) (hV : Vᴴ * V = 1)
    (X Y : Matrix b b ℂ) :
    singleKrausMap V (X * Y) =
      singleKrausMap V X * singleKrausMap V Y := by
  simp only [singleKrausMap_apply, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ V, hV]
  simp

private theorem finKronecker_mul {N : ℕ}
    (A B : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    Matrix.finKronecker A * Matrix.finKronecker B =
      Matrix.finKronecker (fun n ↦ A n * B n) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, Matrix.finKronecker_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum
    (fun _ : Fin N ↦ (Finset.univ : Finset (Fin d)))
    (fun n z ↦ A n (x n) z * B n z (y n))]

/-- Isometric conjugation preserves the product of a nonempty list.  No
coisometry, and hence no unitality assertion, is used. -/
theorem singleKrausMap_list_prod_of_ne_nil
    {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b]
    (V : Matrix a b ℂ) (hV : Vᴴ * V = 1)
    (l : List (Matrix b b ℂ)) (hl : l ≠ []) :
    singleKrausMap V l.prod = (l.map (singleKrausMap V)).prod := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons X l ih =>
      cases l with
      | nil => simp
      | cons Y l =>
          rw [List.prod_cons, List.map_cons, List.prod_cons,
            singleKrausMap_mul_isometry V hV]
          exact congrArg (singleKrausMap V X * ·)
            (ih (by simp))

private def cyclicShiftEquiv (N : ℕ) (i : Fin N) : Fin N ≃ Fin N where
  toFun k := ⟨(i.val + k.val) % N, Nat.mod_lt _ (Fin.pos i)⟩
  invFun k := ⟨(k.val + N - i.val) % N, Nat.mod_lt _ (Fin.pos i)⟩
  left_inv k := by
    apply Fin.ext
    exact MPSTensor.offset_mod_eq i.isLt k.isLt
  right_inv k := by
    apply Fin.ext
    exact MPSTensor.add_offset_mod_eq i.isLt k.isLt

private def cyclicWindowIndexEquiv (L N : ℕ) (hLN : L ≤ N) (i : Fin N) :
    Fin L ⊕ Fin (N - L) ≃ Fin N :=
  finSumFinEquiv |>.trans (finCongr (Nat.add_sub_of_le hLN)) |>.trans
    (cyclicShiftEquiv N i)

@[simp] private theorem cyclicWindowIndexEquiv_inl
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) (r : Fin L) :
    cyclicWindowIndexEquiv L N hLN i (Sum.inl r) =
      ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ := rfl

@[simp] private theorem cyclicWindowIndexEquiv_inr
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) (r : Fin (N - L)) :
    cyclicWindowIndexEquiv L N hLN i (Sum.inr r) =
      ⟨(i.val + L + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ := by
  apply Fin.ext
  change (i.val + (L + r.val)) % N = (i.val + L + r.val) % N
  congr 1
  omega

private theorem prod_cyclicWindow_complement
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) (f : Fin N → ℂ) :
    (∏ n : Fin N, f n) =
      (∏ r : Fin L,
        f ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩) *
        (∏ r : Fin (N - L),
          f ⟨(i.val + L + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩) := by
  rw [Fintype.prod_equiv
    (cyclicWindowIndexEquiv L N hLN i).symm f
    (fun x ↦ f (cyclicWindowIndexEquiv L N hLN i x))
    (fun n ↦ by simp)]
  rw [Fintype.prod_sum_type]
  simp only [cyclicWindowIndexEquiv_inl, cyclicWindowIndexEquiv_inr]

private theorem reindex_sitewisePhysicalMatrix_windowComplement
    (V : Matrix (Fin d) (Fin e) ℂ) {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    Matrix.reindex (windowComplementEquiv (d := d) 2 N hN i)
        (windowComplementEquiv (d := e) 2 N hN i)
        (sitewisePhysicalMatrix V N) =
      sitewisePhysicalMatrix V 2 ⊗ₖ sitewisePhysicalMatrix V (N - 2) := by
  ext ⟨x, u⟩ ⟨y, v⟩
  let ed := windowComplementEquiv (d := d) 2 N hN i
  let ee := windowComplementEquiv (d := e) 2 N hN i
  let s := ed.symm (x, u)
  let t := ee.symm (y, v)
  have hx : MPSTensor.extractWindow 2 i s = x :=
    congrArg Prod.fst (ed.apply_symm_apply (x, u))
  have hy : MPSTensor.extractWindow 2 i t = y :=
    congrArg Prod.fst (ee.apply_symm_apply (y, v))
  have hu : (fun r ↦ s ⟨(i.val + 2 + r.val) % N,
      Nat.mod_lt _ (Fin.pos i)⟩) = u :=
    congrArg Prod.snd (ed.apply_symm_apply (x, u))
  have hv : (fun r ↦ t ⟨(i.val + 2 + r.val) % N,
      Nat.mod_lt _ (Fin.pos i)⟩) = v :=
    congrArg Prod.snd (ee.apply_symm_apply (y, v))
  change (∏ n : Fin N, V (s n) (t n)) = _
  rw [prod_cyclicWindow_complement 2 N hN i]
  simp only [MPSTensor.extractWindow] at hx hy
  simp only [sitewisePhysicalMatrix, Matrix.kroneckerMap_apply]
  apply congrArg₂ (fun a b : ℂ ↦ a * b)
  · apply Finset.prod_congr rfl
    intro r _
    rw [congrFun hx r, congrFun hy r]
  · apply Finset.prod_congr rfl
    intro r _
    rw [congrFun hu r, congrFun hv r]

private noncomputable def cyclicBondProjectionFactor
    (P : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (i n : Fin N) :
    Matrix (Fin d) (Fin d) ℂ :=
  if (n.val + N - i.val) % N < 2 then P else 1

private theorem embed_twoSiteSectorProjection_eq_finKronecker
    (P : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    embedLocalOperator (d := d) 2 N hN i (twoSiteSectorProjection P) =
      Matrix.finKronecker (fun n ↦ cyclicBondProjectionFactor P i n) := by
  rw [← sitewisePhysicalMatrix_two_eq_twoSiteSectorProjection]
  ext σ τ
  simp only [embedLocalOperator_apply, sitewisePhysicalMatrix,
    Matrix.finKronecker_apply]
  by_cases hAgree : AgreesOutsideWindow (d := d) 2 hN i σ τ
  · rw [if_pos hAgree, prod_cyclicWindow_complement 2 N hN i]
    rw [agreesOutsideWindow_iff] at hAgree
    apply Eq.symm
    calc
      (∏ r : Fin 2,
          cyclicBondProjectionFactor P i
            ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩
            (σ ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩)
            (τ ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩)) *
          (∏ r : Fin (N - 2),
            cyclicBondProjectionFactor P i
              ⟨(i.val + 2 + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩
              (σ ⟨(i.val + 2 + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩)
              (τ ⟨(i.val + 2 + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩)) =
          (∏ r : Fin 2,
            P (σ ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩)
              (τ ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩)) * 1 := by
        congr 1
        · apply Finset.prod_congr rfl
          intro r _
          simp only [cyclicBondProjectionFactor]
          rw [MPSTensor.offset_mod_eq i.isLt
            (Nat.lt_of_lt_of_le r.isLt hN)]
          simp [r.isLt]
        · apply Finset.prod_eq_one
          intro r _
          simp only [cyclicBondProjectionFactor]
          have hoff :
              (((i.val + 2 + r.val) % N + N - i.val) % N) =
                2 + r.val := by
            simpa [Nat.add_assoc] using MPSTensor.offset_mod_eq i.isLt
              (by omega : 2 + r.val < N)
          rw [hoff]
          rw [if_neg (by omega)]
          simp only [Matrix.one_apply]
          rw [if_pos]
          exact (hAgree
            ⟨(i.val + 2 + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩
            (by rw [hoff]; omega)).symm
      _ = _ := by simp [MPSTensor.extractWindow]
  · rw [if_neg hAgree]
    rw [agreesOutsideWindow_iff] at hAgree
    push Not at hAgree
    obtain ⟨n, hn, hστ⟩ := hAgree
    apply Eq.symm
    apply Finset.prod_eq_zero (i := n) (Finset.mem_univ n)
    simp only [cyclicBondProjectionFactor]
    rw [if_neg (by omega), Matrix.one_apply, if_neg (Ne.symm hστ)]

private theorem finKronecker_list_prod_of_ne_nil {N : ℕ}
    (l : List (Fin N → Matrix (Fin d) (Fin d) ℂ)) (hl : l ≠ []) :
    (l.map Matrix.finKronecker).prod =
      Matrix.finKronecker (fun n ↦ (l.map fun A ↦ A n).prod) := by
  classical
  induction l with
  | nil => exact (hl rfl).elim
  | cons A l ih =>
      cases l with
      | nil => simp
      | cons B l =>
          rw [List.map_cons, List.prod_cons]
          rw [ih (by simp)]
          rw [finKronecker_mul]
          simp only [List.map_cons, List.prod_cons]

private theorem list_prod_eq_one_of_forall
    (l : List (Matrix (Fin d) (Fin d) ℂ)) (h : ∀ X ∈ l, X = 1) : l.prod = 1 := by
  induction l with
  | nil => simp
  | cons X l ih =>
      rw [List.prod_cons, h X (by simp), Matrix.one_mul]
      exact ih (fun Y hY ↦ h Y (by simp [hY]))

private theorem list_prod_eq_of_mem_idempotent
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P * P = P)
    (l : List (Matrix (Fin d) (Fin d) ℂ))
    (hvalues : ∀ X ∈ l, X = 1 ∨ X = P) (hmem : P ∈ l) :
    l.prod = P := by
  classical
  by_cases hPone : P = 1
  · subst P
    apply list_prod_eq_one_of_forall l
    intro X hX
    rcases hvalues X hX with hX1 | hX1 <;> exact hX1
  induction l with
  | nil => simp at hmem
  | cons X l ih =>
      have hX := hvalues X (by simp)
      rcases hX with hX | hX
      · subst X
        simp only [List.prod_cons, Matrix.one_mul]
        apply ih (fun Y hY ↦ hvalues Y (by simp [hY]))
        simpa [hPone] using hmem
      · subst X
        simp only [List.prod_cons]
        by_cases hPl : P ∈ l
        · rw [ih (fun Y hY ↦ hvalues Y (by simp [hY])) hPl, hP]
        · have hall : ∀ Y ∈ l, Y = 1 := by
            intro Y hY
            rcases hvalues Y (by simp [hY]) with hY1 | hYP
            · exact hY1
            · exact (hPl (hYP ▸ hY)).elim
          have hprod : l.prod = 1 := list_prod_eq_one_of_forall l hall
          rw [hprod, Matrix.mul_one]

private noncomputable def openBondProjectionProduct
    (P : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (hN : 2 ≤ N) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  (List.ofFn fun i : Fin (N - 1) ↦
    embedLocalOperator (d := d) 2 N hN ⟨i.val, by omega⟩
      (twoSiteSectorProjection P)).prod

private theorem openBondProjectionProduct_eq_sitewise
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P * P = P)
    {N : ℕ} (hN : 2 ≤ N) :
    openBondProjectionProduct P hN = sitewisePhysicalMatrix P N := by
  classical
  let factors : Fin (N - 1) → Fin N → Matrix (Fin d) (Fin d) ℂ :=
    fun i n ↦ cyclicBondProjectionFactor P ⟨i.val, by omega⟩ n
  have hlist :
      (List.ofFn fun i : Fin (N - 1) ↦
        embedLocalOperator (d := d) 2 N hN ⟨i.val, by omega⟩
          (twoSiteSectorProjection P)) =
        (List.ofFn factors).map Matrix.finKronecker := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact embed_twoSiteSectorProjection_eq_finKronecker P hN ⟨i.val, by omega⟩
  rw [openBondProjectionProduct, hlist]
  have hne : List.ofFn factors ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_ofFn]
    omega
  rw [finKronecker_list_prod_of_ne_nil _ hne]
  simp only [List.map_ofFn]
  change Matrix.finKronecker
      (fun n ↦ (List.ofFn fun i : Fin (N - 1) ↦ factors i n).prod) =
    Matrix.finKronecker (fun _ ↦ P)
  congr 1
  funext n
  apply list_prod_eq_of_mem_idempotent P hP
  · intro X hX
    rw [List.mem_ofFn] at hX
    obtain ⟨i, rfl⟩ := hX
    simp only [factors, cyclicBondProjectionFactor]
    split_ifs <;> simp
  · rw [List.mem_ofFn]
    by_cases hnlast : n.val < N - 1
    · refine ⟨⟨n.val, hnlast⟩, ?_⟩
      simp only [factors, cyclicBondProjectionFactor]
      have hoff : (n.val + N - n.val) % N = 0 := by
        rw [show n.val + N - n.val = N by omega, Nat.mod_self]
      rw [if_pos (by rw [hoff]; omega)]
    · refine ⟨⟨N - 2, by omega⟩, ?_⟩
      simp only [factors, cyclicBondProjectionFactor]
      have hn : n.val = N - 1 := by omega
      have hoff : (n.val + N - (N - 2)) % N = 1 := by
        rw [hn]
        rw [show N - 1 + N - (N - 2) = N + 1 by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : 1 < N)]
      rw [hoff, if_pos (by omega)]

private theorem list_prod_mul_eq_of_forall
    {n : Type*} [Fintype n] [DecidableEq n]
    (l : List (Matrix n n ℂ)) (X : Matrix n n ℂ)
    (h : ∀ A ∈ l, A * X = X) : l.prod * X = X := by
  induction l with
  | nil => simp
  | cons A l ih =>
      rw [List.prod_cons, Matrix.mul_assoc, ih (fun B hB ↦ h B (by simp [hB])),
        h A (by simp)]

private theorem list_prod_range_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (hQ : Q * Q = Q)
    (l : List (Matrix n n ℂ)) (hl : l ≠ [])
    (hcomm : ∀ A ∈ l, Q * A = A * Q) :
    (l.map fun A ↦ Q * A).prod = Q * l.prod := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons A l ih =>
      cases l with
      | nil => simp
      | cons B l =>
          rw [List.map_cons, List.prod_cons, ih (by simp)
            (fun C hC ↦ hcomm C (by simp [hC]))]
          calc
            (Q * A) * (Q * (B :: l).prod) =
                Q * (A * Q) * (B :: l).prod := by
              simp only [Matrix.mul_assoc]
            _ = Q * (Q * A) * (B :: l).prod := by
              rw [hcomm A (by simp)]
            _ = (Q * Q) * A * (B :: l).prod := by
              simp only [Matrix.mul_assoc]
            _ = Q * (A :: B :: l).prod := by
              rw [hQ]
              simp only [List.prod_cons, Matrix.mul_assoc]

namespace PhysicalSupportRestrictionData

variable {P : Matrix (Fin d) (Fin d) ℂ} {K : MPOTensor d D}

private theorem twoSiteSectorProjection_mul_liftedBond
    (F : PhysicalSupportRestrictionData P K)
    (B : Matrix (Fin 2 → Fin F.supportDim)
      (Fin 2 → Fin F.supportDim) ℂ) :
    twoSiteSectorProjection P * F.liftedBond B = F.liftedBond B := by
  rw [F.twoSiteSectorProjection_eq_lifted_range]
  simp only [liftedBond, singleKrausMap_apply, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
      (sitewisePhysicalMatrix F.inclusion 2)ᴴ
      (sitewisePhysicalMatrix F.inclusion 2),
    sitewisePhysicalMatrix_isometry F.inclusion F.inclusion_isometry 2,
    Matrix.one_mul]

private theorem liftedBondProduct_left_supported
    (F : PhysicalSupportRestrictionData P K)
    (data : TranslationInvariantBondData F.supportDim)
    {N : ℕ} (hN : 2 ≤ N) :
    sitewisePhysicalMatrix P N *
        (List.ofFn fun i : Fin N ↦
          embedLocalOperator (d := d) 2 N hN i
            (F.liftedBond data.bond)).prod =
      (List.ofFn fun i : Fin N ↦
        embedLocalOperator (d := d) 2 N hN i
          (F.liftedBond data.bond)).prod := by
  let A : Fin N → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
    fun i ↦ embedLocalOperator (d := d) 2 N hN i
      (F.liftedBond data.bond)
  let R : Fin (N - 1) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
    fun i ↦ embedLocalOperator (d := d) 2 N hN ⟨i.val, by omega⟩
      (twoSiteSectorProjection P)
  have hpair : (List.ofFn A).Pairwise Commute := by
    rw [List.pairwise_ofFn]
    intro i j _
    exact F.liftedTranslationInvariantBondData data |>.bond_comm
      hN ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
  have hRiAi (i : Fin (N - 1)) :
      R i * A ⟨i.val, by omega⟩ = A ⟨i.val, by omega⟩ := by
    simp only [R, A]
    rw [← embedLocalOperator_mul,
      F.twoSiteSectorProjection_mul_liftedBond]
  have hRiProduct (i : Fin (N - 1)) : R i * (List.ofFn A).prod =
      (List.ofFn A).prod := by
    let j : Fin N := ⟨i.val, by omega⟩
    have hmem : A j ∈ List.ofFn A := by
      rw [List.mem_ofFn]
      exact ⟨j, rfl⟩
    have hperm : List.Perm (List.ofFn A)
        (A j :: (List.ofFn A).erase (A j)) :=
      List.perm_cons_erase hmem
    have hprod := hperm.prod_eq' hpair
    rw [hprod]
    simp only [List.prod_cons]
    rw [← Matrix.mul_assoc, show R i * A j = A j from hRiAi i]
  have hRprod : (List.ofFn R).prod * (List.ofFn A).prod =
      (List.ofFn A).prod :=
    list_prod_mul_eq_of_forall _ _ (by
      intro X hX
      rw [List.mem_ofFn] at hX
      obtain ⟨i, rfl⟩ := hX
      exact hRiProduct i)
  have hP : P * P = P := by
    rw [← F.inclusion_range]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.inclusionᴴ F.inclusion,
      F.inclusion_isometry, Matrix.one_mul]
  have hR : (List.ofFn R).prod = sitewisePhysicalMatrix P N := by
    simpa [R, openBondProjectionProduct] using
      openBondProjectionProduct_eq_sitewise P hP hN
  simpa [A, hR] using hRprod

end PhysicalSupportRestrictionData


/-- The isometric image of one embedded restricted bond is its ambient lift
multiplied by the range projection on the complete chain.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 and equation
`generateMPDO`, lines 1571--1593 and 1733--1770. -/
theorem singleKrausMap_embedLocalOperator_eq_range_mul_lift
    (V : Matrix (Fin d) (Fin e) ℂ) (hV : Vᴴ * V = 1)
    {N : ℕ} (hN : 2 ≤ N) (i : Fin N)
    (B : Matrix (Fin 2 → Fin e) (Fin 2 → Fin e) ℂ) :
    singleKrausMap (sitewisePhysicalMatrix V N)
        (embedLocalOperator (d := e) 2 N hN i B) =
      singleKrausMap (sitewisePhysicalMatrix V N) 1 *
        embedLocalOperator (d := d) 2 N hN i
          (singleKrausMap (sitewisePhysicalMatrix V 2) B) := by
  let ed := windowComplementEquiv (d := d) 2 N hN i
  let ee := windowComplementEquiv (d := e) 2 N hN i
  apply (Matrix.reindex ed ed).injective
  change (Matrix.reindexLinearEquiv ℂ ℂ ed ed)
      (singleKrausMap (sitewisePhysicalMatrix V N)
        (embedLocalOperator (d := e) 2 N hN i B)) =
    (Matrix.reindexLinearEquiv ℂ ℂ ed ed)
      (singleKrausMap (sitewisePhysicalMatrix V N) 1 *
        embedLocalOperator (d := d) 2 N hN i
          (singleKrausMap (sitewisePhysicalMatrix V 2) B))
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ ed ed ed]
  simp only [Matrix.coe_reindexLinearEquiv]
  rw [Matrix.reindex_singleKrausMap ee ed,
    reindex_sitewisePhysicalMatrix_windowComplement,
    reindex_embedLocalOperator_windowComplement]
  change singleKrausMap
      (sitewisePhysicalMatrix V 2 ⊗ₖ sitewisePhysicalMatrix V (N - 2))
        (B ⊗ₖ (1 : Matrix (Fin (N - 2) → Fin e)
          (Fin (N - 2) → Fin e) ℂ)) = _
  rw [singleKrausMap_kronecker]
  have hone : Matrix.reindex ee ee
      (1 : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) = 1 := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [Matrix.reindex_apply]
    · have hne : ee.symm x ≠ ee.symm y := fun h ↦ hxy (ee.symm.injective h)
      simp [Matrix.reindex_apply, hxy, hne]
  rw [Matrix.reindex_singleKrausMap ee ed,
    reindex_sitewisePhysicalMatrix_windowComplement,
    reindex_embedLocalOperator_windowComplement, hone]
  simp only [singleKrausMap_apply, Matrix.mul_one,
    Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  have htwo := sitewisePhysicalMatrix_isometry V hV 2
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
      (sitewisePhysicalMatrix V 2)ᴴ (sitewisePhysicalMatrix V 2),
    htwo, Matrix.one_mul]
  simp

/-- Conjugation by a one-site unitary tensor power carries a complete periodic
bond product to the product of the conjugated two-site bonds.

Both unitary identities are stated explicitly: the first makes single-Kraus
conjugation multiplicative, while the second removes its range projection.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines 1581--1593. -/
theorem singleKrausMap_bondProduct_of_unitary
    (V : Matrix (Fin d) (Fin d) ℂ) (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1)
    {N : ℕ} (hN : 2 ≤ N) (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    singleKrausMap (sitewisePhysicalMatrix V N)
        (List.ofFn fun i : Fin N ↦ embedLocalOperator 2 N hN i B).prod =
      (List.ofFn fun i : Fin N ↦ embedLocalOperator 2 N hN i
        (singleKrausMap (sitewisePhysicalMatrix V 2) B)).prod := by
  have hW : (sitewisePhysicalMatrix V N)ᴴ * sitewisePhysicalMatrix V N = 1 :=
    sitewisePhysicalMatrix_isometry V hV N
  have hne : (List.ofFn fun i : Fin N ↦ embedLocalOperator 2 N hN i B) ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_ofFn]
    omega
  rw [singleKrausMap_list_prod_of_ne_nil _ hW _ hne, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  change singleKrausMap (sitewisePhysicalMatrix V N)
      (embedLocalOperator 2 N hN i B) = _
  rw [singleKrausMap_embedLocalOperator_eq_range_mul_lift V hV hN i B]
  simp only [singleKrausMap_apply, Matrix.mul_one]
  rw [sitewisePhysicalMatrix_mul_conjTranspose, hV']
  rw [sitewisePhysicalMatrix_one, Matrix.one_mul]

namespace PhysicalSupportRestrictionData

variable {P : Matrix (Fin d) (Fin d) ℂ} {K : MPOTensor d D}

/-- Isometric conjugation carries the complete restricted periodic bond
product to the complete product of the lifted ambient bond, for every chain
length at least two.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 and equation
`generateMPDO`, lines 1571--1593 and 1733--1770. -/
theorem singleKrausMap_bondProduct_eq_liftedBondProduct
    (F : PhysicalSupportRestrictionData P K)
    (data : TranslationInvariantBondData F.supportDim)
    {N : ℕ} (hN : 2 ≤ N) :
    singleKrausMap (sitewisePhysicalMatrix F.inclusion N)
        (List.ofFn fun i : Fin N ↦
          embedLocalOperator (d := F.supportDim) 2 N hN i data.bond).prod =
      (List.ofFn fun i : Fin N ↦
        embedLocalOperator (d := d) 2 N hN i
          (F.liftedBond data.bond)).prod := by
  let W := sitewisePhysicalMatrix F.inclusion N
  let Q := singleKrausMap W 1
  let X : Fin N → Matrix (Fin N → Fin F.supportDim)
      (Fin N → Fin F.supportDim) ℂ :=
    fun i ↦ embedLocalOperator (d := F.supportDim) 2 N hN i data.bond
  let A : Fin N → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
    fun i ↦ embedLocalOperator (d := d) 2 N hN i
      (F.liftedBond data.bond)
  have hW : Wᴴ * W = 1 :=
    sitewisePhysicalMatrix_isometry F.inclusion F.inclusion_isometry N
  have hQ : Q * Q = Q := by
    calc
      Q * Q = singleKrausMap W (1 * 1) :=
        (singleKrausMap_mul_isometry W hW 1 1).symm
      _ = Q := by simp [Q]
  have hmap : (List.ofFn X).map (singleKrausMap W) =
      List.ofFn (fun i ↦ Q * A i) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact singleKrausMap_embedLocalOperator_eq_range_mul_lift
      F.inclusion F.inclusion_isometry hN i data.bond
  have hQherm : Q.IsHermitian :=
    (Matrix.PosSemidef.one.mul_mul_conjTranspose_same W).1
  have hcommQ : ∀ C ∈ List.ofFn A, Q * C = C * Q := by
    intro C hC
    rw [List.mem_ofFn] at hC
    obtain ⟨i, rfl⟩ := hC
    have hleft := singleKrausMap_embedLocalOperator_eq_range_mul_lift
      F.inclusion F.inclusion_isometry hN i data.bond
    have hXpos : (X i).PosSemidef :=
      embedLocalOperator_posSemidef 2 hN i data.bond_pos
    have hφherm : (singleKrausMap W (X i)).IsHermitian :=
      (hXpos.mul_mul_conjTranspose_same W).1
    have hAherm : (A i).IsHermitian :=
      (embedLocalOperator_posSemidef 2 hN i
        (F.liftedBond_pos data.bond_pos)).1
    calc
      Q * A i = singleKrausMap W (X i) := hleft.symm
      _ = (singleKrausMap W (X i))ᴴ := hφherm.eq.symm
      _ = (Q * A i)ᴴ := congrArg Matrix.conjTranspose hleft
      _ = A i * Q := by
        rw [Matrix.conjTranspose_mul, hAherm.eq, hQherm.eq]
  have hQrange : Q = sitewisePhysicalMatrix P N := by
    simp only [Q, singleKrausMap_apply, Matrix.mul_one, W]
    rw [sitewisePhysicalMatrix_mul_conjTranspose, F.inclusion_range]
  have hne : List.ofFn X ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_ofFn]
    omega
  have hAne : List.ofFn A ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_ofFn]
    omega
  calc
    singleKrausMap W (List.ofFn X).prod =
        ((List.ofFn X).map (singleKrausMap W)).prod :=
      singleKrausMap_list_prod_of_ne_nil W hW _ hne
    _ = (List.ofFn fun i ↦ Q * A i).prod := congrArg List.prod hmap
    _ = Q * (List.ofFn A).prod := by
      have hm : (List.ofFn A).map (fun C ↦ Q * C) =
          List.ofFn (fun i ↦ Q * A i) := by
        rw [List.map_ofFn]
        apply congrArg List.ofFn
        funext i
        rfl
      rw [← hm]
      exact list_prod_range_mul Q hQ _ hAne hcommQ
    _ = (List.ofFn A).prod := by
      rw [hQrange]
      exact F.liftedBondProduct_left_supported data hN

/-- Eta-local structure on the restricted physical space extends through the
support isometry to eta-local structure on the ambient tensor.  The same
positive normalization scalar is retained at every chain length.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 and equation
`generateMPDO`, lines 1571--1593 and 1733--1770. -/
noncomputable def liftedEtaLocalStructureData
    (F : PhysicalSupportRestrictionData P K)
    (data : EtaLocalStructureData
      (PhysicalSectorFactorization.changePhysicalBasis F.inclusionᴴ K)) :
    EtaLocalStructureData K where
  bondData := F.liftedTranslationInvariantBondData data.bondData
  realizes_mpo := by
    intro N hN
    obtain ⟨c, hc, hreal⟩ := data.realizes_mpo N hN
    refine ⟨c, hc, ?_⟩
    change mpo K N = (c : ℂ) •
      (List.ofFn fun i : Fin N ↦
        embedLocalOperator (d := d) 2 N hN i
          (F.liftedBond data.bondData.bond)).prod
    have hmpo : mpo K N =
        singleKrausMap (sitewisePhysicalMatrix F.inclusion N)
          (mpo (PhysicalSectorFactorization.changePhysicalBasis
            F.inclusionᴴ K) N) := by
      rw [singleKrausMap_sitewisePhysicalMatrix_mpo, F.reembed]
    change mpo (PhysicalSectorFactorization.changePhysicalBasis
      F.inclusionᴴ K) N = (c : ℂ) •
        (List.ofFn fun i : Fin N ↦
          embedLocalOperator (d := F.supportDim) 2 N hN i
            data.bondData.bond).prod at hreal
    rw [hmpo, hreal]
    rw [(singleKrausMap
      (sitewisePhysicalMatrix F.inclusion N)).map_smul]
    rw [F.singleKrausMap_bondProduct_eq_liftedBondProduct data.bondData hN]

/-- The lifted eta-local structure has the isometrically included restricted
bond as its local bond. -/
@[simp] theorem liftedEtaLocalStructureData_bond
    (F : PhysicalSupportRestrictionData P K)
    (data : EtaLocalStructureData
      (PhysicalSectorFactorization.changePhysicalBasis F.inclusionᴴ K)) :
    (F.liftedEtaLocalStructureData data).bondData.bond =
      F.liftedBond data.bondData.bond := rfl

/-- A positive physical-sector factorization on the restricted physical space
gives a positive commuting bond for the ambient tensor supported on the tensor
square of the prescribed one-site projection. Its periodic product is exactly
the ambient MPO at every length at least two.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl`, `Appetakhetc`,
`PjKiPj`, and `generateMPDO`, lines 1383--1450 and 1680--1770. -/
theorem exists_etaLocalStructureData_lifted_supported_of_physicalSectorFactorization
    (F : PhysicalSupportRestrictionData P K)
    (G : PhysicalSectorFactorization
      (PhysicalSectorFactorization.changePhysicalBasis F.inclusionᴴ K))
    (hη : ∀ k h, (G.neighboringOperator k h).PosSemidef) :
    ∃ data : EtaLocalStructureData K,
      twoSiteSectorProjection P * data.bondData.bond *
          twoSiteSectorProjection P = data.bondData.bond ∧
      ∀ N (hN : 2 ≤ N),
        mpo K N = (data.bondData.toCommutingFormData hN).product := by
  let restrictedData := G.etaLocalStructureData hη
  let data := F.liftedEtaLocalStructureData restrictedData
  refine ⟨data, F.liftedBond_supported restrictedData.bondData.bond, ?_⟩
  intro N hN
  change mpo K N =
    ((F.liftedTranslationInvariantBondData restrictedData.bondData).toCommutingFormData
      hN).product
  have hmpo : mpo K N =
      singleKrausMap (sitewisePhysicalMatrix F.inclusion N)
        (mpo (PhysicalSectorFactorization.changePhysicalBasis
          F.inclusionᴴ K) N) := by
    rw [singleKrausMap_sitewisePhysicalMatrix_mpo, F.reembed]
  rw [hmpo]
  change singleKrausMap (sitewisePhysicalMatrix F.inclusion N)
      (mpo (PhysicalSectorFactorization.changePhysicalBasis
        F.inclusionᴴ K) N) =
    (List.ofFn fun i : Fin N ↦
      embedLocalOperator (d := d) 2 N hN i
        (F.liftedBond restrictedData.bondData.bond)).prod
  rw [show mpo (PhysicalSectorFactorization.changePhysicalBasis
      F.inclusionᴴ K) N =
      (List.ofFn fun i : Fin N ↦
        embedLocalOperator (d := F.supportDim) 2 N hN i
          restrictedData.bondData.bond).prod by
    exact G.mpo_eq_product_physicalBond hN]
  exact F.singleKrausMap_bondProduct_eq_liftedBondProduct
    restrictedData.bondData hN

/-- Proposition C.8 on the injective physical support gives an eta-local
commuting-product realization of the ambient tensor whose bond remains in the
prescribed two-site sector.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`) and
equations `PjKiPj` and `generateMPDO`, lines 1571--1593 and 1733--1770. -/
theorem exists_etaLocalStructureData_lifted_supported
    (F : PhysicalSupportRestrictionData P K) (hSAL : IsSAL K) :
    ∃ data : EtaLocalStructureData K,
      twoSiteSectorProjection P * data.bondData.bond *
          twoSiteSectorProjection P = data.bondData.bond ∧
      ∀ N (hN : 2 ≤ N),
        mpo K N = (data.bondData.toCommutingFormData hN).product := by
  obtain ⟨G, hG⟩ := exists_positive_physicalSectorFactorization_of_isSAL
    (PhysicalSectorFactorization.changePhysicalBasis F.inclusionᴴ K)
    F.restricted_injective (F.restricted_isSAL hSAL)
  exact F.exists_etaLocalStructureData_lifted_supported_of_physicalSectorFactorization
    G hG

end PhysicalSupportRestrictionData

end MPOTensor
