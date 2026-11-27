/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Kronecker.KroneckerFactorPositivity
import QICLean.Channel.KrausMap.SingleKrausPositivity
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct
import QICLean.Analysis.FunctionalCalculus.FiniteKroneckerPowers
import TNLean.MPS.FundamentalTheorem.PhysicalSupport.PhysicalSupportBondCommutativity
import TNLean.MPS.Operator.Interaction.PhysicalGibbsEmbedding
import TNLean.MPS.Tensor.CyclicWindowIndex
import TNLean.MPS.Operator.PhysicalSector.CommutingBondEtaCyclicCore
import QICLean.Algebra.Kronecker.PiKroneckerProducts

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

## Cyclic eta decomposition for a commuting bond

This file combines the dependency-neutral cyclic transport with the physical-support
product transport to obtain the finite-chain decomposition of a commuting form.
-/

section

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor

variable {d e D : ℕ}

open PhysicalSectorFactorization

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
            Matrix.singleKrausMap_mul_of_isometry V hV]
          exact congrArg (singleKrausMap V X * ·)
            (ih (by simp))

private noncomputable def cyclicBondProjectionFactor
    (P : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (i n : Fin N) :
    Matrix (Fin d) (Fin d) ℂ :=
  if (n.val + N - i.val) % N < 2 then P else 1

private theorem placeAlong_twoSiteSectorProjection_eq_piKronecker
    (P : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
        (twoSiteSectorProjection P) =
      Matrix.piKronecker (fun n ↦ cyclicBondProjectionFactor P i n) := by
  rw [← piKronecker_two_eq_twoSiteSectorProjection]
  ext σ τ
  rw [ManyBody.placeAlong_apply, ← MPSTensor.extractWindow_eq_comp_ringWindow hN,
    ← MPSTensor.extractWindow_eq_comp_ringWindow hN]
  simp only [Matrix.piKronecker_apply, Matrix.piKronecker_apply]
  by_cases hAgree : ∀ v, (∀ u, ManyBody.ringWindow hN i u ≠ v) → σ v = τ v
  · rw [ite_eq_left hAgree, MPSTensor.prod_cyclicWindow_complement 2 N hN i]
    rw [MPSTensor.forall_ringWindow_ne_imp_iff] at hAgree
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
          rw [ite_eq_right (by omega)]
          simp only [Matrix.one_apply]
          rw [ite_eq_left]
          exact (hAgree
            ⟨(i.val + 2 + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩
            (by rw [hoff]; omega)).symm
      _ = _ := by simp [MPSTensor.extractWindow]
  · rw [ite_eq_right hAgree]
    rw [MPSTensor.forall_ringWindow_ne_imp_iff] at hAgree
    push Not at hAgree
    obtain ⟨n, hn, hστ⟩ := hAgree
    apply Eq.symm
    apply Finset.prod_eq_zero (i := n) (Finset.mem_univ n)
    simp only [cyclicBondProjectionFactor]
    rw [ite_eq_right (by omega), Matrix.one_apply, ite_eq_right (Ne.symm hστ)]

/-- Translates of a tensor-square one-site operator commute. The one-site
operator need not be a projection: at each position the two factors are
copies of that same operator or the identity. -/
theorem embed_twoSiteSectorProjection_commute
    (P : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (hN : 2 ≤ N) (i j : Fin N) :
    Commute (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
        (twoSiteSectorProjection P))
      (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN j)
        (twoSiteSectorProjection P)) := by
  unfold Commute SemiconjBy
  simp only [placeAlong_twoSiteSectorProjection_eq_piKronecker, Matrix.piKronecker_mul]
  congr 1
  funext n
  simp only [cyclicBondProjectionFactor]
  split_ifs <;> simp

private theorem list_prod_eq_of_mem_idempotent
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P * P = P)
    (l : List (Matrix (Fin d) (Fin d) ℂ))
    (hvalues : ∀ X ∈ l, X = 1 ∨ X = P) (hmem : P ∈ l) :
    l.prod = P := by
  classical
  by_cases hPone : P = 1
  · subst P
    apply List.prod_eq_one
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
          have hprod : l.prod = 1 := List.prod_eq_one hall
          rw [hprod, Matrix.mul_one]

private noncomputable def openBondProjectionProduct
    (P : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (hN : 2 ≤ N) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  (List.ofFn fun i : Fin (N - 1) ↦
    ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN ⟨i.val, by omega⟩)
      (twoSiteSectorProjection P)).prod

private theorem openBondProjectionProduct_eq_sitewise
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P * P = P)
    {N : ℕ} (hN : 2 ≤ N) :
    openBondProjectionProduct P hN = (Matrix.piKronecker fun _ : Fin N ↦ P) := by
  classical
  let factors : Fin (N - 1) → Fin N → Matrix (Fin d) (Fin d) ℂ :=
    fun i n ↦ cyclicBondProjectionFactor P ⟨i.val, by omega⟩ n
  have hlist :
      (List.ofFn fun i : Fin (N - 1) ↦
        ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN ⟨i.val, by omega⟩)
          (twoSiteSectorProjection P)) =
        (List.ofFn factors).map Matrix.piKronecker := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact placeAlong_twoSiteSectorProjection_eq_piKronecker P hN ⟨i.val, by omega⟩
  rw [openBondProjectionProduct, hlist]
  rw [Matrix.list_prod_map_piKronecker (List.ofFn factors) fun r ↦ r]
  simp only [List.map_ofFn]
  change Matrix.piKronecker
      (fun n ↦ (List.ofFn fun i : Fin (N - 1) ↦ factors i n).prod) =
    Matrix.piKronecker (fun _ ↦ P)
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
      rw [ite_eq_left (by rw [hoff]; omega)]
    · refine ⟨⟨N - 2, by omega⟩, ?_⟩
      simp only [factors, cyclicBondProjectionFactor]
      have hn : n.val = N - 1 := by omega
      have hoff : (n.val + N - (N - 2)) % N = 1 := by
        rw [hn]
        rw [show N - 1 + N - (N - 2) = N + 1 by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : 1 < N)]
      rw [hoff, ite_eq_left (by omega)]

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

private theorem twoSiteSectorProjection_mul_isometricBond
    (V : Matrix (Fin d) (Fin e) ℂ) (hV : Vᴴ * V = 1)
    (B : Matrix (Fin 2 → Fin e) (Fin 2 → Fin e) ℂ) :
    twoSiteSectorProjection (V * Vᴴ) *
        singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B =
      singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B := by
  rw [← piKronecker_two_mul_conjTranspose V]
  simp only [singleKrausMap_apply, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.piKronecker fun _ : Fin 2 ↦ V)ᴴ
    (Matrix.piKronecker fun _ : Fin 2 ↦ V), Matrix.piKronecker_const_isometry V hV 2,
    Matrix.one_mul]

/-- The complete product of commuting lifted bonds is supported on the
included physical space at every site. No tensor or injectivity hypothesis
is needed. Source context: arXiv:1606.00608, Appendix C.2, equation
generateMPDO, lines 1733–1770. -/
theorem isometricBondProduct_left_supported
    (V : Matrix (Fin d) (Fin e) ℂ) (hV : Vᴴ * V = 1)
    (B : Matrix (Fin 2 → Fin e) (Fin 2 → Fin e) ℂ)
    {N : ℕ} (hN : 2 ≤ N)
    (hcomm : ∀ i j : Fin N,
      Commute (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
          (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B))
        (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN j)
          (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B))) :
    (Matrix.piKronecker fun _ : Fin N ↦ (V * Vᴴ)) *
        (List.ofFn fun i : Fin N =>
          ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
            (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B)).prod =
      (List.ofFn fun i : Fin N =>
        ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
          (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B)).prod := by
  let A : Fin N → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
    fun i ↦ ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
      (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B)
  let R : Fin (N - 1) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
    fun i ↦ ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN ⟨i.val, by omega⟩)
      (twoSiteSectorProjection (V * Vᴴ))
  have hpair : (List.ofFn A).Pairwise Commute := by
    rw [List.pairwise_ofFn]
    intro i j _
    exact hcomm i j
  have hRiAi (i : Fin (N - 1)) :
      R i * A ⟨i.val, by omega⟩ = A ⟨i.val, by omega⟩ := by
    simp only [R, A]
    rw [← ManyBody.placeAlong_mul,
      twoSiteSectorProjection_mul_isometricBond V hV B]
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
  have hP : (V * Vᴴ) * (V * Vᴴ) = (V * Vᴴ) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V,
      hV, Matrix.one_mul]
  have hR : (List.ofFn R).prod = (Matrix.piKronecker fun _ : Fin N ↦ (V * Vᴴ)) := by
    simpa [R, openBondProjectionProduct] using
      openBondProjectionProduct_eq_sitewise (V * Vᴴ) hP hN
  simpa [A, hR] using hRprod





/-- The isometric image of one restricted bond placed on a window of two sites is its ambient lift
multiplied by the range projection on the complete chain.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 and equation
`generateMPDO`, lines 1571--1593 and 1733--1770. -/
theorem singleKrausMap_placeAlong_ringWindow_eq_range_mul_lift
    (V : Matrix (Fin d) (Fin e) ℂ) (hV : Vᴴ * V = 1)
    {N : ℕ} (hN : 2 ≤ N) (i : Fin N)
    (B : Matrix (Fin 2 → Fin e) (Fin 2 → Fin e) ℂ) :
    singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ V)
        (ManyBody.placeAlong (X := fun _ ↦ Fin e) (ManyBody.ringWindow hN i) B) =
      singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ V) 1 *
        ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
          (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B) := by
  let ed := windowComplementEquiv (d := d) 2 N hN i
  let ee := windowComplementEquiv (d := e) 2 N hN i
  apply (Matrix.reindex ed ed).injective
  change (Matrix.reindexLinearEquiv ℂ ℂ ed ed)
      (singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ V)
        (ManyBody.placeAlong (X := fun _ ↦ Fin e) (ManyBody.ringWindow hN i) B)) =
    (Matrix.reindexLinearEquiv ℂ ℂ ed ed)
      (singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ V) 1 *
        ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
          (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B))
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ ed ed ed]
  simp only [Matrix.coe_reindexLinearEquiv]
  rw [Matrix.reindex_singleKrausMap ee ed,
    reindex_piKronecker_windowComplement,
    reindex_placeAlong_ringWindow_windowComplement]
  change singleKrausMap
      ((Matrix.piKronecker fun _ : Fin 2 ↦ V) ⊗ₖ (Matrix.piKronecker fun _ : Fin (N - 2) ↦ V))
        (B ⊗ₖ (1 : Matrix (Fin (N - 2) → Fin e)
          (Fin (N - 2) → Fin e) ℂ)) = _
  rw [Matrix.singleKrausMap_kronecker]
  have hone : Matrix.reindex ee ee
      (1 : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) = 1 := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [Matrix.reindex_apply]
    · have hne : ee.symm x ≠ ee.symm y := fun h ↦ hxy (ee.symm.injective h)
      simp [Matrix.reindex_apply, hxy, hne]
  rw [Matrix.reindex_singleKrausMap ee ed,
    reindex_piKronecker_windowComplement,
    reindex_placeAlong_ringWindow_windowComplement, hone]
  simp only [singleKrausMap_apply, Matrix.mul_one,
    Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  have htwo := Matrix.piKronecker_const_isometry V hV 2
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
      (Matrix.piKronecker fun _ : Fin 2 ↦ V)ᴴ (Matrix.piKronecker fun _ : Fin 2 ↦ V),
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
    singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ V)
        (List.ofFn fun i : Fin N ↦
          ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i) B).prod =
      (List.ofFn fun i : Fin N ↦
        ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
          (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B)).prod := by
  have hW : (Matrix.piKronecker fun _ : Fin N ↦ V)ᴴ * (Matrix.piKronecker fun _ : Fin N ↦ V) = 1 :=
    Matrix.piKronecker_const_isometry V hV N
  have hne : (List.ofFn fun i : Fin N ↦
      ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i) B) ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_ofFn]
    omega
  rw [singleKrausMap_list_prod_of_ne_nil _ hW _ hne, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  change singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ V)
      (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i) B) = _
  rw [singleKrausMap_placeAlong_ringWindow_eq_range_mul_lift V hV hN i B]
  simp only [singleKrausMap_apply, Matrix.mul_one]
  rw [Matrix.piKronecker_const_mul_conjTranspose, hV']
  rw [Matrix.piKronecker_one, Matrix.one_mul]

/-- Isometric inclusion carries a complete periodic product of Hermitian
bonds to the product of their included bonds, provided the included
translates commute. The statement involves no tensor or injectivity
hypothesis. Source context: arXiv:1606.00608, Appendix C.2, equation
generateMPDO, lines 1733–1770. -/
theorem singleKrausMap_bondProduct_of_isometry
    (V : Matrix (Fin d) (Fin e) ℂ) (hV : Vᴴ * V = 1)
    (B : Matrix (Fin 2 → Fin e) (Fin 2 → Fin e) ℂ) (hB : B.IsHermitian)
    {N : ℕ} (hN : 2 ≤ N)
    (hcomm : ∀ i j : Fin N,
      Commute (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
          (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B))
        (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN j)
          (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B))) :
    singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ V)
        (List.ofFn fun i : Fin N =>
          ManyBody.placeAlong (X := fun _ ↦ Fin e) (ManyBody.ringWindow hN i) B).prod =
      (List.ofFn fun i : Fin N =>
        ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
          (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B)).prod := by
  let W := (Matrix.piKronecker fun _ : Fin N ↦ V)
  let Q := singleKrausMap W 1
  let X : Fin N → Matrix (Fin N → Fin e)
      (Fin N → Fin e) ℂ :=
    fun i ↦ ManyBody.placeAlong (X := fun _ ↦ Fin e) (ManyBody.ringWindow hN i) B
  let A : Fin N → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
    fun i ↦ ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
      (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B)
  have hW : Wᴴ * W = 1 :=
    Matrix.piKronecker_const_isometry V hV N
  have hQ : Q * Q = Q := by
    calc
      Q * Q = singleKrausMap W (1 * 1) :=
        (Matrix.singleKrausMap_mul_of_isometry W hW 1 1).symm
      _ = Q := by simp [Q]
  have hmap : (List.ofFn X).map (singleKrausMap W) =
      List.ofFn (fun i ↦ Q * A i) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact singleKrausMap_placeAlong_ringWindow_eq_range_mul_lift
      V hV hN i B
  have hQherm : Q.IsHermitian :=
    (Matrix.PosSemidef.one.mul_mul_conjTranspose_same W).1
  have hcommQ : ∀ C ∈ List.ofFn A, Q * C = C * Q := by
    intro C hC
    rw [List.mem_ofFn] at hC
    obtain ⟨i, rfl⟩ := hC
    have hleft := singleKrausMap_placeAlong_ringWindow_eq_range_mul_lift
      V hV hN i B
    have hXherm : (X i).IsHermitian :=
      ManyBody.isHermitian_placeAlong _ hB
    have hφherm : (singleKrausMap W (X i)).IsHermitian :=
      Matrix.isHermitian_mul_mul_conjTranspose W hXherm
    have hAherm : (A i).IsHermitian :=
      ManyBody.isHermitian_placeAlong _
        (Matrix.isHermitian_mul_mul_conjTranspose (Matrix.piKronecker fun _ : Fin 2 ↦ V) hB)
    calc
      Q * A i = singleKrausMap W (X i) := hleft.symm
      _ = (singleKrausMap W (X i))ᴴ := hφherm.eq.symm
      _ = (Q * A i)ᴴ := congrArg Matrix.conjTranspose hleft
      _ = A i * Q := by
        rw [Matrix.conjTranspose_mul, hAherm.eq, hQherm.eq]
  have hQrange : Q = (Matrix.piKronecker fun _ : Fin N ↦ (V * Vᴴ)) := by
    simp only [Q, singleKrausMap_apply, Matrix.mul_one, W]
    rw [Matrix.piKronecker_const_mul_conjTranspose]
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
      exact isometricBondProduct_left_supported V hV B hN hcomm


namespace PhysicalSupportRestrictionData

variable {P : Matrix (Fin d) (Fin d) ℂ} {K : MPOTensor d D}

/-- Isometric conjugation carries the complete restricted periodic bond
product to the complete product of the lifted ambient bond, for every chain
length at least two.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 and equation
`generateMPDO`, lines 1571--1593 and 1733--1770. -/
theorem singleKrausMap_bondProduct_eq_liftedBondProduct
    (F : PhysicalSupportRestrictionData P K)
    (data : CommutingBond F.supportDim)
    {N : ℕ} (hN : 2 ≤ N) :
    singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ F.inclusion)
        (List.ofFn fun i : Fin N ↦
          ManyBody.placeAlong (X := fun _ ↦ Fin F.supportDim) (ManyBody.ringWindow hN i)
            data.bond).prod =
      (List.ofFn fun i : Fin N ↦
        ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
          (F.liftedBond data.bond)).prod := by
  exact singleKrausMap_bondProduct_of_isometry F.inclusion F.inclusion_isometry
    data.bond data.bond_pos.isHermitian hN
    (fun i j => (F.liftedCommutingBond data).bond_comm hN i j)

/-- A commuting form on the restricted physical space extends through the
support isometry to a commuting form of the ambient tensor.  The same
positive normalization scalar is retained at every chain length.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 and equation
`generateMPDO`, lines 1571--1593 and 1733--1770. -/
noncomputable def liftedCommutingForm
    (F : PhysicalSupportRestrictionData P K)
    (data : CommutingForm
      (PhysicalSectorFactorization.changePhysicalBasis F.inclusionᴴ K)) :
    CommutingForm K where
  toCommutingBond := F.liftedCommutingBond data.toCommutingBond
  realizes_mpo := by
    intro N hN
    obtain ⟨c, hc, hreal⟩ := data.realizes_mpo N hN
    refine ⟨c, hc, ?_⟩
    change mpo K N = (c : ℂ) •
      (List.ofFn fun i : Fin N ↦
        ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
          (F.liftedBond data.bond)).prod
    have hmpo : mpo K N =
        singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ F.inclusion)
          (mpo (PhysicalSectorFactorization.changePhysicalBasis
            F.inclusionᴴ K) N) := by
      rw [singleKrausMap_piKronecker_mpo, F.reembed]
    change mpo (PhysicalSectorFactorization.changePhysicalBasis
      F.inclusionᴴ K) N = (c : ℂ) •
        (List.ofFn fun i : Fin N ↦
          ManyBody.placeAlong (X := fun _ ↦ Fin F.supportDim) (ManyBody.ringWindow hN i)
            data.bond).prod at hreal
    rw [hmpo, hreal]
    rw [(singleKrausMap
      (Matrix.piKronecker fun _ : Fin N ↦ F.inclusion)).map_smul]
    rw [F.singleKrausMap_bondProduct_eq_liftedBondProduct data.toCommutingBond hN]


/-- A positive physical-sector factorization on the restricted physical space
gives a positive commuting bond for the ambient tensor supported on the tensor
square of the prescribed one-site projection. Its periodic product is exactly
the ambient MPO at every length at least two.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl`, `Appetakhetc`,
`PjKiPj`, and `generateMPDO`, lines 1383--1450 and 1680--1770. -/
theorem exists_commutingForm_lifted_supported_of_physicalSectorFactorization
    (F : PhysicalSupportRestrictionData P K)
    (G : PhysicalSectorFactorization
      (PhysicalSectorFactorization.changePhysicalBasis F.inclusionᴴ K))
    (hη : ∀ k h, (G.neighboringOperator k h).PosSemidef) :
    ∃ data : CommutingForm K,
      twoSiteSectorProjection P * data.bond *
          twoSiteSectorProjection P = data.bond ∧
      ∀ N (hN : 2 ≤ N),
        mpo K N = data.product hN := by
  let restrictedData := G.commutingForm hη
  let data := F.liftedCommutingForm restrictedData
  refine ⟨data, F.liftedBond_supported restrictedData.bond, ?_⟩
  intro N hN
  change mpo K N =
    (F.liftedCommutingBond restrictedData.toCommutingBond).product hN
  have hmpo : mpo K N =
      singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ F.inclusion)
        (mpo (PhysicalSectorFactorization.changePhysicalBasis
          F.inclusionᴴ K) N) := by
    rw [singleKrausMap_piKronecker_mpo, F.reembed]
  rw [hmpo]
  change singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ F.inclusion)
      (mpo (PhysicalSectorFactorization.changePhysicalBasis
        F.inclusionᴴ K) N) =
    (List.ofFn fun i : Fin N ↦
      ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
        (F.liftedBond restrictedData.bond)).prod
  rw [show mpo (PhysicalSectorFactorization.changePhysicalBasis
      F.inclusionᴴ K) N =
      (List.ofFn fun i : Fin N ↦
        ManyBody.placeAlong (X := fun _ ↦ Fin F.supportDim) (ManyBody.ringWindow hN i)
          restrictedData.bond).prod by
    exact G.mpo_eq_product_physicalBond hN]
  exact F.singleKrausMap_bondProduct_eq_liftedBondProduct
    restrictedData.toCommutingBond hN

/-- Proposition C.8 on the injective physical support gives a commuting form,
a commuting-product realization of the ambient tensor whose bond remains in the
prescribed two-site sector.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`) and
equations `PjKiPj` and `generateMPDO`, lines 1571--1593 and 1733--1770. -/
theorem exists_commutingForm_lifted_supported
    (F : PhysicalSupportRestrictionData P K) (hSAL : IsSAL K) :
    ∃ data : CommutingForm K,
      twoSiteSectorProjection P * data.bond *
          twoSiteSectorProjection P = data.bond ∧
      ∀ N (hN : 2 ≤ N),
        mpo K N = data.product hN := by
  obtain ⟨G, hG⟩ := exists_positive_physicalSectorFactorization_of_isSAL
    (PhysicalSectorFactorization.changePhysicalBasis F.inclusionᴴ K)
    ((isInjective_toMPSTensor_iff _).2 F.restricted_injective) (F.restricted_isSAL hSAL)
  exact F.exists_commutingForm_lifted_supported_of_physicalSectorFactorization
    G hG

end PhysicalSupportRestrictionData

end MPOTensor

end

section

open scoped BigOperators ComplexOrder Kronecker Matrix

namespace MPOTensor

variable {d : ℕ}

/-- **Scaled finite-chain cyclic neighboring-operator identity.** A positive
translation-invariant commuting bond admits one chain-independent unitary,
one collection of sector dimensions, and one positive neighboring family such
that, at every length at least two, conjugation by the sitewise tensor power
and cyclic regrouping give the direct sum of cyclic neighboring products, up
to the positive realization scalar.

**Local fix (proportionality scalar):** The converse argument in
arXiv:1606.00608, lines 1603--1605, passes from a matrix proportional to a
commuting-bond product to the coefficient-free equation sigmaNK2 without
retaining the proportionality scalar. The statement below preserves the
positive scalar at each chain length. This discrepancy is recorded in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`.

This result uses neither zero correlation length, rank-one trace factorization,
a Markov decomposition, nor saturation of the area law, and it does not prove
Proposition `4to2`.

Source: arXiv:1606.00608, Appendix C.2, equation expression, lines 1571--1576,
and equation sigmaNK2 as invoked at lines 1603--1605.
Documented in `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem CommutingForm.exists_positive_cyclic_eta_block_decomposition
    {D : ℕ} {M : MPOTensor d D} (data : CommutingForm M) :
    ∃ (K : ℕ) (dl dr : Fin K → ℕ)
      (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
      (U : Matrix (Fin d) (Fin d) ℂ)
      (η : (q h : Fin K) →
        Matrix (Matrix.EtaEdgeIndex dl dr q h)
          (Matrix.EtaEdgeIndex dl dr q h) ℂ),
      U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
        (∀ q, 0 < dl q) ∧ (∀ q, 0 < dr q) ∧
        (∀ q h, (η q h).PosSemidef) ∧
        ∀ (N : ℕ) (hN : 2 ≤ N),
          letI : NeZero N := ⟨by omega⟩
          ∃ c : ℝ, 0 < c ∧
          Matrix.reindex
              (Matrix.etaCyclicEdgeEquiv dl dr e)
              (Matrix.etaCyclicEdgeEquiv dl dr e)
              (star (Matrix.piKronecker fun _ : Fin N ↦ U) * mpo M N *
                (Matrix.piKronecker fun _ : Fin N ↦ U)) =
            (c : ℂ) • Matrix.blockDiagonal' fun k : Fin N → Fin K ↦
              fun x y ↦ ∏ n : Fin N, η (k n) (k (n + 1)) (x n) (y n) := by
  classical
  obtain ⟨K, dl, dr, e, U, η, hU, hdl, hdr, hη, hB⟩ :=
    data.exists_positive_eta_pairBond_decomposition
  refine ⟨K, dl, dr, e, U, η, hU, hdl, hdr, hη, ?_⟩
  intro N hN
  let : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc, hreal⟩ := data.realizes_mpo N hN
  refine ⟨c, hc, ?_⟩
  have hUco : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  have hUiso : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hU)
  have hV : (Uᴴ)ᴴ * Uᴴ = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hUco
  have hV' : Uᴴ * (Uᴴ)ᴴ = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hUiso
  change mpo M N = (c : ℂ) •
    (List.ofFn fun i : Fin N ↦
      ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
        data.bond).prod at hreal
  have hconj :
      singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ Uᴴ) (mpo M N) =
        (c : ℂ) • (List.ofFn fun i : Fin N ↦
          ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm
              (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)))).prod := by
    rw [hreal, (singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ Uᴴ)).map_smul,
      singleKrausMap_bondProduct_of_unitary Uᴴ hV hV' hN]
    congr 1
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext i
    rw [singleKrausMap_sitewise_conjTranspose_two_eq]
    rfl
  have hglobal :
      singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ Uᴴ) (mpo M N) =
        star (Matrix.piKronecker fun _ : Fin N ↦ U) * mpo M N *
          (Matrix.piKronecker fun _ : Fin N ↦ U) := by
    simp only [singleKrausMap_apply, ← Matrix.conjTranspose_piKronecker,
      Matrix.conjTranspose_conjTranspose, Matrix.star_eq_conjTranspose]
  have hcyclic := reindex_product_placeAlong_ringWindow_of_etaPair_decomposition
    hN dl dr e η (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)) hB
  calc
    Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
        (Matrix.etaCyclicEdgeEquiv dl dr e)
        (star (Matrix.piKronecker fun _ : Fin N ↦ U) * mpo M N *
          (Matrix.piKronecker fun _ : Fin N ↦ U)) =
      Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
        (Matrix.etaCyclicEdgeEquiv dl dr e)
        (singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ Uᴴ) (mpo M N)) :=
          congrArg (Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
            (Matrix.etaCyclicEdgeEquiv dl dr e)) hglobal.symm
    _ = Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
        (Matrix.etaCyclicEdgeEquiv dl dr e)
        ((c : ℂ) • (List.ofFn fun i : Fin N ↦
          ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm
              (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)))).prod) :=
          congrArg (Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
            (Matrix.etaCyclicEdgeEquiv dl dr e)) hconj
    _ = (c : ℂ) • Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
        (Matrix.etaCyclicEdgeEquiv dl dr e)
        (List.ofFn fun i : Fin N ↦
          ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hN i)
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm
              (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)))).prod := by
          rfl
    _ = (c : ℂ) • Matrix.blockDiagonal' fun k : Fin N → Fin K ↦
        fun x y ↦ ∏ n : Fin N, η (k n) (k (n + 1)) (x n) (y n) :=
          congrArg ((c : ℂ) • ·) hcyclic

end MPOTensor

end
