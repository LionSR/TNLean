/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RingTheory.SimpleModule.Basic
import QICLean.Algebra.MatrixFamilyAction
import QICLean.Channel.Schwarz.Basic
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessBlocks
import TNLean.MPS.FundamentalTheorem.Arbitrary.ArbitraryTensor
import TNLean.MPS.FundamentalTheorem.Arbitrary.Basic
import TNLean.MPS.FundamentalTheorem.Arbitrary.WordModuleGauge
import TNLean.MPS.FundamentalTheorem.UnitaryGauge

/-!
# Completely reducible tensors and unitary gauges

A tensor is *completely reducible* when its word module is semisimple, a direct sum of simple
submodules, its *summands*; the zero summands are the lines on which every letter acts as zero.
Two completely reducible tensors have the same states exactly when their nonzero summands are
isomorphic in pairs; with equal bond dimensions, or without zero summands, exactly when they are
gauge equivalent. Between irreducible right-normalized tensors every gauge
is a nonzero scalar times a unitary, and the unitary is unique up to a phase.

## Main results

* `MPSTensor.sameMPV₂Pos_iff_exists_equiv_forall_nonempty_linearEquiv`,
  `MPSTensor.sameMPV₂Pos_iff_isGaugeRelated_of_isSemisimpleModule`,
  `MPSTensor.sameMPV₂Pos_iff_isGaugeRelated_of_forall_exists_smul_ne_zero`.
* `MPSTensor.exists_ne_zero_and_exists_mem_unitaryGroup_eq_smul`,
  `MPSTensor.exists_norm_eq_one_and_eq_smul_of_mem_unitaryGroup`.
-/

open scoped Matrix

namespace MPSTensor

open WordAlgebra

/-! ### Direct sums of simple submodules -/

section DirectSum

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- Adding a submodule `N` disjoint from `P` gives a step `(P ⊔ N) / P` isomorphic to `N`. -/
private noncomputable def subquotSupEquiv {P N : Submodule R M} (h : Disjoint P N) :
    Submodule.subquot P (P ⊔ N) ≃ₗ[R] N :=
  ((Submodule.subquotCongr rfl (sup_comm P N)).trans
    (LinearMap.quotientInfEquivSupQuotient N P).symm).trans
    (Submodule.quotEquivOfEqBot _ (by
      rw [Submodule.comap_subtype_self, top_inf_eq, ← Submodule.disjoint_iff_comap_eq_bot]
      exact h.symm))

/-- The partial sums `⨆_{σ⁻¹ i < k} N i` of a family indexed through `σ : Fin n ≃ ι`. -/
private def partialSup {ι : Type*} {n : ℕ} (N : ι → Submodule R M) (σ : Fin n ≃ ι) (k : ℕ) :
    Submodule R M :=
  ⨆ i ∈ {i | ((σ.symm i : Fin n) : ℕ) < k}, N i

private theorem partialSup_zero {ι : Type*} {n : ℕ} (N : ι → Submodule R M) (σ : Fin n ≃ ι) :
    partialSup N σ 0 = ⊥ := by
  simp [partialSup]

private theorem partialSup_eq_top {ι : Type*} {n : ℕ} (N : ι → Submodule R M) (σ : Fin n ≃ ι)
    (htop : ⨆ j, N j = ⊤) : partialSup N σ n = ⊤ := by
  simp [partialSup, htop]

private theorem partialSup_succ {ι : Type*} {n : ℕ} (N : ι → Submodule R M) (σ : Fin n ≃ ι)
    (k : Fin n) : partialSup N σ (k + 1) = partialSup N σ k ⊔ N (σ k) := by
  have hset : {i | ((σ.symm i : Fin n) : ℕ) < k + 1} =
      insert (σ k) {i | ((σ.symm i : Fin n) : ℕ) < k} := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    rw [Nat.lt_succ_iff_lt_or_eq, ← Equiv.symm_apply_eq, ← Fin.val_inj, or_comm]
  rw [partialSup, partialSup, hset, iSup_insert, sup_comm]

private theorem disjoint_partialSup {ι : Type*} {n : ℕ} (N : ι → Submodule R M) (σ : Fin n ≃ ι)
    (hN : iSupIndep N) (k : Fin n) : Disjoint (partialSup N σ k) (N (σ k)) :=
  (hN.disjoint_biSup (x := σ k) (y := {i | ((σ.symm i : Fin n) : ℕ) < k}) (by simp)).symm

/-- **A decomposition into simple submodules gives an invariant flag**: the partial sums of a
finite independent family of simple submodules with sum `⊤` form a
composition series whose steps are the summands. -/
private theorem exists_compositionSeries_of_iSupIndep {ι : Type*} [Finite ι]
    (N : ι → Submodule R M) (hN : iSupIndep N) (htop : ⨆ j, N j = ⊤)
    (hsimple : ∀ j, IsSimpleModule R (N j)) :
    ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤ ∧
      ∃ σ : Fin s.length ≃ ι, ∀ k,
        Nonempty (Submodule.subquot (s k.castSucc) (s k.succ) ≃ₗ[R] N (σ k)) := by
  obtain ⟨n, ⟨τ⟩⟩ := Finite.exists_equiv_fin ι
  have hstep : ∀ k : Fin n, Submodule.subquot (partialSup N τ.symm k)
      (partialSup N τ.symm (k + 1)) ≃ₗ[R] N (τ.symm k) := fun k =>
    (Submodule.subquotCongr rfl (partialSup_succ N τ.symm k)).trans
      (subquotSupEquiv (disjoint_partialSup N τ.symm hN k))
  refine ⟨⟨n, fun k => partialSup N τ.symm k, fun k => ?_⟩, partialSup_zero N τ.symm,
    partialSup_eq_top N τ.symm htop, τ.symm, fun k => ⟨hstep k⟩⟩
  have := hsimple (τ.symm k)
  change partialSup N τ.symm k ⋖ partialSup N τ.symm (k + 1)
  rw [covBy_iff_quot_is_simple (le_sup_left.trans_eq (partialSup_succ N τ.symm k).symm)]
  exact IsSimpleModule.congr (hstep k)

/-- **Matched summands give isomorphic modules**: two internal direct sums of families of
submodules matched by a bijection pairing isomorphic summands are isomorphic. -/
private theorem nonempty_linearEquiv_of_iSupIndep {ι κ M' : Type*} [AddCommGroup M']
    [Module R M'] (N : ι → Submodule R M) (N' : κ → Submodule R M') (hN : iSupIndep N)
    (htop : ⨆ j, N j = ⊤) (hN' : iSupIndep N') (htop' : ⨆ k, N' k = ⊤) (f : ι ≃ κ)
    (h : ∀ j, Nonempty (N j ≃ₗ[R] N' (f j))) : Nonempty (M ≃ₗ[R] M') := by
  classical
  have hi := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N).2 ⟨hN, htop⟩
  have hi' := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N').2 ⟨hN', htop'⟩
  let φ : ∀ k, N (f.symm k) ≃ₗ[R] N' k := fun k =>
    (h (f.symm k)).some.trans (LinearEquiv.ofEq _ _ (congrArg N' (f.apply_symm_apply k)))
  exact ⟨(LinearEquiv.ofBijective (DirectSum.coeLinearMap N) hi).symm.trans
    ((DirectSum.lequivCongrLeft R f).trans ((DFinsupp.mapRange.linearEquiv φ).trans
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap N') hi')))⟩

end DirectSum

section WordModule

variable {d : ℕ}

/-- Nonzero letters are transported along isomorphisms of word-algebra modules. -/
private theorem exists_smul_ne_zero_congr {X Y : Type*} [AddCommMonoid X]
    [Module (WordAlgebra d) X] [AddCommMonoid Y] [Module (WordAlgebra d) Y]
    (e : X ≃ₗ[WordAlgebra d] Y) :
    (∃ (i : Fin d) (x : X), (ofWord [i] : WordAlgebra d) • x ≠ 0) ↔
      ∃ (i : Fin d) (y : Y), (ofWord [i] : WordAlgebra d) • y ≠ 0 :=
  ⟨fun ⟨i, x, hx⟩ => ⟨i, e x, by rw [← LinearEquiv.map_smul, e.map_ne_zero_iff]; exact hx⟩,
    fun ⟨i, y, hy⟩ => ⟨i, e.symm y, by
      rw [← LinearEquiv.map_smul, e.symm.map_ne_zero_iff]; exact hy⟩⟩

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
  [IsScalarTower ℂ (WordAlgebra d) M]

/-- Two modules of equal finite dimension on which every letter acts as zero are isomorphic. -/
private theorem nonempty_linearEquiv_of_forall_smul_eq_zero {N : Type*} [AddCommGroup N]
    [Module ℂ N] [Module (WordAlgebra d) N] [IsScalarTower ℂ (WordAlgebra d) N]
    [FiniteDimensional ℂ M] [FiniteDimensional ℂ N]
    (hM : ∀ (i : Fin d) (x : M), (ofWord [i] : WordAlgebra d) • x = 0)
    (hN : ∀ (i : Fin d) (x : N), (ofWord [i] : WordAlgebra d) • x = 0)
    (h : Module.finrank ℂ M = Module.finrank ℂ N) : Nonempty (M ≃ₗ[WordAlgebra d] N) :=
  ⟨linearEquivOfLetter (LinearEquiv.ofFinrankEq M N h) fun i x => by
    rw [hM, hN, map_zero]⟩

/-- The empty word has trace the dimension. -/
private theorem traceWord_nil [FiniteDimensional ℂ M] :
    traceWord M ([] : List (Fin d)) = Module.finrank ℂ M := by
  rw [traceWord_def, ofWord_nil, map_one, LinearMap.trace_one]

/-- Submodules of a finite-dimensional module are finite-dimensional. -/
private theorem finiteDimensional_submodule [FiniteDimensional ℂ M]
    (K : Submodule (WordAlgebra d) M) : FiniteDimensional ℂ K :=
  Module.Finite.of_injective (K.subtype.restrictScalars ℂ) K.subtype_injective

/-- An independent family of simple submodules of a finite-dimensional module is finite. -/
private theorem finite_of_iSupIndep [FiniteDimensional ℂ M] {ι : Type*}
    (N : ι → Submodule (WordAlgebra d) M) (hN : iSupIndep N)
    (hsimple : ∀ j, IsSimpleModule (WordAlgebra d) (N j)) : Finite ι := by
  have : IsNoetherian (WordAlgebra d) M := isNoetherian_of_tower ℂ inferInstance
  exact WellFoundedGT.finite_of_iSupIndep hN fun j => (isSimpleModule_iff_isAtom.1 (hsimple j)).1

/-- **Traces over a direct sum**: the trace of a word on an internal direct sum of simple
submodules is the sum of its traces on the summands (along the flag of partial sums). -/
private theorem traceWord_eq_sum_of_iSupIndep [FiniteDimensional ℂ M] {ι : Type*} [Fintype ι]
    (N : ι → Submodule (WordAlgebra d) M) (hN : iSupIndep N) (htop : ⨆ j, N j = ⊤)
    (hsimple : ∀ j, IsSimpleModule (WordAlgebra d) (N j)) (w : List (Fin d)) :
    traceWord M w = ∑ j, traceWord (N j) w := by
  obtain ⟨s, h0, h1, σ, hσ⟩ := exists_compositionSeries_of_iSupIndep N hN htop hsimple
  have hsum := traceWord_eq_sum_subquot s.toFun h0 s.strictMono.monotone w
  rw [show s.toFun (Fin.last s.length) = ⊤ from h1,
    traceWord_congr (Submodule.topEquiv (R := WordAlgebra d) (M := M)) w] at hsum
  rw [hsum, ← Equiv.sum_comp σ]
  exact Finset.sum_congr rfl fun k _ => traceWord_congr (hσ k).some w

end WordModule

variable {d DA DB : ℕ} {A : MPSTensor d DA} {B : MPSTensor d DB}

/-- Completely reducible tensors with the same states: the nonzero summands are matched. -/
private theorem exists_equiv_forall_nonempty_linearEquiv_of_sameMPV₂Pos {ι κ : Type*}
    (N : ι → Submodule (WordAlgebra d) A.WordModule)
    (N' : κ → Submodule (WordAlgebra d) B.WordModule)
    (hN : iSupIndep N) (hNtop : ⨆ j, N j = ⊤) (hNsimple : ∀ j, IsSimpleModule (WordAlgebra d) (N j))
    (hN' : iSupIndep N') (hN'top : ⨆ k, N' k = ⊤)
    (hN'simple : ∀ k, IsSimpleModule (WordAlgebra d) (N' k)) (h : SameMPV₂Pos A B) :
    ∃ e : {j // ∃ (i : Fin d) (x : N j), (ofWord [i] : WordAlgebra d) • x ≠ 0} ≃
        {k // ∃ (i : Fin d) (x : N' k), (ofWord [i] : WordAlgebra d) • x ≠ 0},
      ∀ j, Nonempty (N j.1 ≃ₗ[WordAlgebra d] N' (e j).1) := by
  have := finite_of_iSupIndep N hN hNsimple
  have := finite_of_iSupIndep N' hN' hN'simple
  obtain ⟨s, hs0, hs1, σ, hσ⟩ := exists_compositionSeries_of_iSupIndep N hN hNtop hNsimple
  obtain ⟨s', hs0', hs1', σ', hσ'⟩ :=
    exists_compositionSeries_of_iSupIndep N' hN' hN'top hN'simple
  have h12 := (tfae_sameMPV₂Pos_compositionSeries (B := A) (B' := B)).out 1 2
  obtain ⟨e0, he0⟩ := h12.1 h s s' hs0 hs1 hs0' hs1'
  let tS : {k : Fin s.length // ∃ (i : Fin d) (x : Submodule.subquot (s k.castSucc) (s k.succ)),
        (ofWord [i] : WordAlgebra d) • x ≠ 0} ≃
      {j // ∃ (i : Fin d) (x : N j), (ofWord [i] : WordAlgebra d) • x ≠ 0} :=
    σ.subtypeEquiv fun k => by have hk := exists_smul_ne_zero_congr (d := d) (hσ k).some; exact hk
  let tS' : {k : Fin s'.length // ∃ (i : Fin d)
        (x : Submodule.subquot (s' k.castSucc) (s' k.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0} ≃
      {j // ∃ (i : Fin d) (x : N' j), (ofWord [i] : WordAlgebra d) • x ≠ 0} :=
    σ'.subtypeEquiv fun k => by
      have hk := exists_smul_ne_zero_congr (d := d) (hσ' k).some; exact hk
  refine ⟨tS.symm.trans (e0.trans tS'), fun j => ?_⟩
  obtain ⟨a⟩ := hσ (tS.symm j).1
  obtain ⟨b⟩ := he0 (tS.symm j)
  obtain ⟨c⟩ := hσ' (e0 (tS.symm j)).1
  have hj : N (σ (tS.symm j).1) = N j.1 := congrArg N (σ.apply_symm_apply j.1)
  exact ⟨((LinearEquiv.ofEq _ _ hj).symm.trans a.symm).trans (b.trans c)⟩

/-- Completely reducible tensors with matched nonzero summands have the same states. -/
private theorem sameMPV₂Pos_of_exists_equiv_forall_nonempty_linearEquiv {ι κ : Type*}
    (N : ι → Submodule (WordAlgebra d) A.WordModule)
    (N' : κ → Submodule (WordAlgebra d) B.WordModule)
    (hN : iSupIndep N) (hNtop : ⨆ j, N j = ⊤) (hNsimple : ∀ j, IsSimpleModule (WordAlgebra d) (N j))
    (hN' : iSupIndep N') (hN'top : ⨆ k, N' k = ⊤)
    (hN'simple : ∀ k, IsSimpleModule (WordAlgebra d) (N' k))
    (e : {j // ∃ (i : Fin d) (x : N j), (ofWord [i] : WordAlgebra d) • x ≠ 0} ≃
        {k // ∃ (i : Fin d) (x : N' k), (ofWord [i] : WordAlgebra d) • x ≠ 0})
    (he : ∀ j, Nonempty (N j.1 ≃ₗ[WordAlgebra d] N' (e j).1)) : SameMPV₂Pos A B := by
  classical
  have := finite_of_iSupIndep N hN hNsimple
  have := finite_of_iSupIndep N' hN' hN'simple
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype κ := Fintype.ofFinite κ
  let p : ι → Prop := fun j => ∃ (i : Fin d) (x : N j), (ofWord [i] : WordAlgebra d) • x ≠ 0
  let p' : κ → Prop := fun k => ∃ (i : Fin d) (x : N' k), (ofWord [i] : WordAlgebra d) • x ≠ 0
  refine sameMPV₂Pos_iff_forall_trace_evalWord_eq.2 fun w hw => ?_
  rw [← traceWord_wordModule, ← traceWord_wordModule]
  have hz : ∑ j : {j // ¬ p j}, traceWord (N j.1) w = 0 :=
    Finset.sum_eq_zero fun j _ => traceWord_eq_zero_of_forall_smul_eq_zero
      (fun i x => by_contra fun hx => j.2 ⟨i, x, hx⟩) hw
  have hz' : ∑ k : {k // ¬ p' k}, traceWord (N' k.1) w = 0 :=
    Finset.sum_eq_zero fun k _ => traceWord_eq_zero_of_forall_smul_eq_zero
      (fun i x => by_contra fun hx => k.2 ⟨i, x, hx⟩) hw
  rw [traceWord_eq_sum_of_iSupIndep N hN hNtop hNsimple w,
    traceWord_eq_sum_of_iSupIndep N' hN' hN'top hN'simple w,
    ← Fintype.sum_subtype_add_sum_subtype p, ← Fintype.sum_subtype_add_sum_subtype p', hz, hz',
    add_zero, add_zero]
  exact Fintype.sum_equiv e _ _ fun j => traceWord_congr (he j).some w

/-- **The dimension count**: the bond dimension of a tensor whose word module is the internal
direct sum of simple submodules `L j` is the sum of the dimensions of the summands with `q j`
plus the number of the others, provided these are lines. -/
private theorem natCast_eq_sum_traceWord_nil_add_card {D' : ℕ} (A' : MPSTensor d D') {γ : Type*}
    [Fintype γ] (L : γ → Submodule (WordAlgebra d) A'.WordModule) (q : γ → Prop)
    [DecidablePred q] (hL : iSupIndep L) (hLtop : ⨆ j, L j = ⊤)
    (hLsimple : ∀ j, IsSimpleModule (WordAlgebra d) (L j))
    (hLone : ∀ j, ¬ q j → Module.finrank ℂ (L j) = 1) :
    (D' : ℂ) = ∑ j : {j // q j}, traceWord (L j.1) ([] : List (Fin d)) +
      Fintype.card {j // ¬ q j} := by
  have h1 := traceWord_eq_sum_of_iSupIndep L hL hLtop hLsimple []
  rw [traceWord_wordModule, ← Fintype.sum_subtype_add_sum_subtype q] at h1
  rw [show (D' : ℂ) = Matrix.trace (Kraus.evalWord A' []) by simp [Kraus.evalWord], h1,
    Fintype.card_eq_sum_ones, Nat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have := finiteDimensional_submodule (L j.1)
  rw [traceWord_nil, hLone j.1 j.2, Nat.cast_one]

/-- Matched nonzero summands and equal bond dimensions give a gauge. The zero
summands are lines with zero letters, equally many on both sides by the dimension count. -/
private theorem isGaugeRelated_of_exists_equiv_forall_nonempty_linearEquiv {ι κ : Type*}
    (N : ι → Submodule (WordAlgebra d) A.WordModule)
    (N' : κ → Submodule (WordAlgebra d) B.WordModule)
    (hN : iSupIndep N) (hNtop : ⨆ j, N j = ⊤) (hNsimple : ∀ j, IsSimpleModule (WordAlgebra d) (N j))
    (hN' : iSupIndep N') (hN'top : ⨆ k, N' k = ⊤)
    (hN'simple : ∀ k, IsSimpleModule (WordAlgebra d) (N' k)) (hD : DA = DB)
    (e : {j // ∃ (i : Fin d) (x : N j), (ofWord [i] : WordAlgebra d) • x ≠ 0} ≃
        {k // ∃ (i : Fin d) (x : N' k), (ofWord [i] : WordAlgebra d) • x ≠ 0})
    (he : ∀ j, Nonempty (N j.1 ≃ₗ[WordAlgebra d] N' (e j).1)) : IsGaugeRelated A B := by
  classical
  have := finite_of_iSupIndep N hN hNsimple
  have := finite_of_iSupIndep N' hN' hN'simple
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype κ := Fintype.ofFinite κ
  let p : ι → Prop := fun j => ∃ (i : Fin d) (x : N j), (ofWord [i] : WordAlgebra d) • x ≠ 0
  let p' : κ → Prop := fun k => ∃ (i : Fin d) (x : N' k), (ofWord [i] : WordAlgebra d) • x ≠ 0
  have hzero : ∀ j, ¬ p j → ∀ (i : Fin d) (x : N j), (ofWord [i] : WordAlgebra d) • x = 0 :=
    fun j hj i x => by_contra fun hx => hj ⟨i, x, hx⟩
  have hzero' : ∀ k, ¬ p' k → ∀ (i : Fin d) (x : N' k), (ofWord [i] : WordAlgebra d) • x = 0 :=
    fun k hk i x => by_contra fun hx => hk ⟨i, x, hx⟩
  have hone : ∀ j, ¬ p j → Module.finrank ℂ (N j) = 1 := fun j hj => by
    have := hNsimple j
    exact finrank_eq_one_of_isSimpleModule_of_forall_smul_eq_zero (M := N j) (hzero j hj)
  have hone' : ∀ k, ¬ p' k → Module.finrank ℂ (N' k) = 1 := fun k hk => by
    have := hN'simple k
    exact finrank_eq_one_of_isSimpleModule_of_forall_smul_eq_zero (M := N' k) (hzero' k hk)
  -- the dimension count
  have hcard : Fintype.card {j // ¬ p j} = Fintype.card {k // ¬ p' k} := by
    have hA := natCast_eq_sum_traceWord_nil_add_card A N p hN hNtop hNsimple hone
    have hB := natCast_eq_sum_traceWord_nil_add_card B N' p' hN' hN'top hN'simple hone'
    have hsum : ∑ j : {j // p j}, traceWord (N j.1) ([] : List (Fin d)) =
        ∑ k : {k // p' k}, traceWord (N' k.1) ([] : List (Fin d)) :=
      Fintype.sum_equiv e _ _ fun j => traceWord_congr (he j).some []
    have hDc : (DA : ℂ) = DB := by rw [hD]
    have hc : (Fintype.card {j // ¬ p j} : ℂ) = Fintype.card {k // ¬ p' k} := by
      linear_combination hB + hDc - hA - hsum
    exact_mod_cast hc
  let eZ : {j // ¬ p j} ≃ {k // ¬ p' k} := Fintype.equivOfCardEq hcard
  let f : ι ≃ κ := (Equiv.sumCompl p).symm.trans ((e.sumCongr eZ).trans (Equiv.sumCompl p'))
  have hf : ∀ j, Nonempty (N j ≃ₗ[WordAlgebra d] N' (f j)) := by
    intro j
    by_cases hj : p j
    · rw [show f j = (e ⟨j, hj⟩).1 by simp [f, Equiv.sumCompl_symm_apply_of_pos hj]]
      exact he ⟨j, hj⟩
    · rw [show f j = (eZ ⟨j, hj⟩).1 by simp [f, Equiv.sumCompl_symm_apply_of_neg hj]]
      have := finiteDimensional_submodule (N j)
      have := finiteDimensional_submodule (N' (eZ ⟨j, hj⟩).1)
      exact nonempty_linearEquiv_of_forall_smul_eq_zero (M := N j) (N := N' (eZ ⟨j, hj⟩).1)
        (hzero j hj)
        (hzero' _ (eZ ⟨j, hj⟩).2) (by rw [hone j hj, hone' _ (eZ ⟨j, hj⟩).2])
  exact isGaugeRelated_iff_nonempty_linearEquiv_wordModule.2
    (nonempty_linearEquiv_of_iSupIndep N N' hN hNtop hN' hN'top f hf)

/-! ### Completely reducible tensors -/

/-- **Completely reducible tensors, the states**. Let the word modules of `A` and `B` be the
internal direct sums of the simple submodules `N j` and `N' k`. Then `A` and `B` have the same
states if and only if a bijection between the nonzero summands (those on which some letter acts as a
nonzero map) pairs isomorphic summands. -/
theorem sameMPV₂Pos_iff_exists_equiv_forall_nonempty_linearEquiv {ι κ : Type*}
    (N : ι → Submodule (WordAlgebra d) A.WordModule)
    (N' : κ → Submodule (WordAlgebra d) B.WordModule)
    (hN : iSupIndep N) (hNtop : ⨆ j, N j = ⊤) (hNsimple : ∀ j, IsSimpleModule (WordAlgebra d) (N j))
    (hN' : iSupIndep N') (hN'top : ⨆ k, N' k = ⊤)
    (hN'simple : ∀ k, IsSimpleModule (WordAlgebra d) (N' k)) :
    SameMPV₂Pos A B ↔
      ∃ e : {j // ∃ (i : Fin d) (x : N j), (ofWord [i] : WordAlgebra d) • x ≠ 0} ≃
          {k // ∃ (i : Fin d) (x : N' k), (ofWord [i] : WordAlgebra d) • x ≠ 0},
        ∀ j, Nonempty (N j.1 ≃ₗ[WordAlgebra d] N' (e j).1) :=
  ⟨exists_equiv_forall_nonempty_linearEquiv_of_sameMPV₂Pos N N' hN hNtop hNsimple hN' hN'top
      hN'simple,
    fun ⟨e, he⟩ => sameMPV₂Pos_of_exists_equiv_forall_nonempty_linearEquiv N N' hN hNtop hNsimple
      hN' hN'top hN'simple e he⟩

/-- **Completely reducible tensors of equal bond dimension**. Two completely reducible tensors of
the same bond dimension have the same states if and only if they are gauge equivalent. -/
theorem sameMPV₂Pos_iff_isGaugeRelated_of_isSemisimpleModule
    (hA : IsSemisimpleModule (WordAlgebra d) A.WordModule)
    (hB : IsSemisimpleModule (WordAlgebra d) B.WordModule) (hD : DA = DB) :
    SameMPV₂Pos A B ↔ IsGaugeRelated A B := by
  refine ⟨fun h => ?_, IsGaugeRelated.sameMPV₂Pos⟩
  obtain ⟨SA, hindA, hsupA, hsimA⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (WordAlgebra d) A.WordModule
  obtain ⟨SB, hindB, hsupB, hsimB⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (WordAlgebra d) B.WordModule
  have hNA := (sSupIndep_iff SA).1 hindA
  have hNB := (sSupIndep_iff SB).1 hindB
  have htopA : ⨆ m : SA, (m : Submodule (WordAlgebra d) A.WordModule) = ⊤ := by
    rw [← sSup_eq_iSup']; exact hsupA
  have htopB : ⨆ m : SB, (m : Submodule (WordAlgebra d) B.WordModule) = ⊤ := by
    rw [← sSup_eq_iSup']; exact hsupB
  obtain ⟨e, he⟩ := exists_equiv_forall_nonempty_linearEquiv_of_sameMPV₂Pos _ _ hNA htopA
    (fun m => hsimA m.1 m.2) hNB htopB (fun m => hsimB m.1 m.2) h
  exact isGaugeRelated_of_exists_equiv_forall_nonempty_linearEquiv _ _ hNA htopA
    (fun m => hsimA m.1 m.2) hNB htopB (fun m => hsimB m.1 m.2) hD e he

/-- **Completely reducible tensors without zero summands**. Let the word modules of `A` and `B` be
the internal direct sums of the simple submodules `N j` and `N' k`, on each of which some letter
acts as a nonzero map. Then `A` and `B` have the same states if and only if they are gauge
equivalent. -/
theorem sameMPV₂Pos_iff_isGaugeRelated_of_forall_exists_smul_ne_zero {ι κ : Type*}
    (N : ι → Submodule (WordAlgebra d) A.WordModule)
    (N' : κ → Submodule (WordAlgebra d) B.WordModule)
    (hN : iSupIndep N) (hNtop : ⨆ j, N j = ⊤) (hNsimple : ∀ j, IsSimpleModule (WordAlgebra d) (N j))
    (hN' : iSupIndep N') (hN'top : ⨆ k, N' k = ⊤)
    (hN'simple : ∀ k, IsSimpleModule (WordAlgebra d) (N' k))
    (h0 : ∀ j, ∃ (i : Fin d) (x : N j), (ofWord [i] : WordAlgebra d) • x ≠ 0)
    (h0' : ∀ k, ∃ (i : Fin d) (x : N' k), (ofWord [i] : WordAlgebra d) • x ≠ 0) :
    SameMPV₂Pos A B ↔ IsGaugeRelated A B := by
  refine ⟨fun h => ?_, IsGaugeRelated.sameMPV₂Pos⟩
  obtain ⟨e, he⟩ := exists_equiv_forall_nonempty_linearEquiv_of_sameMPV₂Pos N N' hN hNtop
    hNsimple hN' hN'top hN'simple h
  let f : ι ≃ κ :=
    (Equiv.subtypeUnivEquiv h0).symm.trans (e.trans (Equiv.subtypeUnivEquiv h0'))
  exact isGaugeRelated_iff_nonempty_linearEquiv_wordModule.2
    (nonempty_linearEquiv_of_iSupIndep N N' hN hNtop hN' hN'top f fun j => he ⟨j, h0 j⟩)

/-! ### Unitary gauges -/

variable {D : ℕ}

/-- **Unitary gauges, existence**. Let `A` and `B` be
irreducible and right-normalized, `∑_i A^i A^{i†} = 1 = ∑_i B^i B^{i†}`. Every gauge `X` with
`B^i = X A^i X⁻¹` is a nonzero scalar times a unitary. -/
theorem exists_ne_zero_and_exists_mem_unitaryGroup_eq_smul {A B : MPSTensor d D}
    (hA : Matrix.IsIrreducibleAction A) (hB : Matrix.IsIrreducibleAction B)
    (hAu : Kraus.IsUnital A) (hBu : Kraus.IsUnital B) (X : GL (Fin D) ℂ)
    (hX : ∀ i, B i = (X : Matrix (Fin D) (Fin D) ℂ) * A i *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ U ∈ Matrix.unitaryGroup (Fin D) ℂ,
      (X : Matrix (Fin D) (Fin D) ℂ) = c • U := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact ⟨1, one_ne_zero, 1, one_mem _, Subsingleton.elim _ _⟩
  have : NeZero D := ⟨hD.ne'⟩
  -- the adjoint tensors are left-canonical and irreducible
  have hAt : Kraus.IsIrreducibleFamily (fun i => (A i)ᴴ) :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM _
      (Kraus.isIrreducibleMap_mapLM_conjTranspose A
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A
          ((Kraus.isIrreducibleAction_iff_isIrreducibleFamily A).1 hA)))
  have hBt : Kraus.IsIrreducibleFamily (fun i => (B i)ᴴ) :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM _
      (Kraus.isIrreducibleMap_mapLM_conjTranspose B
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B
          ((Kraus.isIrreducibleAction_iff_isIrreducibleFamily B).1 hB)))
  have hAl : IsLeftCanonical (fun i => (A i)ᴴ) := by
    change ∑ i, ((A i)ᴴ)ᴴ * (A i)ᴴ = 1
    simp only [Matrix.conjTranspose_conjTranspose]
    exact hAu
  have hBl : IsLeftCanonical (fun i => (B i)ᴴ) := by
    change ∑ i, ((B i)ᴴ)ᴴ * (B i)ᴴ = 1
    simp only [Matrix.conjTranspose_conjTranspose]
    exact hBu
  -- they are gauge equivalent through `X^{-†}`
  let Y : GL (Fin D) ℂ :=
    ⟨((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)ᴴ, (X : Matrix (Fin D) (Fin D) ℂ)ᴴ,
      by rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one],
      by rw [← Matrix.conjTranspose_mul, Units.inv_mul, Matrix.conjTranspose_one]⟩
  have hY : ∀ i, (fun i => (B i)ᴴ) i = (1 : ℂ) • ((Y : Matrix (Fin D) (Fin D) ℂ) *
      (fun i => (A i)ᴴ) i * ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
    intro i
    change (B i)ᴴ = (1 : ℂ) • (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)ᴴ * (A i)ᴴ *
      (X : Matrix (Fin D) (Fin D) ℂ)ᴴ)
    rw [one_smul, hX i, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  obtain ⟨U, -, hU⟩ := exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible Y 1
    one_ne_zero hY hAl hBl hAt hBt
  have hBU : ∀ i, B i = (U : Matrix (Fin D) (Fin D) ℂ) * A i * (U : Matrix (Fin D) (Fin D) ℂ)ᴴ :=
    fun i => by
      simpa only [one_smul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.mul_assoc] using congrArg Matrix.conjTranspose (hU i)
  have hUU : (U : Matrix (Fin D) (Fin D) ℂ)ᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 U.2
  have hUU' : (U : Matrix (Fin D) (Fin D) ℂ) * (U : Matrix (Fin D) (Fin D) ℂ)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 U.2
  -- `U† X` commutes with every letter of `A`, hence is a scalar (Schur)
  have hcomm : ∀ i, (U : Matrix (Fin D) (Fin D) ℂ)ᴴ * X * A i =
      A i * ((U : Matrix (Fin D) (Fin D) ℂ)ᴴ * X) := by
    intro i
    have hXA : (X : Matrix (Fin D) (Fin D) ℂ) * A i = B i * X := by
      rw [hX i, Matrix.mul_assoc ((X : Matrix (Fin D) (Fin D) ℂ) * A i), Units.inv_mul,
        Matrix.mul_one]
    rw [Matrix.mul_assoc, hXA, hBU i]
    simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_intertwines hA hcomm
  have hXc : (X : Matrix (Fin D) (Fin D) ℂ) = c • (U : Matrix (Fin D) (Fin D) ℂ) := by
    calc (X : Matrix (Fin D) (Fin D) ℂ)
        = U * ((U : Matrix (Fin D) (Fin D) ℂ)ᴴ * X) := by
          rw [← Matrix.mul_assoc, hUU', Matrix.one_mul]
      _ = c • (U : Matrix (Fin D) (Fin D) ℂ) := by rw [hc, Matrix.mul_smul, Matrix.mul_one]
  refine ⟨c, fun hc0 => ?_, U, U.2, hXc⟩
  have h1 : (X : Matrix (Fin D) (Fin D) ℂ) * ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
    1 := Units.mul_inv X
  rw [hXc, hc0, zero_smul, Matrix.zero_mul] at h1
  exact zero_ne_one h1

/-- **Unitary gauges, uniqueness up to a phase**. For an
irreducible `A`, two unitaries `U`, `U'` with `B^i = U A^i U† = U' A^i U'†` differ by a phase. In
particular the unitary of `exists_ne_zero_and_exists_mem_unitaryGroup_eq_smul` is unique up to a
phase. -/
theorem exists_norm_eq_one_and_eq_smul_of_mem_unitaryGroup {A B : MPSTensor d D}
    (hA : Matrix.IsIrreducibleAction A) {U U' : Matrix (Fin D) (Fin D) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (hU' : U' ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (h : ∀ i, B i = U * A i * Uᴴ) (h' : ∀ i, B i = U' * A i * U'ᴴ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ U' = c • U := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact ⟨1, norm_one, Subsingleton.elim _ _⟩
  have hUU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hU
  have hU'U' : U'ᴴ * U' = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hU'
  have hUU' : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hU
  -- `U'† U` commutes with every letter of `A`, hence is a scalar (Schur)
  have hcomm : ∀ i, U'ᴴ * U * A i = A i * (U'ᴴ * U) := by
    intro i
    calc U'ᴴ * U * A i = U'ᴴ * (U * A i * Uᴴ) * U := by
          simp only [Matrix.mul_assoc, hUU, Matrix.mul_one]
      _ = U'ᴴ * (U' * A i * U'ᴴ) * U := by rw [← h i, h' i]
      _ = A i * (U'ᴴ * U) := by simp only [← Matrix.mul_assoc, hU'U', Matrix.one_mul]
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_intertwines hA hcomm
  have hc' : Uᴴ * U' = star c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    have := congrArg Matrix.conjTranspose hc
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one] at this
  have hU'eq : U' = star c • U := by
    calc U' = U * (Uᴴ * U') := by rw [← Matrix.mul_assoc, hUU', Matrix.one_mul]
      _ = star c • U := by rw [hc', Matrix.mul_smul, Matrix.mul_one]
  have hcc : c * star c = 1 := by
    have h1 : U'ᴴ * U' = (c * star c) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
      rw [hU'eq, Matrix.conjTranspose_smul, star_star, Matrix.smul_mul, Matrix.mul_smul, hUU,
        smul_smul]
    rw [hU'U'] at h1
    have h2 := congrFun (congrFun h1 ⟨0, hD⟩) ⟨0, hD⟩
    simpa using h2.symm
  refine ⟨star c, ?_, hU'eq⟩
  have hn : ‖c‖ ^ 2 = 1 := by
    have h3 : (Complex.normSq c : ℂ) = 1 := by rw [← Complex.mul_conj]; exact hcc
    rw [← Complex.normSq_eq_norm_sq]
    exact_mod_cast h3
  rw [norm_star]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 hn

end MPSTensor
