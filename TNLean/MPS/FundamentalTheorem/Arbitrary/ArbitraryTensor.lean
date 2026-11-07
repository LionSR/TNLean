/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Order.JordanHolder
import Mathlib.Topology.Instances.Matrix
import QICLean.Algebra.MatrixFamilyAction
import QICLean.Kraus.IrreducibleAction
import TNLean.Algebra.Subquotient
import TNLean.MPS.Chain.VaryingBondOBC
import TNLean.MPS.FundamentalTheorem.Reduction.FlagData
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlock
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessBlocks
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessAllReductions
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace
import TNLean.MPS.FundamentalTheorem.Arbitrary.Basic
import TNLean.MPS.FundamentalTheorem.Arbitrary.FlagExistence
import TNLean.MPS.FundamentalTheorem.Arbitrary.WordModuleGauge
import TNLean.MPS.CanonicalForm.Existence
import TNLean.MPS.Core.TracePairing
import TNLean.MPS.Preparation.MinimalCutRepresentationPadding

/-!
# The fundamental theorem for arbitrary tensors

Two tensors `B`, `B'` with `d` letters, of arbitrary bond dimensions and in no canonical form, have
the same periodic states at every positive length exactly when both have multi-block reductions
onto one finite family of admissible tensors (irreducible, with a nonzero letter), and this family
is determined by the states up to relabelling and gauge. Equivalently, any
invariant flags (composition series of the word modules) of the two tensors have their nonzero
steps isomorphic in pairs, and every invariant flag is the flag of a reduction. Two tensors
with reductions onto one family have a common block diagonal limit under conjugation, after padding
to a common bond dimension, and two tensors with such a limit have the same states.

A tensor with a reduction onto `(C_s)` has the states of `⨁_s C_s`
(`MultiBlockCompression.trace_evalWord_eq_sum`), and the numbers of zero blocks are fixed by
`MultiBlockCompression.dim_eq`.

## Main definitions

* `MPSTensor.stepTensor`: the tensor of a step of a composition series, in chosen coordinates.

## Main results

* `MPSTensor.sameMPV₂Pos_iff_exists_multiBlockCompression`.
* `MPSTensor.MultiBlockCompression.z_sub_z_eq_and_exists_equiv_isGaugeRelated_of_sameMPV₂Pos`.
* `MPSTensor.exists_compositionSeries_wordModule`,
  `MPSTensor.finrank_subquot_eq_one_of_forall_smul_eq_zero`,
  `MPSTensor.nonempty_linearEquiv_wordModule_stepTensor`,
  `MPSTensor.isIrreducibleAction_stepTensor`, `MPSTensor.exists_stepTensor_apply_ne_zero`,
  `MPSTensor.isGaugeRelated_stepTensor`.
* `MPSTensor.tfae_sameMPV₂Pos_compositionSeries`.
* `MPSTensor.SameMPV₂Pos.exists_equiv_isGaugeRelated_stepTensor`: matched steps of any two
  invariant flags have gauge equivalent tensors.
* `MPSTensor.exists_multiBlockCompression_mem_iff_and_flag_eq_and_ord_eq`.
* `MPSTensor.MultiBlockCompression.exists_isUnit_and_tendsto_mul_zeroPad_mul_inv`,
  `MPSTensor.sameMPV₂Pos_of_tendsto_mul_zeroPad_mul_inv`.
-/

open scoped Matrix Topology
open Filter

namespace MPSTensor

open WordAlgebra

variable {d DB DB' : ℕ}

/-! ### Auxiliary facts -/

/-- A sum of word traces over a family each of whose members is gauge equivalent to the
representative of its class is a sum over the classes weighted by the class multiplicities. -/
private theorem sum_trace_evalWord_eq_sum_card_mul {γ Q : Type*} [Fintype γ] [Fintype Q]
    [DecidableEq Q] (φ : γ → Q) {Dg : γ → ℕ} (E : ∀ c, MPSTensor d (Dg c)) {Dq : Q → ℕ}
    (C' : ∀ q, MPSTensor d (Dq q)) (hE : ∀ c, IsGaugeRelated (E c) (C' (φ c)))
    (w : List (Fin d)) :
    ∑ c, Matrix.trace (Kraus.evalWord (E c) w) =
      ∑ q, ((Finset.univ.filter fun c => φ c = q).card : ℂ) *
        Matrix.trace (Kraus.evalWord (C' q) w) := by
  rw [← Finset.sum_fiberwise Finset.univ φ]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => Matrix.trace (Kraus.evalWord (C' q) w)),
    Finset.sum_const, nsmul_eq_mul]
  intro c hc
  obtain ⟨-, rfl⟩ := Finset.mem_filter.1 hc
  exact (hE c).trace_evalWord_eq w

/-- **Counting gauge classes.** Two finite families of admissible tensors
whose word traces have equal sums on every nonempty word are related by a bijection pairing gauge
equivalent members: the multiplicities of each gauge class agree by the independence of the traces
of pairwise non-gauge-equivalent admissible tensors. -/
private theorem exists_equiv_isGaugeRelated_of_sum_trace_eq {α β : Type*} [Fintype α]
    [Fintype β] {Da : α → ℕ} {Db : β → ℕ} (A : ∀ a, MPSTensor d (Da a))
    (A' : ∀ b, MPSTensor d (Db b)) (hirr : ∀ a, Matrix.IsIrreducibleAction (A a))
    (hlet : ∀ a, ∃ i, A a i ≠ 0) (hirr' : ∀ b, Matrix.IsIrreducibleAction (A' b))
    (hlet' : ∀ b, ∃ i, A' b i ≠ 0)
    (h : ∀ w : List (Fin d), w ≠ [] →
      ∑ a, Matrix.trace (Kraus.evalWord (A a) w) = ∑ b, Matrix.trace (Kraus.evalWord (A' b) w)) :
    ∃ τ : α ≃ β, ∀ a, IsGaugeRelated (A a) (A' (τ a)) := by
  classical
  let DJ : α ⊕ β → ℕ := Sum.elim Da Db
  let T : ∀ j, MPSTensor d (DJ j) := Sum.rec (motive := fun j => MPSTensor d (DJ j)) A A'
  have hirrT : ∀ j, Matrix.IsIrreducibleAction (T j) := Sum.rec hirr hirr'
  have hletT : ∀ j, ∃ i, T j i ≠ 0 := Sum.rec hlet hlet'
  let r : Setoid (α ⊕ β) :=
    ⟨fun j k => IsGaugeRelated (T j) (T k),
      ⟨fun j => IsGaugeRelated.refl _, fun h => h.symm, fun h h' => h.trans h'⟩⟩
  let Qt := Quotient r
  have : Fintype Qt := Fintype.ofFinite Qt
  let C' : ∀ q : Qt, MPSTensor d (DJ q.out) := fun q => T q.out
  have hne : Pairwise fun q q' : Qt => ¬ IsGaugeRelated (C' q) (C' q') := by
    intro q q' hqq' hg
    apply hqq'
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    exact Quotient.sound hg
  have hrep : ∀ j, IsGaugeRelated (T j) (C' (Quotient.mk r j)) := fun j =>
    IsGaugeRelated.symm (Quotient.mk_out (s := r) j)
  let f : α → Qt := fun a => Quotient.mk r (Sum.inl a)
  let g : β → Qt := fun b => Quotient.mk r (Sum.inr b)
  have hcard : ∀ q, (Finset.univ.filter fun a => f a = q).card =
      (Finset.univ.filter fun b => g b = q).card := by
    have h0 := eq_zero_of_forall_sum_mul_trace_evalWord_eq_zero C' (fun q => hirrT _) hne
      (fun q => hletT _)
      (fun q => ((Finset.univ.filter fun a => f a = q).card : ℂ) -
        (Finset.univ.filter fun b => g b = q).card) (fun w hw => by
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [← sum_trace_evalWord_eq_sum_card_mul f A C' (fun a => hrep (Sum.inl a)) w,
          ← sum_trace_evalWord_eq_sum_card_mul g A' C' (fun b => hrep (Sum.inr b)) w,
          h w hw, sub_self])
    intro q
    have := congrFun h0 q
    simp only [Pi.zero_apply, sub_eq_zero] at this
    exact_mod_cast this
  have E : ∀ q, {a // f a = q} ≃ {b // g b = q} := fun q =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype, hcard q])
  let τ : α ≃ β := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight E).trans (Equiv.sigmaFiberEquiv g))
  refine ⟨τ, fun a => ?_⟩
  have hq : g (τ a) = f a := (E (f a) ⟨a, rfl⟩).2
  exact Quotient.exact (s := r) hq.symm

/-! ### The theorem and the uniqueness of the family -/

/-- **The fundamental theorem for arbitrary tensors**. Two tensors have the same states if and only
if there is a finite family of admissible tensors onto which both have multi-block reductions. -/
theorem sameMPV₂Pos_iff_exists_multiBlockCompression {B : MPSTensor d DB}
    {B' : MPSTensor d DB'} :
    SameMPV₂Pos B B' ↔
      ∃ (r : ℕ) (D : Fin r → ℕ) (C : ∀ k, MPSTensor d (D k)),
        (∀ k, Matrix.IsIrreducibleAction (C k)) ∧ (∀ k, ∃ i, C k i ≠ 0) ∧
          Nonempty (MultiBlockCompression B Finset.univ C) ∧
            Nonempty (MultiBlockCompression B' Finset.univ C) := by
  classical
  constructor
  · intro h
    obtain ⟨r, dim, blocks, hIrr, hlet, -, hsame, -⟩ :=
      exists_irreducible_blockDecomp_nonzeroBlocks B'
    have hirr : ∀ k, Matrix.IsIrreducibleAction (blocks k) := fun k =>
      (Kraus.isIrreducibleAction_iff_isIrreducibleFamily _).2 (hIrr k)
    have htr' : ∀ w : List (Fin d), w ≠ [] → Matrix.trace (Kraus.evalWord B' w) =
        ∑ k ∈ Finset.univ, Matrix.trace (Kraus.evalWord (blocks k) w) := by
      intro w hw
      rw [hsame.trace_evalWord w hw]
      have := mpv_toTensorFromBlocks_eq_sum (d := d) (fun _ : Fin r => (1 : ℂ)) blocks w.get
      simpa [mpv, coeff, List.ofFn_get] using this
    have htr : ∀ w : List (Fin d), w ≠ [] → Matrix.trace (Kraus.evalWord B w) =
        ∑ k ∈ Finset.univ, Matrix.trace (Kraus.evalWord (blocks k) w) := fun w hw =>
      (h.trace_evalWord w hw).trans (htr' w hw)
    obtain ⟨P, -⟩ := exists_multiBlockCompression_z_eq_of_isIrreducibleAction Finset.univ blocks
      (fun k _ => hirr k) (fun k _ => hlet k) B htr
    obtain ⟨Q, -⟩ := exists_multiBlockCompression_z_eq_of_isIrreducibleAction Finset.univ blocks
      (fun k _ => hirr k) (fun k _ => hlet k) B' htr'
    exact ⟨r, dim, blocks, hirr, hlet, ⟨P⟩, ⟨Q⟩⟩
  · rintro ⟨r, D, C, -, -, ⟨P⟩, ⟨Q⟩⟩
    refine sameMPV₂Pos_iff_forall_trace_evalWord_eq.2 fun w hw => ?_
    rw [P.trace_evalWord_eq_sum w hw, Q.trace_evalWord_eq_sum w hw]

namespace MultiBlockCompression

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {D : ι → ℕ} {D' : κ → ℕ}
  {S : Finset ι} {S' : Finset κ} {C : ∀ s, MPSTensor d (D s)} {C' : ∀ t, MPSTensor d (D' t)}
  {B : MPSTensor d DB} {B' : MPSTensor d DB'}

/-- **The family is determined by the states**.
If `B` has a reduction onto an admissible family `(C_s)_{s ∈ S}` with `z` zero blocks, `B'` one
onto an admissible family `(C'_t)_{t ∈ S'}` with `z'` zero blocks, and `B`, `B'` have the same
states, then `z - z' = D_B - D_{B'}` and a bijection `S ≃ S'` pairs gauge equivalent blocks. -/
theorem z_sub_z_eq_and_exists_equiv_isGaugeRelated_of_sameMPV₂Pos
    (P : MultiBlockCompression B S C) (Q : MultiBlockCompression B' S' C')
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    (hirr' : ∀ t ∈ S', Matrix.IsIrreducibleAction (C' t)) (hlet' : ∀ t ∈ S', ∃ i, C' t i ≠ 0)
    (h : SameMPV₂Pos B B') :
    (P.z : ℤ) - Q.z = (DB : ℤ) - DB' ∧
      ∃ τ : {s // s ∈ S} ≃ {t // t ∈ S'}, ∀ s, IsGaugeRelated (C s.1) (C' (τ s).1) := by
  obtain ⟨τ, hτ⟩ := exists_equiv_isGaugeRelated_of_sum_trace_eq (fun s : {s // s ∈ S} => C s.1)
    (fun t : {t // t ∈ S'} => C' t.1) (fun s => hirr s.1 s.2) (fun s => hlet s.1 s.2)
    (fun t => hirr' t.1 t.2) (fun t => hlet' t.1 t.2) (fun w hw => by
      rw [Finset.sum_coe_sort S (fun s => Matrix.trace (Kraus.evalWord (C s) w)),
        Finset.sum_coe_sort S' (fun t => Matrix.trace (Kraus.evalWord (C' t) w)),
        ← P.trace_evalWord_eq_sum w hw, ← Q.trace_evalWord_eq_sum w hw, h.trace_evalWord w hw])
  refine ⟨?_, τ, hτ⟩
  have hD : ∑ s ∈ S, D s = ∑ t ∈ S', D' t := by
    rw [← Finset.sum_coe_sort S D, ← Finset.sum_coe_sort S' D']
    exact Fintype.sum_equiv τ _ _ fun s => (hτ s).dim_eq
  have h1 := P.dim_eq
  have h2 := Q.dim_eq
  omega

end MultiBlockCompression

/-! ### Invariant flags -/

section Flag

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
  [IsScalarTower ℂ (WordAlgebra d) M]

omit [Module ℂ M] [IsScalarTower ℂ (WordAlgebra d) M] in
/-- A step of a composition series is a simple module. -/
private theorem isSimpleModule_subquot (s : CompositionSeries (Submodule (WordAlgebra d) M))
    (k : Fin s.length) :
    IsSimpleModule (WordAlgebra d) (Submodule.subquot (s k.castSucc) (s k.succ)) :=
  (covBy_iff_quot_is_simple (s.lt_succ k).le).1 (s.step k)

/-- **Every tensor has an invariant flag**. The word module of a tensor has
a composition series from `0` to the whole bond space. -/
theorem exists_compositionSeries_wordModule (B : MPSTensor d DB) :
    ∃ s : CompositionSeries (Submodule (WordAlgebra d) B.WordModule), s.head = ⊥ ∧ s.last = ⊤ := by
  have : IsNoetherian (WordAlgebra d) B.WordModule := isNoetherian_of_tower ℂ inferInstance
  have : IsArtinian (WordAlgebra d) B.WordModule := isArtinian_of_tower ℂ inferInstance
  exact exists_compositionSeries_of_isNoetherian_isArtinian _ _

/-- **Zero steps are lines**. A step of an invariant flag on which every
letter acts as zero is one-dimensional. -/
theorem finrank_subquot_eq_one_of_forall_smul_eq_zero
    (s : CompositionSeries (Submodule (WordAlgebra d) M)) (k : Fin s.length)
    (h : ∀ (i : Fin d) (x : Submodule.subquot (s k.castSucc) (s k.succ)),
      (ofWord [i] : WordAlgebra d) • x = 0) :
    Module.finrank ℂ (Submodule.subquot (s k.castSucc) (s k.succ)) = 1 := by
  have := isSimpleModule_subquot s k
  exact finrank_eq_one_of_isSimpleModule_of_forall_smul_eq_zero h

/-- **The tensor of a step in coordinates**. For a step
`s_k / s_{k-1}` of a composition series and coordinates `ψ` of the step, the tensor whose letter
`i` is the matrix, in the coordinates `ψ`, of the one-letter word `i` acting on the step. -/
noncomputable def stepTensor (s : CompositionSeries (Submodule (WordAlgebra d) M))
    (k : Fin s.length) {n : ℕ}
    (ψ : Submodule.subquot (s k.castSucc) (s k.succ) ≃ₗ[ℂ] (Fin n → ℂ)) : MPSTensor d n :=
  fun i => LinearMap.toMatrix'
    (ψ.conj (Algebra.lsmul ℂ ℂ (Submodule.subquot (s k.castSucc) (s k.succ)) (ofWord [i])))

/-- **A step is the word module of its tensor**. The step `s_k / s_{k-1}`
is isomorphic, as a module over the word algebra, to the word module of its tensor in any
coordinates `ψ`. -/
theorem nonempty_linearEquiv_wordModule_stepTensor
    (s : CompositionSeries (Submodule (WordAlgebra d) M)) (k : Fin s.length) {n : ℕ}
    (ψ : Submodule.subquot (s k.castSucc) (s k.succ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    Nonempty (Submodule.subquot (s k.castSucc) (s k.succ) ≃ₗ[WordAlgebra d]
      (stepTensor s k ψ).WordModule) := by
  refine ⟨linearEquivOfLetter (ψ.trans (stepTensor s k ψ).wordRep.asModuleEquiv.symm)
    fun i x => ?_⟩
  apply (stepTensor s k ψ).wordRep.asModuleEquiv.injective
  rw [asModuleEquiv_ofWord_smul]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, Kraus.evalWord,
    Matrix.mul_one, stepTensor, LinearMap.toMatrix'_mulVec, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_apply_apply, Algebra.lsmul_coe]

/-- **A step written in a basis is irreducible**. The tensor of a step of
an invariant flag in any coordinates `ψ` is irreducible. -/
theorem isIrreducibleAction_stepTensor
    (s : CompositionSeries (Submodule (WordAlgebra d) M)) (k : Fin s.length) {n : ℕ}
    (ψ : Submodule.subquot (s k.castSucc) (s k.succ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    Matrix.IsIrreducibleAction (stepTensor s k ψ) := by
  have := isSimpleModule_subquot s k
  obtain ⟨e⟩ := nonempty_linearEquiv_wordModule_stepTensor s k ψ
  exact ((isIrreducibleAction_and_pos_iff_isSimpleModule _).2 (IsSimpleModule.congr e.symm)).1

/-- **A nonzero step written in a basis has a nonzero letter**. If some
letter acts as a nonzero map on a step, the tensor of that step in coordinates `ψ` has a nonzero
letter; with `isIrreducibleAction_stepTensor` it is admissible. -/
theorem exists_stepTensor_apply_ne_zero
    (s : CompositionSeries (Submodule (WordAlgebra d) M)) (k : Fin s.length) {n : ℕ}
    (ψ : Submodule.subquot (s k.castSucc) (s k.succ) ≃ₗ[ℂ] (Fin n → ℂ))
    (h : ∃ (i : Fin d) (x : Submodule.subquot (s k.castSucc) (s k.succ)),
      (ofWord [i] : WordAlgebra d) • x ≠ 0) :
    ∃ i : Fin d, stepTensor s k ψ i ≠ 0 := by
  obtain ⟨i, x, hx⟩ := h
  refine ⟨i, fun h0 => hx ?_⟩
  have h1 : ψ.conj (Algebra.lsmul ℂ ℂ (Submodule.subquot (s k.castSucc) (s k.succ))
      (ofWord [i] : WordAlgebra d)) = 0 :=
    LinearMap.toMatrix'.injective (by rw [map_zero]; exact h0)
  have h2 := LinearMap.congr_fun h1 (ψ x)
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, LinearMap.zero_apply,
    LinearEquiv.map_eq_zero_iff] at h2
  exact h2

/-- **A step determines its tensor up to gauge**. The tensors of one step of
an invariant flag in two coordinate systems `ψ`, `ψ'` are gauge equivalent. -/
theorem isGaugeRelated_stepTensor
    (s : CompositionSeries (Submodule (WordAlgebra d) M)) (k : Fin s.length) {n n' : ℕ}
    (ψ : Submodule.subquot (s k.castSucc) (s k.succ) ≃ₗ[ℂ] (Fin n → ℂ))
    (ψ' : Submodule.subquot (s k.castSucc) (s k.succ) ≃ₗ[ℂ] (Fin n' → ℂ)) :
    IsGaugeRelated (stepTensor s k ψ) (stepTensor s k ψ') := by
  obtain ⟨e⟩ := nonempty_linearEquiv_wordModule_stepTensor s k ψ
  obtain ⟨e'⟩ := nonempty_linearEquiv_wordModule_stepTensor s k ψ'
  exact isGaugeRelated_of_linearEquiv (e.symm.trans e')

/-- A word acts on a step through its letters, so its trace is the trace of the step tensor. -/
private theorem trace_evalWord_stepTensor (s : CompositionSeries (Submodule (WordAlgebra d) M))
    (k : Fin s.length) {n : ℕ}
    (ψ : Submodule.subquot (s k.castSucc) (s k.succ) ≃ₗ[ℂ] (Fin n → ℂ)) (w : List (Fin d)) :
    Matrix.trace (Kraus.evalWord (stepTensor s k ψ) w) =
      traceWord (Submodule.subquot (s k.castSucc) (s k.succ)) w := by
  obtain ⟨e⟩ := nonempty_linearEquiv_wordModule_stepTensor s k ψ
  rw [traceWord_congr e, traceWord_wordModule]

/-- The steps of a flag of a finite-dimensional module are finite-dimensional. -/
private instance finiteDimensional_subquot [FiniteDimensional ℂ M]
    (A A' : Submodule (WordAlgebra d) M) : FiniteDimensional ℂ (Submodule.subquot A A') := by
  have : FiniteDimensional ℂ A' :=
    Module.Finite.of_injective (A'.subtype.restrictScalars ℂ) A'.subtype_injective
  exact LinearEquiv.finiteDimensional
    (Submodule.Quotient.restrictScalarsEquiv ℂ (A.comap A'.subtype))

/-- The nonzero steps of a composition series: those on which some letter acts as a nonzero
map. -/
private abbrev NonzeroStep (s : CompositionSeries (Submodule (WordAlgebra d) M)) : Type _ :=
  {k : Fin s.length // ∃ (i : Fin d) (x : Submodule.subquot (s k.castSucc) (s k.succ)),
    (ofWord [i] : WordAlgebra d) • x ≠ 0}

/-- The tensor of a step of a flag of a finite-dimensional module, in a chosen basis. -/
private noncomputable abbrev stepTensorFinBasis [FiniteDimensional ℂ M]
    (s : CompositionSeries (Submodule (WordAlgebra d) M)) (k : Fin s.length) :
    MPSTensor d (Module.finrank ℂ (Submodule.subquot (s k.castSucc) (s k.succ))) :=
  stepTensor s k (Module.finBasis ℂ (Submodule.subquot (s k.castSucc) (s k.succ))).equivFun

/-- **Traces along an invariant flag, nonzero steps only**:
for a composition series from `0` to the whole module and a nonempty word, the trace of the word
on the module is the sum of its traces on the nonzero steps (the zero steps contribute
nothing). -/
private theorem traceWord_eq_sum_nonzeroStep [FiniteDimensional ℂ M]
    (s : CompositionSeries (Submodule (WordAlgebra d) M)) [Fintype (NonzeroStep s)]
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) {w : List (Fin d)} (hw : w ≠ []) :
    traceWord M w =
      ∑ k : NonzeroStep s, traceWord (Submodule.subquot (s k.1.castSucc) (s k.1.succ)) w := by
  classical
  have hsum : traceWord M w =
      ∑ k : Fin s.length, traceWord (Submodule.subquot (s k.castSucc) (s k.succ)) w := by
    rw [← traceWord_eq_sum_subquot s.toFun h0 s.strictMono.monotone w]
    rw [show s.toFun (Fin.last s.length) = ⊤ from h1]
    exact traceWord_congr Submodule.topEquiv.symm w
  rw [hsum, ← Finset.sum_filter_of_ne (p := fun k : Fin s.length => ∃ (i : Fin d)
      (x : Submodule.subquot (s k.castSucc) (s k.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0)]
  · exact Finset.sum_subtype _ (fun k => Finset.mem_filter.trans
      (and_iff_right (Finset.mem_univ _))) _
  · intro k _ hk
    by_contra hnot
    simp only [not_exists, not_not] at hnot
    exact hk (traceWord_eq_zero_of_forall_smul_eq_zero hnot hw)

variable {M' : Type*} [AddCommGroup M'] [Module ℂ M'] [Module (WordAlgebra d) M']
  [IsScalarTower ℂ (WordAlgebra d) M']

/-- **Equal traces match the nonzero steps**: if two finite-dimensional
modules have equal traces on every nonempty word, the nonzero steps of any composition series of
the first and of the second are matched by a bijection pairing isomorphic steps. This is the
counting argument above applied to the nonzero steps written in bases. -/
private theorem exists_equiv_nonzeroStep_of_traceWord_eq [FiniteDimensional ℂ M]
    [FiniteDimensional ℂ M'] (s : CompositionSeries (Submodule (WordAlgebra d) M))
    (s' : CompositionSeries (Submodule (WordAlgebra d) M')) (h0 : s.head = ⊥) (h1 : s.last = ⊤)
    (h0' : s'.head = ⊥) (h1' : s'.last = ⊤)
    (htr : ∀ w : List (Fin d), w ≠ [] → traceWord M w = traceWord M' w) :
    ∃ e : NonzeroStep s ≃ NonzeroStep s', ∀ k,
      Nonempty (Submodule.subquot (s k.1.castSucc) (s k.1.succ) ≃ₗ[WordAlgebra d]
        Submodule.subquot (s' (e k).1.castSucc) (s' (e k).1.succ)) := by
  classical
  obtain ⟨τ, hτ⟩ := exists_equiv_isGaugeRelated_of_sum_trace_eq
    (fun k : NonzeroStep s => stepTensorFinBasis s k.1)
    (fun k : NonzeroStep s' => stepTensorFinBasis s' k.1)
    (fun k => isIrreducibleAction_stepTensor _ _ _)
    (fun k => exists_stepTensor_apply_ne_zero _ _ _ k.2)
    (fun k => isIrreducibleAction_stepTensor _ _ _)
    (fun k => exists_stepTensor_apply_ne_zero _ _ _ k.2) (fun w hw => by
      simp only [stepTensorFinBasis, trace_evalWord_stepTensor]
      rw [← traceWord_eq_sum_nonzeroStep s h0 h1 hw, ← traceWord_eq_sum_nonzeroStep s' h0' h1' hw,
        htr w hw])
  refine ⟨τ, fun k => ?_⟩
  obtain ⟨a⟩ := nonempty_linearEquiv_wordModule_stepTensor s k.1
    (Module.finBasis ℂ (Submodule.subquot (s k.1.castSucc) (s k.1.succ))).equivFun
  obtain ⟨b⟩ := nonempty_linearEquiv_wordModule_stepTensor s' (τ k).1
    (Module.finBasis ℂ (Submodule.subquot (s' (τ k).1.castSucc) (s' (τ k).1.succ))).equivFun
  obtain ⟨c⟩ := nonempty_linearEquiv_wordModule_of_isGaugeRelated (hτ k)
  exact ⟨(a.trans c).trans b.symm⟩

/-- Isomorphic steps of two flags give gauge equivalent step tensors in any coordinates. -/
private theorem isGaugeRelated_stepTensor_of_linearEquiv
    (s : CompositionSeries (Submodule (WordAlgebra d) M))
    (s' : CompositionSeries (Submodule (WordAlgebra d) M')) (k : Fin s.length)
    (k' : Fin s'.length) {n n' : ℕ}
    (ψ : Submodule.subquot (s k.castSucc) (s k.succ) ≃ₗ[ℂ] (Fin n → ℂ))
    (ψ' : Submodule.subquot (s' k'.castSucc) (s' k'.succ) ≃ₗ[ℂ] (Fin n' → ℂ))
    (ε : Submodule.subquot (s k.castSucc) (s k.succ) ≃ₗ[WordAlgebra d]
      Submodule.subquot (s' k'.castSucc) (s' k'.succ)) :
    IsGaugeRelated (stepTensor s k ψ) (stepTensor s' k' ψ') := by
  obtain ⟨a⟩ := nonempty_linearEquiv_wordModule_stepTensor s k ψ
  obtain ⟨b⟩ := nonempty_linearEquiv_wordModule_stepTensor s' k' ψ'
  exact isGaugeRelated_of_linearEquiv ((a.symm.trans ε).trans b)

/-- **Matched nonzero steps give equal traces** ((iii)⇒(i)). -/
private theorem traceWord_eq_of_equiv_nonzeroStep [FiniteDimensional ℂ M]
    [FiniteDimensional ℂ M'] (s : CompositionSeries (Submodule (WordAlgebra d) M))
    (s' : CompositionSeries (Submodule (WordAlgebra d) M')) (h0 : s.head = ⊥) (h1 : s.last = ⊤)
    (h0' : s'.head = ⊥) (h1' : s'.last = ⊤) (e : NonzeroStep s ≃ NonzeroStep s')
    (he : ∀ k, Nonempty (Submodule.subquot (s k.1.castSucc) (s k.1.succ) ≃ₗ[WordAlgebra d]
        Submodule.subquot (s' (e k).1.castSucc) (s' (e k).1.succ)))
    {w : List (Fin d)} (hw : w ≠ []) : traceWord M w = traceWord M' w := by
  classical
  rw [traceWord_eq_sum_nonzeroStep s h0 h1 hw, traceWord_eq_sum_nonzeroStep s' h0' h1' hw]
  exact Fintype.sum_equiv e _ _ fun k => traceWord_congr (he k).some w

end Flag

/-- Same states give matched nonzero steps, for the word modules of two tensors. -/
private theorem forall_exists_equiv_nonzeroStep_of_sameMPV₂Pos {B : MPSTensor d DB}
    {B' : MPSTensor d DB'} (h : SameMPV₂Pos B B') :
    ∀ (s : CompositionSeries (Submodule (WordAlgebra d) B.WordModule))
      (s' : CompositionSeries (Submodule (WordAlgebra d) B'.WordModule)),
      s.head = ⊥ → s.last = ⊤ → s'.head = ⊥ → s'.last = ⊤ →
      ∃ e : {k : Fin s.length // ∃ (i : Fin d) (x : Submodule.subquot (s k.castSucc)
            (s k.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0} ≃
          {k : Fin s'.length // ∃ (i : Fin d) (x : Submodule.subquot (s' k.castSucc)
            (s' k.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0},
        ∀ k, Nonempty (Submodule.subquot (s k.1.castSucc) (s k.1.succ) ≃ₗ[WordAlgebra d]
          Submodule.subquot (s' (e k).1.castSucc) (s' (e k).1.succ)) := by
  intro s s' h0 h1 h0' h1'
  have htr : ∀ w : List (Fin d), w ≠ [] → traceWord B.WordModule w = traceWord B'.WordModule w :=
    fun w hw => by
      rw [traceWord_wordModule, traceWord_wordModule]
      exact h.trace_evalWord w hw
  exact exists_equiv_nonzeroStep_of_traceWord_eq s s' h0 h1 h0' h1' htr

/-- Matched nonzero steps give the same states, for the word modules of two tensors. -/
private theorem sameMPV₂Pos_of_exists_equiv_nonzeroStep {B : MPSTensor d DB}
    {B' : MPSTensor d DB'}
    (h : ∃ (s : CompositionSeries (Submodule (WordAlgebra d) B.WordModule))
      (s' : CompositionSeries (Submodule (WordAlgebra d) B'.WordModule)),
      s.head = ⊥ ∧ s.last = ⊤ ∧ s'.head = ⊥ ∧ s'.last = ⊤ ∧
      ∃ e : {k : Fin s.length // ∃ (i : Fin d) (x : Submodule.subquot (s k.castSucc)
            (s k.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0} ≃
          {k : Fin s'.length // ∃ (i : Fin d) (x : Submodule.subquot (s' k.castSucc)
            (s' k.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0},
        ∀ k, Nonempty (Submodule.subquot (s k.1.castSucc) (s k.1.succ) ≃ₗ[WordAlgebra d]
          Submodule.subquot (s' (e k).1.castSucc) (s' (e k).1.succ))) :
    SameMPV₂Pos B B' := by
  obtain ⟨s, s', h0, h1, h0', h1', e, he⟩ := h
  refine sameMPV₂Pos_iff_forall_trace_evalWord_eq.2 fun w hw => ?_
  rw [← traceWord_wordModule, ← traceWord_wordModule]
  exact traceWord_eq_of_equiv_nonzeroStep s s' h0 h1 h0' h1' e he hw

/-- **Every invariant flag**. For tensors `B`, `B'`
the following are equivalent: (i) they have the same states; (ii) for every invariant flag of `B`
and every invariant flag of `B'` there is a bijection between their nonzero steps under which
paired steps are isomorphic modules; (iii) the same for some pair of invariant flags. A step is
nonzero when some letter acts on it as a nonzero map. -/
theorem tfae_sameMPV₂Pos_compositionSeries {B : MPSTensor d DB} {B' : MPSTensor d DB'} :
    List.TFAE
      [SameMPV₂Pos B B',
        ∀ (s : CompositionSeries (Submodule (WordAlgebra d) B.WordModule))
          (s' : CompositionSeries (Submodule (WordAlgebra d) B'.WordModule)),
          s.head = ⊥ → s.last = ⊤ → s'.head = ⊥ → s'.last = ⊤ →
          ∃ e : {k : Fin s.length // ∃ (i : Fin d) (x : Submodule.subquot (s k.castSucc)
                (s k.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0} ≃
              {k : Fin s'.length // ∃ (i : Fin d) (x : Submodule.subquot (s' k.castSucc)
                (s' k.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0},
            ∀ k, Nonempty (Submodule.subquot (s k.1.castSucc) (s k.1.succ) ≃ₗ[WordAlgebra d]
              Submodule.subquot (s' (e k).1.castSucc) (s' (e k).1.succ)),
        ∃ (s : CompositionSeries (Submodule (WordAlgebra d) B.WordModule))
          (s' : CompositionSeries (Submodule (WordAlgebra d) B'.WordModule)),
          s.head = ⊥ ∧ s.last = ⊤ ∧ s'.head = ⊥ ∧ s'.last = ⊤ ∧
          ∃ e : {k : Fin s.length // ∃ (i : Fin d) (x : Submodule.subquot (s k.castSucc)
                (s k.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0} ≃
              {k : Fin s'.length // ∃ (i : Fin d) (x : Submodule.subquot (s' k.castSucc)
                (s' k.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0},
            ∀ k, Nonempty (Submodule.subquot (s k.1.castSucc) (s k.1.succ) ≃ₗ[WordAlgebra d]
              Submodule.subquot (s' (e k).1.castSucc) (s' (e k).1.succ))] := by
  tfae_have 1 → 2 := forall_exists_equiv_nonzeroStep_of_sameMPV₂Pos
  tfae_have 2 → 3 := fun h =>
    (exists_compositionSeries_wordModule B).elim fun s hs =>
      (exists_compositionSeries_wordModule B').elim fun s' hs' =>
        ⟨s, s', hs.1, hs.2, hs'.1, hs'.2, h s s' hs.1 hs.2 hs'.1 hs'.2⟩
  tfae_have 3 → 1 := sameMPV₂Pos_of_exists_equiv_nonzeroStep
  tfae_finish

/-- **Matched steps have gauge equivalent tensors**. If `B` and `B'` have the same states, then for
every invariant flag `s` of `B` and every invariant flag `s'` of `B'` there is a bijection `e`
between their nonzero steps such that, in any coordinates `ψ` of a nonzero step `k` of `s` and `ψ'`
of the step `e k` of `s'`, the tensors of the two steps are gauge equivalent. -/
theorem SameMPV₂Pos.exists_equiv_isGaugeRelated_stepTensor {B : MPSTensor d DB}
    {B' : MPSTensor d DB'} (h : SameMPV₂Pos B B')
    (s : CompositionSeries (Submodule (WordAlgebra d) B.WordModule))
    (s' : CompositionSeries (Submodule (WordAlgebra d) B'.WordModule))
    (hs₀ : s.head = ⊥) (hs₁ : s.last = ⊤) (hs'₀ : s'.head = ⊥) (hs'₁ : s'.last = ⊤) :
    ∃ e : {k : Fin s.length // ∃ (i : Fin d) (x : Submodule.subquot (s k.castSucc)
          (s k.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0} ≃
        {k : Fin s'.length // ∃ (i : Fin d) (x : Submodule.subquot (s' k.castSucc)
          (s' k.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0},
      ∀ k {n n' : ℕ} (ψ : Submodule.subquot (s k.1.castSucc) (s k.1.succ) ≃ₗ[ℂ] (Fin n → ℂ))
        (ψ' : Submodule.subquot (s' (e k).1.castSucc) (s' (e k).1.succ) ≃ₗ[ℂ] (Fin n' → ℂ)),
        IsGaugeRelated (stepTensor s k.1 ψ) (stepTensor s' (e k).1 ψ') := by
  exact (forall_exists_equiv_nonzeroStep_of_sameMPV₂Pos h s s' hs₀ hs₁ hs'₀ hs'₁).elim fun e he =>
    ⟨e, fun k n n' ψ ψ' => isGaugeRelated_stepTensor_of_linearEquiv s s' k.1 (e k).1 ψ ψ'
      (he k).some⟩

/-- **Every invariant flag is the flag of a reduction**. For an invariant
flag `s` of `B`, with `S` the set of its nonzero steps, there are tensors `C k`, `k ∈ S`, and a
multi-block reduction `Q` of `B` onto `(C k)_{k ∈ S}` such that: `S` consists exactly of the
nonzero steps; the flag of `Q` is `s` (in particular `Q` has `s.length` blocks, its zero blocks
sitting at the zero steps of `s`); and the block `k ∈ S` sits at the position of the step `k`.
By `MultiBlockCompression.stepEquiv`, the step `k` is then isomorphic to the word module of `C k`,
so `C k` is the step `k` written in a basis. -/
theorem exists_multiBlockCompression_mem_iff_and_flag_eq_and_ord_eq {B : MPSTensor d DB}
    (s : CompositionSeries (Submodule (WordAlgebra d) B.WordModule)) (h0 : s.head = ⊥)
    (h1 : s.last = ⊤) :
    ∃ (S : Finset (Fin s.length)) (D : Fin s.length → ℕ) (C : ∀ k, MPSTensor d (D k))
      (Q : MultiBlockCompression B S C) (hr : s.length = S.card + Q.z),
      (∀ k, k ∈ S ↔ ∃ (i : Fin d) (x : Submodule.subquot (s k.castSucc) (s k.succ)),
          (ofWord [i] : WordAlgebra d) • x ≠ 0) ∧
        (∀ k : Fin (s.length + 1), Q.flag (Fin.cast (congrArg (· + 1) hr) k) = s k) ∧
          ∀ (k : Fin s.length) (hk : k ∈ S), Q.ord (Sum.inl ⟨k, hk⟩) = Fin.cast hr k := by
  classical
  let p : Fin s.length → Prop := fun k => ∃ (i : Fin d)
    (x : Submodule.subquot (s k.castSucc) (s k.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0
  let S : Finset (Fin s.length) := Finset.univ.filter p
  have hS : ∀ k, k ∈ S ↔ p k := fun k => by simp [S]
  let D : Fin s.length → ℕ := fun k =>
    Module.finrank ℂ (Submodule.subquot (s k.castSucc) (s k.succ))
  let C : ∀ k, MPSTensor d (D k) := fun k => stepTensor s k (Module.finBasis ℂ _).equivFun
  let z := Fintype.card {k // k ∉ S}
  let lab : Fin s.length ≃ ({k // k ∈ S} ⊕ Fin z) :=
    (Equiv.sumCompl (· ∈ S)).symm.trans (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin _))
  have hpos : ∀ k (hk : k ∈ S), lab k = Sum.inl ⟨k, hk⟩ := fun k hk => by
    simp [lab, Equiv.sumCompl_symm_apply_of_pos hk]
  have hneg : ∀ k (hk : k ∉ S), lab k = Sum.inr (Fintype.equivFin _ ⟨k, hk⟩) := fun k hk => by
    simp [lab, Equiv.sumCompl_symm_apply_of_neg hk]
  have hzero : ∀ (k : Fin s.length) (t : Fin z), lab k = Sum.inr t → ∀ (i : Fin d)
      (x : Submodule.subquot (s k.castSucc) (s k.succ)), (ofWord [i] : WordAlgebra d) • x = 0 := by
    intro k t hk i x
    by_cases hkS : k ∈ S
    · rw [hpos k hkS] at hk
      exact absurd hk Sum.inl_ne_inr
    · have := (hS k).not.1 hkS
      simp only [p, not_exists, not_not] at this
      exact this i x
  let F : FlagData B.WordModule S C :=
    { r := s.length
      z := z
      H := s.toFun
      H_zero := h0
      H_last := h1
      H_mono := s.strictMono.monotone
      label := lab
      label_bijective := lab.bijective
      matched := fun k t hk => by
        by_cases hkS : k ∈ S
        · rw [hpos k hkS] at hk
          obtain rfl := Sum.inl_injective hk
          exact nonempty_linearEquiv_wordModule_stepTensor s k _
        · rw [hneg k hkS] at hk
          exact absurd hk Sum.inr_ne_inl
      unmatched_finrank := fun k t hk =>
        finrank_subquot_eq_one_of_forall_smul_eq_zero s k (hzero k t hk)
      unmatched_smul := hzero }
  refine ⟨S, D, C, F.toMultiBlockCompression, F.r_eq, hS, fun k => F.toMultiBlockCompression_flag k,
    fun k hk => ?_⟩
  change finCongr F.r_eq (F.labelEquiv.symm (Sum.inl ⟨k, hk⟩)) = Fin.cast F.r_eq k
  rw [show F.labelEquiv.symm (Sum.inl ⟨k, hk⟩) = k from
    F.labelEquiv.symm_apply_eq.2 (hpos k hk).symm]
  rfl

/-! ### The common block diagonal limit -/

/-- Conjugation by an invertible matrix commutes with word evaluation. -/
private theorem evalWord_conj {n : ℕ} (A : Fin d → Matrix (Fin n) (Fin n) ℂ)
    {G : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G) (w : List (Fin d)) :
    Kraus.evalWord (fun i => G * A i * G⁻¹) w = G * Kraus.evalWord A w * G⁻¹ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det G).1 hG
  induction w with
  | nil => simp [Kraus.evalWord, Matrix.mul_nonsing_inv _ hdet]
  | cons i w ih =>
    simp only [Kraus.evalWord, ih]
    calc G * A i * G⁻¹ * (G * Kraus.evalWord A w * G⁻¹)
        = G * A i * (G⁻¹ * G) * Kraus.evalWord A w * G⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = G * (A i * Kraus.evalWord A w) * G⁻¹ := by
          rw [Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one, Matrix.mul_assoc G]

/-- Word evaluation is continuous in the letters: letterwise limits give limits of words. -/
private theorem tendsto_evalWord {n : ℕ} {F : ℝ → Fin d → Matrix (Fin n) (Fin n) ℂ}
    {L : Fin d → Matrix (Fin n) (Fin n) ℂ} {l : Filter ℝ}
    (h : ∀ i, Tendsto (fun t => F t i) l (𝓝 (L i)))
    (w : List (Fin d)) :
    Tendsto (fun t => Kraus.evalWord (F t) w) l (𝓝 (Kraus.evalWord L w)) := by
  induction w with
  | nil => simpa [Kraus.evalWord] using tendsto_const_nhds
  | cons i w ih => simpa [Kraus.evalWord] using (h i).mul ih

/-- **Traces survive a limit of conjugates**: if `G(t) A^i G(t)⁻¹ → L^i` as `t → 0⁺`
with `G(t)` invertible for `t > 0`, then `tr L^w = tr A^w` for every word. -/
private theorem trace_evalWord_eq_of_tendsto_conj {n : ℕ} (A L : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (G : ℝ → Matrix (Fin n) (Fin n) ℂ) (hG : ∀ t : ℝ, 0 < t → IsUnit (G t))
    (h : ∀ i, Tendsto (fun t => G t * A i * (G t)⁻¹) (𝓝[>] 0) (𝓝 (L i))) (w : List (Fin d)) :
    Matrix.trace (Kraus.evalWord L w) = Matrix.trace (Kraus.evalWord A w) := by
  have hw := (continuous_id.matrix_trace.tendsto _).comp (tendsto_evalWord h w)
  refine tendsto_nhds_unique hw (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Function.comp_apply, id]
  rw [evalWord_conj A (hG t ht) w, Matrix.trace_mul_cycle,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hG t ht)), Matrix.one_mul]

/-- Zero padding commutes with nonempty words. -/
private theorem evalWord_zeroPad {n : ℕ} (B : MPSTensor d DB) (hn : DB ≤ n) {w : List (Fin d)}
    (hw : w ≠ []) :
    Kraus.evalWord (fun i => Matrix.zeroPad n (B i)) w = Matrix.zeroPad n (Kraus.evalWord B w) := by
  induction w with
  | nil => exact absurd rfl hw
  | cons i w ih =>
    rcases eq_or_ne w [] with rfl | hw'
    · simp [Kraus.evalWord]
    · rw [Kraus.evalWord, ih hw', Kraus.evalWord, Matrix.zeroPad_mul _ _ hn]

/-- Zero padding preserves the trace of a square matrix. -/
private theorem trace_zeroPad {n : ℕ} (X : Matrix (Fin DB) (Fin DB) ℂ) (hn : DB ≤ n) :
    Matrix.trace (Matrix.zeroPad n X) = Matrix.trace X := by
  simp only [Matrix.trace, Matrix.diag]
  rw [Fin.sum_castLE_extend_zero (fun j => X j j) hn]
  refine Finset.sum_congr rfl fun α _ => ?_
  by_cases hα : α.val < DB <;> simp [Matrix.zeroPad, hα]

/-- **Scaling a block upper triangular matrix**: with `Δ(t)` the diagonal matrix with
entry `t^{-κ(k)}` on the block `k`, conjugation `Δ(t) N Δ(t)⁻¹` multiplies the entry of the blocks
`(k, l)` by `t^{κ(l) - κ(k)}`; for a block upper triangular `N` and an injective order `κ` it tends
to the block diagonal part of `N` as `t → 0⁺`. -/
private theorem tendsto_diagonal_mul_mul_diagonal {K : Type*} [Fintype K] [DecidableEq K]
    {sz : K → ℕ} (κ : K → ℕ) (hκ : Function.Injective κ)
    (N : Matrix (Σ k, Fin (sz k)) (Σ k, Fin (sz k)) ℂ)
    (hN : ∀ x y : Σ k, Fin (sz k), κ y.1 < κ x.1 → N x y = 0) :
    Tendsto (fun t : ℝ => Matrix.diagonal (fun x : Σ k, Fin (sz k) => ((t : ℂ)⁻¹) ^ κ x.1) * N *
        Matrix.diagonal (fun x : Σ k, Fin (sz k) => (t : ℂ) ^ κ x.1)) (𝓝[>] 0)
      (𝓝 (Matrix.blockDiagonal' N.blockDiag')) := by
  refine tendsto_pi_nhds.2 fun x => tendsto_pi_nhds.2 fun y => ?_
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases lt_trichotomy (κ x.1) (κ y.1) with hlt | heq | hgt
  · have hne : x.1 ≠ y.1 := fun h => hlt.ne (congrArg κ h)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
    have hlim : Tendsto (fun t : ℝ => (t : ℂ) ^ (k + 1) * N x y) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous fun t : ℝ => (t : ℂ) ^ (k + 1) * N x y :=
        (Complex.continuous_ofReal.pow _).mul continuous_const
      simpa using tendsto_nhdsWithin_of_tendsto_nhds (hc.tendsto 0)
    have hx : x = ⟨x.1, x.2⟩ := rfl
    have hy : y = ⟨y.1, y.2⟩ := rfl
    rw [hx, hy, Matrix.blockDiagonal'_apply_ne _ _ _ hne]
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ht)
    rw [hk, pow_add, inv_pow]
    field_simp
    ring
  · have hxy : x.1 = y.1 := hκ heq
    obtain ⟨k, i⟩ := x
    obtain ⟨k', j⟩ := y
    simp only at hxy
    subst hxy
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiag'_apply]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ht)
    rw [inv_pow]
    field_simp
  · have hne : x.1 ≠ y.1 := fun h => hgt.ne' (congrArg κ h)
    have hx : x = ⟨x.1, x.2⟩ := rfl
    have hy : y = ⟨y.1, y.2⟩ := rfl
    rw [hN x y hgt, hx, hy, Matrix.blockDiagonal'_apply_ne _ _ _ hne]
    simp

/-- Zero padding of a square matrix is the block matrix `[[X, 0], [0, 0]]` in coordinates
`Fin n ≃ Fin D ⊕ Fin (n - D)`. -/
private theorem zeroPad_eq_submatrix_fromBlocks {n m : ℕ} (X : Matrix (Fin DB) (Fin DB) ℂ)
    (h : n = DB + m) :
    Matrix.zeroPad n X = (Matrix.fromBlocks X 0 0 (0 : Matrix (Fin m) (Fin m) ℂ)).submatrix
      ((finCongr h).trans finSumFinEquiv.symm) ((finCongr h).trans finSumFinEquiv.symm) := by
  have key : ∀ a b, Matrix.zeroPad n X (((finCongr h).trans finSumFinEquiv.symm).symm a)
      (((finCongr h).trans finSumFinEquiv.symm).symm b) =
      Matrix.fromBlocks X 0 0 (0 : Matrix (Fin m) (Fin m) ℂ) a b := by
    rintro (j | u) (j' | u')
    · rw [Matrix.zeroPad_apply_of_lt X (by simp) (by simp)]
      simp
    · rw [Matrix.zeroPad_apply_eq_zero X (by simp)]
      simp
    · rw [Matrix.zeroPad_apply_eq_zero X (by simp)]
      simp
    · rw [Matrix.zeroPad_apply_eq_zero X (by simp)]
      simp
  ext α β
  rw [Matrix.submatrix_apply, ← key, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The number of coordinates of the block space. -/
theorem card_blockSpace {ι : Type*} {D : ι → ℕ} (S : Finset ι) (z : ℕ) :
    Fintype.card (BlockSpace D S z) = ∑ s ∈ S, D s + z := by
  rw [Fintype.card_sigma, Fintype.sum_sum_type]
  simp only [slotSize, Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_one]
  rw [Finset.sum_coe_sort S D]

/-- Two coordinates of zero blocks agree when the zero blocks do. -/
private theorem blockSpace_inr_eq {ι : Type*} {D : ι → ℕ} {S : Finset ι} {z : ℕ} {t t' : Fin z}
    (h : t = t') (j : Fin (slotSize D (Sum.inr t : BlockIndex S z)))
    (j' : Fin (slotSize D (Sum.inr t' : BlockIndex S z))) :
    (⟨Sum.inr t, j⟩ : BlockSpace D S z) = ⟨Sum.inr t', j'⟩ := by
  subst h
  exact congrArg (Sigma.mk (Sum.inr t)) (Subsingleton.elim (α := Fin 1) j j')

/-- The inclusion of the block space with `z` zero blocks into the one with `z'` zero blocks. -/
private def blockSpaceCastLE {ι : Type*} {D : ι → ℕ} {S : Finset ι} {z z' : ℕ} (h : z ≤ z') :
    BlockSpace D S z → BlockSpace D S z'
  | ⟨Sum.inl s, j⟩ => ⟨Sum.inl s, j⟩
  | ⟨Sum.inr t, j⟩ => ⟨Sum.inr (Fin.castLE h t), j⟩

/-- **One tensor of the common limit**: a reduction of `B` onto `(C_s)` gives conjugations of the
zero padding of `B` to any bond dimension `n ≥ D_B` converging to the block diagonal tensor of the
blocks, read in any order `e` of the coordinates. -/
private theorem MultiBlockCompression.exists_isUnit_and_tendsto_aux {ι : Type*} [DecidableEq ι]
    {D : ι → ℕ} {S : Finset ι} {C : ∀ s, MPSTensor d (D s)} {B : MPSTensor d DB}
    (P : MultiBlockCompression B S C) {n : ℕ} (hn : DB ≤ n)
    (e : BlockSpace D S (n - ∑ s ∈ S, D s) ≃ Fin n) :
    ∃ G : ℝ → Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, 0 < t → IsUnit (G t)) ∧
      ∀ i : Fin d,
        Tendsto (fun t => G t * Matrix.zeroPad n (B i) * (G t)⁻¹) (𝓝[>] 0)
          (𝓝 (Matrix.reindex e e (Matrix.blockDiagonal' (blockOf D C i)))) := by
  classical
  simp only [Matrix.reindex_apply]
  have hdim := P.dim_eq
  obtain ⟨m, hnm⟩ : ∃ m, n = DB + m := ⟨n - DB, by omega⟩
  generalize hzb : n - ∑ s ∈ S, D s = zb at e ⊢
  have hz : P.z + m = zb := by omega
  have hzle : P.z ≤ zb := by omega
  -- the block coordinates with the padding blocks added
  let ι₁ : BlockSpace D S P.z → BlockSpace D S zb := blockSpaceCastLE hzle
  let ι₂ : Fin m → BlockSpace D S zb := fun u => ⟨Sum.inr ⟨P.z + u, by omega⟩, 0⟩
  have hsurj : Function.Surjective (Sum.elim ι₁ ι₂) := by
    rintro ⟨s | ⟨t, ht⟩, j⟩
    · exact ⟨Sum.inl ⟨Sum.inl s, j⟩, rfl⟩
    · by_cases htz : t < P.z
      · exact ⟨Sum.inl ⟨Sum.inr ⟨t, htz⟩, j⟩, rfl⟩
      · refine ⟨Sum.inr ⟨t - P.z, by omega⟩, ?_⟩
        exact blockSpace_inr_eq (Fin.ext (by simp; omega)) _ _
  have hcard : Fintype.card (BlockSpace D S P.z ⊕ Fin m) = Fintype.card (BlockSpace D S zb) := by
    rw [Fintype.card_sum, card_blockSpace, card_blockSpace, Fintype.card_fin]
    omega
  let ψ' : BlockSpace D S P.z ⊕ Fin m ≃ BlockSpace D S zb :=
    Equiv.ofBijective _ ((Fintype.bijective_iff_surjective_and_card _).2 ⟨hsurj, hcard⟩)
  have hψ₁ : ∀ p, ψ' (Sum.inl p) = ι₁ p := fun _ => rfl
  have hψ₂ : ∀ u, ψ' (Sum.inr u) = ι₂ u := fun _ => rfl
  -- the gauge and its inverse, padded
  let gb : Matrix (BlockSpace D S zb) (Fin n) ℂ :=
    (Matrix.fromBlocks (gaugeMatrix P.gauge) 0 0 (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix ψ'.symm
      ((finCongr hnm).trans finSumFinEquiv.symm)
  let gb' : Matrix (Fin n) (BlockSpace D S zb) ℂ :=
    (Matrix.fromBlocks (gaugeMatrixInv P.gauge) 0 0 (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix
      ((finCongr hnm).trans finSumFinEquiv.symm) ψ'.symm
  have hgg : gb * gb' = 1 := by
    simp only [gb, gb', Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
      gaugeMatrix_mul_gaugeMatrixInv, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, Matrix.mul_one, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  -- the conjugated padded letters
  let N : Fin d → Matrix (BlockSpace D S zb) (BlockSpace D S zb) ℂ := fun i =>
    (Matrix.fromBlocks (conjMatrix P.gauge (B i)) 0 0
      (0 : Matrix (Fin m) (Fin m) ℂ)).submatrix ψ'.symm ψ'.symm
  have hN : ∀ i, gb * Matrix.zeroPad n (B i) * gb' = N i := by
    intro i
    rw [zeroPad_eq_submatrix_fromBlocks (B i) hnm]
    simp only [gb, gb', N, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, conjMatrix_eq_gaugeMatrix_mul]
  have hNapp : ∀ i a b, N i (ψ' a) (ψ' b) = Matrix.fromBlocks (conjMatrix P.gauge (B i)) 0 0
      (0 : Matrix (Fin m) (Fin m) ℂ) a b := by
    intro i a b
    simp only [N, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  -- the order of the blocks: the slots of `P` in its order, the padding blocks last
  let κ : BlockIndex S zb → ℕ := Sum.elim (fun s => (P.ord (Sum.inl s) : ℕ))
    (fun t => if h : (t : ℕ) < P.z then (P.ord (Sum.inr ⟨t, h⟩) : ℕ) else S.card + t)
  have hκ₁ : ∀ p : BlockSpace D S P.z, κ (ι₁ p).1 = P.ord p.1 := by
    rintro ⟨s | ⟨t, ht⟩, j⟩
    · rfl
    · simp [κ, ι₁, blockSpaceCastLE, ht]
  have hκ : Function.Injective κ := by
    have hlt : ∀ b : BlockIndex S P.z, (P.ord b : ℕ) < S.card + P.z := fun b => (P.ord b).2
    rintro (s | ⟨t, ht⟩) (s' | ⟨t', ht'⟩) h
    · exact congrArg Sum.inl (Sum.inl_injective (P.ord.injective (Fin.ext h)))
    · simp only [κ, Sum.elim_inl, Sum.elim_inr] at h
      by_cases h' : t' < P.z
      · simp only [h', ↓reduceDIte] at h
        exact absurd (P.ord.injective (Fin.ext h)) Sum.inl_ne_inr
      · simp only [h', ↓reduceDIte] at h
        have := hlt (Sum.inl s); omega
    · simp only [κ, Sum.elim_inl, Sum.elim_inr] at h
      by_cases h' : t < P.z
      · simp only [h', ↓reduceDIte] at h
        exact absurd (P.ord.injective (Fin.ext h)) Sum.inr_ne_inl
      · simp only [h', ↓reduceDIte] at h
        have := hlt (Sum.inl s'); omega
    · simp only [κ, Sum.elim_inr] at h
      by_cases h₁ : t < P.z <;> by_cases h₂ : t' < P.z
      · simp only [h₁, h₂, ↓reduceDIte] at h
        have := P.ord.injective (Fin.ext h)
        simp only [Sum.inr.injEq, Fin.mk.injEq] at this
        exact congrArg Sum.inr (Fin.ext this)
      · simp only [h₁, h₂, ↓reduceDIte] at h
        have := hlt (Sum.inr ⟨t, h₁⟩); omega
      · simp only [h₁, h₂, ↓reduceDIte] at h
        have := hlt (Sum.inr ⟨t', h₂⟩); omega
      · simp only [h₁, h₂, ↓reduceDIte] at h
        exact congrArg Sum.inr (Fin.ext (by simp only; omega))
  have htri : ∀ i (x y : BlockSpace D S zb), κ y.1 < κ x.1 → N i x y = 0 := by
    intro i x y hxy
    obtain ⟨a, rfl⟩ := ψ'.surjective x
    obtain ⟨b, rfl⟩ := ψ'.surjective y
    rw [hNapp]
    rcases a with p | u <;> rcases b with q | v
    · rw [hψ₁, hψ₁, hκ₁, hκ₁] at hxy
      rw [Matrix.fromBlocks_apply₁₁]
      exact P.triangular i (Fin.lt_def.2 hxy)
    · simp
    · simp
    · simp
  have hdiag : ∀ i, (N i).blockDiag' = blockOf D C i := by
    intro i
    funext b j j'
    rw [Matrix.blockDiag'_apply]
    rcases b with s | ⟨t, ht⟩
    · change N i (ψ' (Sum.inl ⟨Sum.inl s, j⟩)) (ψ' (Sum.inl ⟨Sum.inl s, j'⟩)) = _
      rw [hNapp, Matrix.fromBlocks_apply₁₁]
      exact congrFun (congrFun (P.matched i s) j) j'
    · by_cases htz : t < P.z
      · change N i (ψ' (Sum.inl ⟨Sum.inr ⟨t, htz⟩, j⟩)) (ψ' (Sum.inl ⟨Sum.inr ⟨t, htz⟩, j'⟩)) = _
        rw [hNapp, Matrix.fromBlocks_apply₁₁]
        exact congrFun (congrFun (P.unmatched i ⟨t, htz⟩) j) j'
      · have hpad : ∀ j₀ : Fin (slotSize D (Sum.inr ⟨t, ht⟩ : BlockIndex S zb)),
            (⟨Sum.inr ⟨t, ht⟩, j₀⟩ : BlockSpace D S zb) = ψ' (Sum.inr ⟨t - P.z, by omega⟩) := by
          intro j₀
          exact blockSpace_inr_eq (Fin.ext (by simp; omega)) _ _
        rw [hpad j, hpad j', hNapp, Matrix.fromBlocks_apply₂₂]
        rfl
  -- the scaled gauges
  let Δ : ℝ → Matrix (BlockSpace D S zb) (BlockSpace D S zb) ℂ := fun t =>
    Matrix.diagonal fun x => ((t : ℂ)⁻¹) ^ κ x.1
  let Δ' : ℝ → Matrix (BlockSpace D S zb) (BlockSpace D S zb) ℂ := fun t =>
    Matrix.diagonal fun x => (t : ℂ) ^ κ x.1
  have hΔ : ∀ t : ℝ, 0 < t → Δ t * Δ' t = 1 := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ht)
    simp only [Δ, Δ', Matrix.diagonal_mul_diagonal, ← mul_pow, inv_mul_cancel₀ ht0, one_pow]
    exact Matrix.diagonal_one
  have hsub : ∀ (X : Matrix (BlockSpace D S zb) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ)
      (Z : Matrix (Fin n) (BlockSpace D S zb) ℂ),
      X.submatrix e.symm id * Y * Z.submatrix id e.symm = (X * Y * Z).submatrix e.symm e.symm := by
    intro X Y Z
    conv_lhs => rw [← Matrix.submatrix_id_id Y]
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
  let G : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => (Δ t * gb).submatrix e.symm id
  let G' : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => (gb' * Δ' t).submatrix id e.symm
  have hGG : ∀ t : ℝ, 0 < t → G t * G' t = 1 := by
    intro t ht
    have := hsub (Δ t * gb) 1 (gb' * Δ' t)
    simp only [Matrix.mul_one] at this
    simp only [G, G']
    rw [this, Matrix.mul_assoc, ← Matrix.mul_assoc gb, hgg, Matrix.one_mul,
      hΔ t ht, Matrix.submatrix_one_equiv]
  have hinv : ∀ t : ℝ, 0 < t → (G t)⁻¹ = G' t := fun t ht => Matrix.inv_eq_right_inv (hGG t ht)
  refine ⟨G, fun t ht => ?_, fun i => ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (hGG t ht))
  · have hlim := ((continuous_id.matrix_submatrix e.symm e.symm).tendsto _).comp
      (tendsto_diagonal_mul_mul_diagonal κ hκ (N i) (htri i))
    rw [hdiag i] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Function.comp_apply, id]
    rw [hinv t ht]
    simp only [G, G', Δ, Δ']
    rw [hsub, ← hN i]
    simp only [Matrix.mul_assoc]

/-- **Common block diagonal limit**. Let
`n = max D_B D_{B'}` and pad `B`, `B'` by zero blocks to bond dimension `n`. If `B` and `B'` have
reductions onto one family `(C_s)_{s ∈ S}`, then for every order `e` of the coordinates of the
blocks of `⨁_s C_s ⊕ 0` (with `n - ∑_s D_s` zero blocks), and `L` the block diagonal tensor read in
that order, there are matrices `G(t)`, `G'(t)`, invertible for `t > 0`, such that
`G(t) B̂^i G(t)⁻¹ → L^i` and `G'(t) B̂'^i G'(t)⁻¹ → L^i` as `t → 0⁺`, for every letter `i`. -/
theorem MultiBlockCompression.exists_isUnit_and_tendsto_mul_zeroPad_mul_inv {ι : Type*}
    [DecidableEq ι] {D : ι → ℕ} {S : Finset ι} {C : ∀ s, MPSTensor d (D s)} {B : MPSTensor d DB}
    {B' : MPSTensor d DB'} (P : MultiBlockCompression B S C)
    (Q : MultiBlockCompression B' S C)
    (e : BlockSpace D S (max DB DB' - ∑ s ∈ S, D s) ≃ Fin (max DB DB')) :
    ∃ G G' : ℝ → Matrix (Fin (max DB DB')) (Fin (max DB DB')) ℂ,
      (∀ t : ℝ, 0 < t → IsUnit (G t)) ∧ (∀ t : ℝ, 0 < t → IsUnit (G' t)) ∧
        ∀ i : Fin d,
          Tendsto (fun t => G t * Matrix.zeroPad (max DB DB') (B i) * (G t)⁻¹) (𝓝[>] 0)
              (𝓝 (Matrix.reindex e e (Matrix.blockDiagonal' (blockOf D C i)))) ∧
            Tendsto (fun t => G' t * Matrix.zeroPad (max DB DB') (B' i) * (G' t)⁻¹) (𝓝[>] 0)
              (𝓝 (Matrix.reindex e e (Matrix.blockDiagonal' (blockOf D C i)))) := by
  obtain ⟨G, hG, hGt⟩ := P.exists_isUnit_and_tendsto_aux (le_max_left DB DB') e
  obtain ⟨G', hG', hG't⟩ := Q.exists_isUnit_and_tendsto_aux (le_max_right DB DB') e
  exact ⟨G, G', hG, hG', fun i => ⟨hGt i, hG't i⟩⟩

/-- **A common limit gives the same states**. With
`n = max D_B D_{B'}` and `B̂`, `B̂'` the zero paddings to bond dimension `n`, if
`G(t) B̂^i G(t)⁻¹ → L^i` and `G'(t) B̂'^i G'(t)⁻¹ → L^i` as `t → 0⁺` for some tensor `L` and
matrices `G(t)`, `G'(t)` invertible for `t > 0`, then `B` and `B'` have the same states. -/
theorem sameMPV₂Pos_of_tendsto_mul_zeroPad_mul_inv {B : MPSTensor d DB} {B' : MPSTensor d DB'}
    (L : MPSTensor d (max DB DB')) (G G' : ℝ → Matrix (Fin (max DB DB')) (Fin (max DB DB')) ℂ)
    (hG : ∀ t : ℝ, 0 < t → IsUnit (G t)) (hG' : ∀ t : ℝ, 0 < t → IsUnit (G' t))
    (h : ∀ i : Fin d,
      Tendsto (fun t => G t * Matrix.zeroPad (max DB DB') (B i) * (G t)⁻¹) (𝓝[>] 0) (𝓝 (L i)))
    (h' : ∀ i : Fin d,
      Tendsto (fun t => G' t * Matrix.zeroPad (max DB DB') (B' i) * (G' t)⁻¹) (𝓝[>] 0)
        (𝓝 (L i))) :
    SameMPV₂Pos B B' := by
  refine sameMPV₂Pos_iff_forall_trace_evalWord_eq.2 fun w hw => ?_
  have hB := trace_evalWord_eq_of_tendsto_conj _ L G hG h w
  have hB' := trace_evalWord_eq_of_tendsto_conj _ L G' hG' h' w
  rw [evalWord_zeroPad B (le_max_left DB DB') hw, trace_zeroPad _ (le_max_left DB DB')] at hB
  rw [evalWord_zeroPad B' (le_max_right DB DB') hw, trace_zeroPad _ (le_max_right DB DB')] at hB'
  rw [← hB, hB']

end MPSTensor
