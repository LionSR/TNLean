/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Noetherian.Basic
import TNLean.Algebra.TraceInvariantSubmodule
import TNLean.MPS.FundamentalTheorem.Reduction.FlagData
import TNLean.MPS.FundamentalTheorem.Reduction.Identification

/-!
# The composition-series flag of the asymmetric compression theorem

Let `M` be a finite-dimensional module over the word algebra whose word traces are the sums of
the word traces of a finite family of normal blocks `C s`, `s ∈ S`, of positive bond dimension
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, hypothesis
eq:p5-main-hypothesis through eq:p5-main-word-traces). Then `M` carries a labelled invariant flag
`MPSTensor.FlagData`: a composition series whose factors are the blocks, each exactly once, and
one-dimensional zero modules. This is the module-theoretic core of Theorem 7.7, clauses (i)–(iii)
and (vii), obtained here by induction on the dimension: a maximal invariant subspace has a simple
quotient, which is either a zero module or, by the identification theorem, one of the blocks.

## Main results

* `WordAlgebra.traceWord_congr`, `WordAlgebra.traceWord_eq_add_quotient`: word traces are
  invariant under isomorphism and additive over an invariant submodule.
* `MPSTensor.finset_eq_empty_of_forall_sum_trace_evalWord_eq_zero`: a family of normal blocks
  whose word traces sum to zero is empty.
* `MPSTensor.exists_flagData`: the flag theorem.
* `MPSTensor.isEmpty_linearEquiv_wordModule_of_mpv_ne`,
  `MPSTensor.pairwise_isEmpty_linearEquiv_of_linearIndependent`: distinct, or linearly
  independent, periodic vectors give non-isomorphic word modules.
-/

universe u

namespace WordAlgebra

variable {d : ℕ}

section Congr

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
  [IsScalarTower ℂ (WordAlgebra d) M] [AddCommGroup N] [Module ℂ N] [Module (WordAlgebra d) N]
  [IsScalarTower ℂ (WordAlgebra d) N]

/-- Word traces are invariant under isomorphism of word-algebra modules. -/
lemma traceWord_congr (e : M ≃ₗ[WordAlgebra d] N) (w : List (Fin d)) :
    traceWord M w = traceWord N w := by
  have : actAlgHom N (ofWord w) = (e.restrictScalars ℂ).conj (actAlgHom M (ofWord w)) := by
    ext n
    simp [LinearEquiv.conj_apply, map_smul]
  rw [traceWord_def, traceWord_def, this, LinearMap.trace_conj']

/-- Word traces of a product module add. -/
lemma traceWord_prod [FiniteDimensional ℂ M] [FiniteDimensional ℂ N] (w : List (Fin d)) :
    traceWord (M × N) w = traceWord M w + traceWord N w := by
  have : actAlgHom (M × N) (ofWord w) =
      (actAlgHom M (ofWord w)).prodMap (actAlgHom N (ofWord w)) := by
    ext m <;> simp
  rw [traceWord_def, this, LinearMap.trace_prodMap', traceWord_def, traceWord_def]

end Congr

section Quotient

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
  [IsScalarTower ℂ (WordAlgebra d) M] [FiniteDimensional ℂ M]

/-- Word traces are additive over an invariant submodule: the trace on `M` is the trace on `K`
plus the trace on `M ⧸ K`. -/
lemma traceWord_eq_add_quotient (K : Submodule (WordAlgebra d) M) (w : List (Fin d)) :
    traceWord M w = traceWord K w + traceWord (M ⧸ K) w := by
  have hf : ∀ x ∈ K.restrictScalars ℂ, actAlgHom M (ofWord w) x ∈ K.restrictScalars ℂ :=
    fun x hx => K.smul_mem _ hx
  rw [traceWord_def, LinearMap.trace_eq_trace_restrict_add_trace_quotient (K.restrictScalars ℂ)
    (actAlgHom M (ofWord w)) hf, traceWord_def, traceWord_def]
  congr 1

end Quotient

end WordAlgebra

namespace MPSTensor

open WordAlgebra

variable {d D : ℕ} {ι : Type*}

/-- On a normal tensor of positive bond dimension some generator acts nontrivially. -/
lemma exists_ofWord_smul_ne_zero_of_isNormal (B : MPSTensor d D) (hB : Kraus.IsNormal B)
    (hD : 0 < D) : ∃ (i : Fin d) (v : B.WordModule), (ofWord [i] : WordAlgebra d) • v ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  obtain ⟨L, hL, hspan⟩ := hB
  have hB0 : ∀ i, B i = 0 := by
    intro i
    rw [← Matrix.toLin'.map_eq_zero_iff]
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, LinearMap.zero_apply]
    have := congrArg B.wordRep.asModuleEquiv (h i (B.wordRep.asModuleEquiv.symm x))
    rw [asModuleEquiv_ofWord_smul, map_zero, LinearEquiv.apply_symm_apply] at this
    simpa [Kraus.evalWord] using this
  have hgen : ∀ σ : Fin L → Fin d, Kraus.evalWord B (List.ofFn σ) = 0 := by
    intro σ
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [List.ofFn_succ, Kraus.evalWord, hB0, zero_mul]
  have hbot : Kraus.wordSpan B L = ⊥ := by
    rw [Kraus.wordSpan, Submodule.span_eq_bot]
    rintro _ ⟨σ, rfl⟩
    exact hgen σ
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  exact (bot_ne_top (α := Submodule ℂ (Matrix (Fin D) (Fin D) ℂ))) (hbot.symm.trans hspan)

/-- A module carrying the word traces of a finite family of blocks: a product of their word
modules. -/
lemma exists_module_traceWord_eq_sum (S : Finset ι) {D : ι → ℕ} (C : ∀ s, MPSTensor d (D s)) :
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module ℂ N) (_ : Module (WordAlgebra d) N)
      (_ : IsScalarTower ℂ (WordAlgebra d) N) (_ : FiniteDimensional ℂ N),
      (∀ w : List (Fin d), traceWord N w = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w)) ∧
      ∀ p : WordAlgebra d, (∀ n : N, p • n = 0) → ∀ s ∈ S, ∀ v : (C s).WordModule, p • v = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨MPSTensor.WordModule (0 : MPSTensor d 0), inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, fun w => ?_, fun p _ s hs => (Finset.notMem_empty s hs).elim⟩
    rw [traceWord_wordModule, Finset.sum_empty]
    exact Matrix.trace_eq_zero_of_isEmpty _
  | insert t S ht ih =>
    obtain ⟨N, _, _, _, _, _, hN, hN0⟩ := ih
    refine ⟨(C t).WordModule × N, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, fun w => ?_, fun p hp s hs v => ?_⟩
    · rw [traceWord_prod, hN, traceWord_wordModule, Finset.sum_insert ht]
    · rcases Finset.mem_insert.1 hs with rfl | hs
      · have := congrArg Prod.fst (hp (v, 0))
        simpa using this
      · refine hN0 p (fun n => ?_) s hs v
        have := congrArg Prod.snd (hp (0, n))
        simpa using this

/-- A family of normal blocks of positive bond dimension whose word traces sum to zero on every
nonempty word is empty: otherwise a positive element acting as the identity on one block would
act nilpotently on the product of the blocks (base case of the flag theorem). -/
lemma finset_eq_empty_of_forall_sum_trace_evalWord_eq_zero (S : Finset ι) {D : ι → ℕ}
    (C : ∀ s, MPSTensor d (D s)) (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (h : ∀ w : List (Fin d), w ≠ [] → ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w) = 0) :
    S = ∅ := by
  by_contra hS
  obtain ⟨s₀, hs₀⟩ := Finset.nonempty_iff_ne_empty.2 hS
  obtain ⟨N, _, _, _, _, _, hN, hN0⟩ := exists_module_traceWord_eq_sum S C
  have : IsSimpleModule (WordAlgebra d) (C s₀).WordModule :=
    isSimpleModule_wordModule_of_isNormal (C s₀) (hC s₀ hs₀) (hD s₀ hs₀)
  obtain ⟨u, hu, hu'⟩ := exists_aug_eq_zero_smul_eq_self (C s₀).WordModule
    (exists_ofWord_smul_ne_zero_of_isNormal (C s₀) (hC s₀ hs₀) (hD s₀ hs₀))
  have hzero : ∀ k : ℕ, 0 < k → LinearMap.trace ℂ N ((actAlgHom N u) ^ k) = 0 := by
    intro k hk
    have hχ : ∀ w : List (Fin d), w ≠ [] → traceWord N w = (0 : WordAlgebra d →ₗ[ℂ] ℂ) (ofWord w) :=
      fun w hw => by rw [hN, h w hw, LinearMap.zero_apply]
    rw [← map_pow, ← traceChar_apply, traceChar_eq_of_traceWord_eq hχ (aug_pow hu hk),
      LinearMap.zero_apply]
  obtain ⟨n, hn⟩ := LinearMap.isNilpotent_of_forall_trace_pow_eq_zero (actAlgHom N u) hzero
  have hpow : ∀ x : N, (u ^ n) • x = 0 := by
    intro x
    have := LinearMap.congr_fun hn x
    simpa [← map_pow] using this
  have hpowQ : ∀ (k : ℕ) (v : (C s₀).WordModule), (u ^ k) • v = v := by
    intro k v
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_smul, hu', ih]
  have : Nonempty (Fin (D s₀)) := ⟨⟨0, hD s₀ hs₀⟩⟩
  have : Nontrivial (Fin (D s₀) → ℂ) := inferInstance
  have : Nontrivial (C s₀).WordModule := (C s₀).wordRep.asModuleEquiv.toEquiv.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : (C s₀).WordModule)
  exact hv ((hpowQ n v).symm.trans (hN0 (u ^ n) hpow s₀ hs₀ v))

/-- The flag theorem: a finite-dimensional module whose word traces are the sums of the word
traces of a family of normal blocks of positive bond dimension carries a labelled invariant flag
whose factors are the blocks, each once, and one-dimensional zero modules (Theorem 7.7 (i)–(iii),
(vii) of the P5 note, at the level of the word-algebra module). -/
theorem exists_flagData {S : Finset ι} {D : ι → ℕ} (C : ∀ s, MPSTensor d (D s))
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (M : Type u) [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
    [IsScalarTower ℂ (WordAlgebra d) M] [FiniteDimensional ℂ M]
    (htr : ∀ w : List (Fin d), w ≠ [] →
      traceWord M w = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w)) :
    Nonempty (FlagData M S C) := by
  suffices key : ∀ n : ℕ, ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
      [IsScalarTower ℂ (WordAlgebra d) M] [FiniteDimensional ℂ M] (S : Finset ι),
      Module.finrank ℂ M = n → (∀ s ∈ S, Kraus.IsNormal (C s)) → (∀ s ∈ S, 0 < D s) →
      (∀ w : List (Fin d), w ≠ [] →
        traceWord M w = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w)) →
      Nonempty (FlagData M S C) from key _ M S rfl hC hD htr
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ S hn hC hD htr
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · -- trivial module: no slots
    have : Subsingleton M := Module.finrank_zero_iff.1 hn
    have hS : S = ∅ := by
      refine finset_eq_empty_of_forall_sum_trace_evalWord_eq_zero S C hC hD fun w hw => ?_
      rw [← htr w hw, traceWord_def, Subsingleton.elim (actAlgHom M (ofWord w)) 0, map_zero]
    subst hS
    exact ⟨FlagData.ofSubsingleton⟩
  -- nontrivial module: choose a maximal invariant subspace
  have : Nontrivial M := Module.nontrivial_of_finrank_pos (hn ▸ hpos)
  have : IsNoetherian (WordAlgebra d) M := isNoetherian_of_tower ℂ inferInstance
  have hcoat : IsCoatomic (Submodule (WordAlgebra d) M) :=
    isCoatomic_of_orderTop_gt_wellFounded wellFounded_gt
  obtain ⟨K, hK, -⟩ := (hcoat.eq_top_or_exists_le_coatom ⊥).resolve_left bot_ne_top
  have : IsSimpleModule (WordAlgebra d) (M ⧸ K) := (isSimpleModule_iff_isCoatom).2 hK
  have : FiniteDimensional ℂ K :=
    Module.Finite.of_injective (K.subtype.restrictScalars ℂ) K.subtype_injective
  have hlt : Module.finrank ℂ K < n := by
    rw [← hn,
      ← ((Submodule.restrictScalarsEquiv ℂ (WordAlgebra d) M K).restrictScalars ℂ).finrank_eq]
    exact Submodule.finrank_lt fun h => hK.1 ((Submodule.restrictScalars_eq_top_iff ℂ _ _).1 h)
  have hadd := traceWord_eq_add_quotient K
  by_cases hQ : ∃ (i : Fin d) (q : M ⧸ K), (ofWord [i] : WordAlgebra d) • q ≠ 0
  · -- the quotient is one of the blocks
    obtain ⟨s₀, hs₀, ⟨e⟩⟩ := exists_linearEquiv_wordModule_of_isSimpleModule_quotient M K hQ S C
      (fun s hs => isSimpleModule_wordModule_of_isNormal (C s) (hC s hs) (hD s hs)) htr
    have htrK : ∀ w : List (Fin d), w ≠ [] →
        traceWord K w = ∑ s ∈ S.erase s₀, Matrix.trace (Kraus.evalWord (C s) w) := by
      intro w hw
      rw [Finset.sum_erase_eq_sub hs₀, ← htr w hw, hadd w, traceWord_congr e,
        traceWord_wordModule, add_sub_cancel_right]
    obtain ⟨F⟩ := ih _ hlt K (S.erase s₀) rfl (fun s hs => hC s (Finset.mem_of_mem_erase hs))
      (fun s hs => hD s (Finset.mem_of_mem_erase hs)) htrK
    rw [← Finset.insert_erase hs₀]
    exact ⟨F.extendMatched K s₀ (Finset.notMem_erase s₀ S) e⟩
  · -- the quotient is a zero module
    simp only [not_exists, not_not] at hQ
    have hfin : Module.finrank ℂ (M ⧸ K) = 1 :=
      finrank_eq_one_of_isSimpleModule_of_forall_smul_eq_zero hQ
    have hQw : ∀ w : List (Fin d), w ≠ [] → traceWord (M ⧸ K) w = 0 := by
      intro w hw
      obtain ⟨i, w, rfl⟩ := List.exists_cons_of_ne_nil hw
      have : actAlgHom (M ⧸ K) (ofWord (i :: w)) = 0 := by
        ext q
        rw [ofWord_cons, map_mul, Module.End.mul_apply, actAlgHom_apply, actAlgHom_apply, hQ,
          LinearMap.zero_apply]
      rw [traceWord_def, this, map_zero]
    have htrK : ∀ w : List (Fin d), w ≠ [] →
        traceWord K w = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w) := by
      intro w hw
      rw [← htr w hw, hadd w, hQw w hw, add_zero]
    obtain ⟨F⟩ := ih _ hlt K S rfl hC hD htrK
    exact ⟨F.extendZero K hfin hQ⟩

section WordModuleIso

/-- Tensors with different periodic vectors at some length have non-isomorphic word modules:
isomorphic word modules have the same word traces. -/
theorem isEmpty_linearEquiv_wordModule_of_mpv_ne {D D' L : ℕ} (A : MPSTensor d D)
    (A' : MPSTensor d D') (σ : Fin L → Fin d) (h : mpv A σ ≠ mpv A' σ) :
    IsEmpty (A.WordModule ≃ₗ[WordAlgebra d] A'.WordModule) := by
  refine ⟨fun e => h ?_⟩
  have := traceWord_congr e (List.ofFn σ)
  rw [traceWord_wordModule, traceWord_wordModule] at this
  simpa only [mpv, coeff] using this

/-- Tensors with linearly independent periodic vectors at one length have pairwise
non-isomorphic word modules, the hypothesis of the multi-block integrality theorem
`MPSTensor.exists_nat_eq_of_forall_trace_evalWord_eq_sum_mul`. -/
theorem pairwise_isEmpty_linearEquiv_of_linearIndependent {κ : Type*} {D : κ → ℕ}
    (A : ∀ x, MPSTensor d (D x)) {L₀ : ℕ}
    (hli : LinearIndependent ℂ fun x => fun σ : Fin L₀ → Fin d => mpv (A x) σ) :
    Pairwise fun y y' =>
      IsEmpty ((A y).WordModule ≃ₗ[WordAlgebra d] (A y').WordModule) := by
  intro y y' hyy'
  have hv : (fun σ : Fin L₀ → Fin d => mpv (A y) σ) ≠ fun σ => mpv (A y') σ :=
    fun heq => hyy' (hli.injective heq)
  obtain ⟨σ, hσ⟩ := Function.ne_iff.1 hv
  exact isEmpty_linearEquiv_wordModule_of_mpv_ne (A y) (A y') σ hσ

end WordModuleIso

end MPSTensor
