/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import TNLean.Algebra.ConstantTracePowers
import TNLean.MPS.FundamentalTheorem.Reduction.Flag
import TNLean.MPS.MPDO.ActionTensor

/-!
# Rank-one actions on a normal tensor are integral

If the periodic operators of a matrix product operator tensor `T` act on the periodic vectors of
a normal tensor `A` of positive bond dimension by one length-independent scalar `c`, then `c` is
a nonnegative integer (`Notes/OpenProblemsTN/checks/asym_fibonacci_categorical_data.md`, §6.4).
This is the lattice form of the integrality of the multiplicities in the action-tensor
corollary of the multi-block asymmetric compression theorem: a block that reappears with
multiplicity `c` reappears an integral number of times.

The mechanism is the word-trace identity `tr((T · A)^w) = c · tr(A^w)` for every nonempty word
`w`, obtained from the action tensor. Normality of `A` writes a matrix unit as a combination
`∑_u x_u A^u` of words of one positive length `ℓ`, and the same combination `N = ∑_u x_u (T·A)^u`
of words of the action tensor then satisfies `tr(N^k) = c · tr((∑_u x_u A^u)^k) = c` for every
positive `k`; `Matrix.exists_nat_eq_of_forall_trace_pow_eq` concludes.

The same argument applies against several normal tensors with pairwise non-isomorphic word
modules: an element of the word algebra of augmentation zero acts as a matrix unit on one of them
and as zero on the others, and isolates one coefficient. The rank-one statement is the case of a
single tensor.

## Main results

* `MPSTensor.exists_nat_eq_of_forall_trace_evalWord_eq_sum_mul`: the word-trace form against
  several normal tensors.
* `MPSTensor.exists_nat_eq_of_forall_trace_evalWord_eq_mul`: the rank-one word-trace form.
* `MPOTensor.trace_evalWord_actTensor_of_mpo_mulVec_eq`: a length-independent periodic action
  gives the word-trace relation of the action tensor.
* `MPOTensor.exists_nat_eq_of_mpo_mulVec_mpv_eq_smul`: the periodic-operator form.
-/

open scoped Matrix

namespace MPSTensor

open WordAlgebra

variable {d : ℕ} {κ : Type*} [Fintype κ]

/-- The action of a finite combination of words on the word module of a tensor. -/
lemma asModuleEquiv_sum_smul {D ℓ : ℕ} (A : MPSTensor d D) (x : (Fin ℓ → Fin d) → ℂ)
    (v : A.WordModule) :
    A.wordRep.asModuleEquiv ((∑ σ, x σ • ofWord (List.ofFn σ)) • v) =
      (∑ σ, x σ • Kraus.evalWord A (List.ofFn σ)) *ᵥ A.wordRep.asModuleEquiv v := by
  rw [Finset.sum_smul, map_sum, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [smul_assoc, map_smul, asModuleEquiv_ofWord_smul, Matrix.smul_mulVec]

/-- **Multi-block word-trace relations against distinct normal tensors are integral.**
If every nonempty word trace of `B` is the combination `∑_y c_y tr(A_y^w)` of the word traces of
normal tensors of positive bond dimension with pairwise non-isomorphic word modules, then every
coefficient `c_y` is a nonnegative integer. -/
theorem exists_nat_eq_of_forall_trace_evalWord_eq_sum_mul {DB : ℕ} {D : κ → ℕ}
    (B : MPSTensor d DB) (A : ∀ y, MPSTensor d (D y)) (hA : ∀ y, Kraus.IsNormal (A y))
    (hD : ∀ y, 0 < D y)
    (hne : Pairwise fun y y' => IsEmpty ((A y).WordModule ≃ₗ[WordAlgebra d] (A y').WordModule))
    (c : κ → ℂ)
    (h : ∀ w : List (Fin d), w ≠ [] →
      (Kraus.evalWord B w).trace = ∑ y, c y * (Kraus.evalWord (A y) w).trace) (y₀ : κ) :
    ∃ m : ℕ, c y₀ = m := by
  classical
  have hsimple : ∀ y, IsSimpleModule (WordAlgebra d) (A y).WordModule :=
    fun y => isSimpleModule_wordModule_of_isNormal (A y) (hA y) (hD y)
  have := hsimple y₀
  obtain ⟨p, hp, hpQ, hpS⟩ := exists_aug_eq_zero_of_forall_isEmpty_linearEquiv
    (A y₀).WordModule (exists_ofWord_smul_ne_zero_of_isNormal (A y₀) (hA y₀) (hD y₀))
    (Finset.univ.erase y₀) A (fun s _ => hsimple s)
    (fun s hs => hne (Finset.ne_of_mem_erase hs).symm)
  -- a combination of words of `A y₀` equal to a matrix unit
  have : NeZero (D y₀) := ⟨(hD y₀).ne'⟩
  obtain ⟨ℓ, hℓ, hspan⟩ := hA y₀
  have hmem : Matrix.single (0 : Fin (D y₀)) 0 (1 : ℂ) ∈ Submodule.span ℂ
      (Set.range fun σ : Fin ℓ → Fin d => Kraus.evalWord (A y₀) (List.ofFn σ)) :=
    hspan.span_eq_top ▸ Submodule.mem_top
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
  set e : WordAlgebra d := ∑ σ, x σ • ofWord (List.ofFn σ) with he
  set u : WordAlgebra d := p * e with hu
  have hu0 : aug u = 0 := aug_mul_right hp e
  -- `u` kills every other block
  have hzero : ∀ y, y ≠ y₀ → actAlgHom (A y).WordModule u = 0 := by
    intro y hy
    ext v
    simp [hu, hpS y (Finset.mem_erase.2 ⟨hy, Finset.mem_univ y⟩)]
  -- `u` acts on the block `y₀` as the matrix unit `E`
  set E : Matrix (Fin (D y₀)) (Fin (D y₀)) ℂ := Matrix.single 0 0 1 with hE
  have hact : ∀ v : (A y₀).WordModule,
      (A y₀).wordRep.asModuleEquiv (u • v) = E *ᵥ (A y₀).wordRep.asModuleEquiv v := by
    intro v
    rw [hu, mul_smul, hpQ, he, asModuleEquiv_sum_smul, hx]
  have hone : actAlgHom (A y₀).WordModule u =
      (A y₀).wordRep.asModuleEquiv.symm.conj (Matrix.toLin' E) := by
    ext v
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, actAlgHom_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearEquiv.eq_symm_apply,
      hact, Matrix.toLin'_apply]
  have hff : actAlgHom (A y₀).WordModule u * actAlgHom (A y₀).WordModule u =
      actAlgHom (A y₀).WordModule u := by
    ext v
    apply (A y₀).wordRep.asModuleEquiv.injective
    rw [Module.End.mul_apply, actAlgHom_apply, actAlgHom_apply, hact, hact, Matrix.mulVec_mulVec,
      hE, Matrix.single_mul_single_same, mul_one]
  have hpowf : ∀ j : ℕ,
      actAlgHom (A y₀).WordModule u ^ (j + 1) = actAlgHom (A y₀).WordModule u := by
    intro j
    induction j with
    | zero => rw [pow_one]
    | succ j ih => rw [pow_succ, ih, hff]
  have hchar : ∀ k : ℕ, 0 < k →
      traceChar B.WordModule (u ^ k) = ∑ y, c y * traceChar (A y).WordModule (u ^ k) := by
    intro k hk
    have hχ : ∀ w : List (Fin d), w ≠ [] → traceWord B.WordModule w =
        (∑ y, c y • traceChar (A y).WordModule) (ofWord w) := by
      intro w hw
      rw [traceWord_wordModule, h w hw, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [LinearMap.smul_apply, traceChar_wordModule_ofWord, smul_eq_mul]
    rw [traceChar_eq_of_traceWord_eq hχ (aug_pow hu0 hk), LinearMap.sum_apply]
    rfl
  have hblock : ∀ k : ℕ, 0 < k → ∀ y,
      traceChar (A y).WordModule (u ^ k) = if y = y₀ then 1 else 0 := by
    intro k hk y
    rw [traceChar_apply, map_pow]
    split_ifs with hy
    · subst hy
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [hpowf, hone, LinearMap.trace_conj',
        LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin (D y))),
        LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', hE,
        Matrix.trace_single_eq_same]
    · rw [hzero y hy, zero_pow hk.ne', map_zero]
  -- constant trace powers on `B`
  let b := Module.finBasis ℂ B.WordModule
  refine Matrix.exists_nat_eq_of_forall_trace_pow_eq
    (LinearMap.toMatrix b b (actAlgHom B.WordModule u)) (c y₀) fun k hk => ?_
  rw [LinearMap.toMatrix_pow, ← LinearMap.trace_eq_matrix_trace, ← map_pow, ← traceChar_apply,
    hchar k hk]
  simp only [hblock k hk, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-- **Rank-one word-trace relations against a normal tensor are integral.** If every nonempty
word trace of `B` is `c` times the corresponding word trace of a normal tensor `A` of positive
bond dimension, then `c` is a nonnegative integer (data file §6.4). -/
theorem exists_nat_eq_of_forall_trace_evalWord_eq_mul {DB DA : ℕ} [NeZero DA]
    (B : MPSTensor d DB) (A : MPSTensor d DA) (hA : Kraus.IsNormal A) (c : ℂ)
    (h : ∀ w : List (Fin d), w ≠ [] →
      (Kraus.evalWord B w).trace = c * (Kraus.evalWord A w).trace) :
    ∃ m : ℕ, c = m :=
  exists_nat_eq_of_forall_trace_evalWord_eq_sum_mul B (fun _ : Unit => A) (fun _ => hA)
    (fun _ => Nat.pos_of_ne_zero (NeZero.ne DA)) (fun y y' hyy' => absurd (Subsingleton.elim y y')
      hyy') (fun _ => c) (fun w hw => by simpa using h w hw) ()

end MPSTensor

namespace MPOTensor

variable {d D DA : ℕ}

/-- A length-independent action of the periodic operators of `T` on the periodic vector of `A`,
`O_T ψ_A = ∑_y c_y ψ_{A'_y}` at every positive length, gives the word-trace relation
`tr((T · A)^w) = ∑_y c_y tr(A'_y^w)` of the action tensor on every nonempty word. -/
theorem trace_evalWord_actTensor_of_mpo_mulVec_eq {κ : Type*} [Fintype κ] {D' : κ → ℕ}
    (T : MPOTensor d D) (A : MPSTensor d DA) (A' : ∀ y, MPSTensor d (D' y)) (c : κ → ℂ)
    (h : ∀ N : ℕ, 0 < N →
      mpo T N *ᵥ (fun τ : Fin N → Fin d => MPSTensor.mpv A τ) =
        fun σ : Fin N → Fin d => ∑ y, c y * MPSTensor.mpv (A' y) σ)
    (w : List (Fin d)) (hw : w ≠ []) :
    (Kraus.evalWord (actTensor T A) w).trace = ∑ y, c y * (Kraus.evalWord (A' y) w).trace := by
  have hlen : 0 < w.length := List.length_pos_iff.mpr hw
  have hw' : w = List.ofFn w.get := (List.ofFn_get w).symm
  have hσ := congrFun ((mpo_mulVec_mpv T A w.length).symm.trans (h w.length hlen)) w.get
  simp only [MPSTensor.mpv, MPSTensor.coeff] at hσ
  rw [hw']
  exact hσ

/-- **Rank-one actions on a normal tensor are integral** (data file §6.4). If at every positive
length the periodic operator of `T` acts on the periodic vector of a normal tensor `A` of positive
bond dimension as multiplication by one scalar `c`, then `c` is a nonnegative integer. -/
theorem exists_nat_eq_of_mpo_mulVec_mpv_eq_smul [NeZero DA] (T : MPOTensor d D)
    (A : MPSTensor d DA) (hA : Kraus.IsNormal A) (c : ℂ)
    (h : ∀ N : ℕ, 0 < N →
      mpo T N *ᵥ (fun τ : Fin N → Fin d => MPSTensor.mpv A τ) =
        c • fun σ : Fin N → Fin d => MPSTensor.mpv A σ) :
    ∃ m : ℕ, c = m := by
  refine MPSTensor.exists_nat_eq_of_forall_trace_evalWord_eq_mul (actTensor T A) A hA c
    fun w hw => ?_
  simpa using trace_evalWord_actTensor_of_mpo_mulVec_eq T A (fun _ : Unit => A) (fun _ => c)
    (fun N hN => by rw [h N hN]; funext σ; simp) w hw

end MPOTensor
