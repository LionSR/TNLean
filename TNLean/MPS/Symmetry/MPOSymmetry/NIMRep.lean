/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Flag
import TNLean.MPS.FundamentalTheorem.Reduction.IntegralRankOneAction
import TNLean.MPS.Symmetry.MPOSymmetry.Defs

/-!
# Matrix product operator symmetries: integrality and the representation of the fusion ring

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), Section 3,
`Papers/2203.12563/REsubmission.tex` lines 458–460 (the action of a block `a` of the algebra on a
block `x` of the state decomposes into blocks `y` with nonnegative integer multiplicities
`M_{a,x}^y`) and lines 491–492 (associativity `(a × b) · x = a · (b · x)` of the action); for
groups, line 683 (`M_{gh,x}^y = ∑_z M_{g,z}^y M_{h,x}^z`).

**Formalized here.** For a family of normal tensors with linearly independent periodic vectors
at one positive length whose periodic vectors are carried by the periodic operators of a matrix
product operator fusion algebra to length-independent combinations of the family, the
coefficients are nonnegative integers and satisfy the associativity relation of the source: they
form a nonnegative integer representation of the fusion ring on the block labels. The source
obtains integrality from the arbitrary-boundary action tensors; here it is derived from the
periodic-boundary action alone, through the trace characters of the word modules.

**Scope restriction (periodic boundary):** the symmetry hypothesis is the periodic-boundary
form `MPOTensor.IsMPOSymmetricFamily` of the source's invariance of the arbitrary-boundary
subspace (lines 431–434); documented in `docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`.

## Main results

* `MPSTensor.exists_nat_eq_of_forall_trace_evalWord_eq_sum_mul`: a word-trace relation
  `tr(B^w) = ∑_y c_y tr(A_y^w)` on nonempty words against normal tensors with pairwise
  non-isomorphic word modules has nonnegative integer coefficients.
* `MPOTensor.exists_nat_eq_of_isMPOSymmetricFamily`: the action coefficients are nonnegative
  integers.
* `MPOTensor.sum_fusion_mul_eq_sum_mul_of_isMPOSymmetricFamily`: the action coefficients satisfy
  `∑_c N_{ab}^c M_{c,x}^y = ∑_z M_{b,x}^z M_{a,z}^y`.
* `MPOTensor.exists_isNIMRep_of_isMPOSymmetricFamily`: together, a nonnegative integer
  representation of the fusion ring.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
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

/-- Tensors with different periodic vectors at some length have non-isomorphic word modules:
isomorphic word modules have the same word traces. -/
theorem isEmpty_linearEquiv_wordModule_of_mpv_ne {D D' L : ℕ} (A : MPSTensor d D)
    (A' : MPSTensor d D') (σ : Fin L → Fin d) (h : mpv A σ ≠ mpv A' σ) :
    IsEmpty (A.WordModule ≃ₗ[WordAlgebra d] A'.WordModule) := by
  refine ⟨fun e => h ?_⟩
  have := traceWord_congr e (List.ofFn σ)
  rw [traceWord_wordModule, traceWord_wordModule] at this
  simpa only [mpv, coeff] using this

end MPSTensor

namespace MPOTensor

open MPSTensor

variable {d : ℕ} {ι κ : Type*} {χ : ι → ℕ} {D : κ → ℕ}

/-- Linearly independent periodic vectors have pairwise non-isomorphic word modules. -/
theorem pairwise_isEmpty_linearEquiv_of_linearIndependent (A : ∀ x, MPSTensor d (D x))
    {L₀ : ℕ} (hli : LinearIndependent ℂ fun x => fun σ : Fin L₀ → Fin d => mpv (A x) σ) :
    Pairwise fun y y' =>
      IsEmpty ((A y).WordModule ≃ₗ[WordAlgebra d] (A y').WordModule) := by
  intro y y' hyy'
  have hv : (fun σ : Fin L₀ → Fin d => mpv (A y) σ) ≠ fun σ => mpv (A y') σ :=
    fun heq => hyy' (hli.injective heq)
  obtain ⟨σ, hσ⟩ := Function.ne_iff.1 hv
  exact isEmpty_linearEquiv_wordModule_of_mpv_ne (A y) (A y') σ hσ

variable [Fintype κ]

/-- **The action multiplicities are nonnegative integers.**

Source: arXiv:2203.12563, line 460: the coefficient `M_{a,x}^y` of the block `y` in the action
of `a` on the block `x` is the multiplicity of `y` in the decomposition of the action tensor,
hence a nonnegative integer. Here it is derived from the periodic-boundary action alone: the
action tensor `T_a · A_x` has the word traces `∑_y M_{a,x}^y tr(A_y^w)`, and the blocks are
normal with linearly independent periodic vectors at one positive length, a consequence of the
source's standing assumption of injective blocks orthogonal to each other in the thermodynamic
limit (line 317; compare `MPSTensor.IsBNT.eventually_li`). -/
theorem exists_nat_eq_of_isMPOSymmetricFamily (O : ∀ a, MPOTensor d (χ a))
    (A : ∀ x, MPSTensor d (D x)) (M : ι → κ → κ → ℂ) (hsym : IsMPOSymmetricFamily O A M)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x) {L₀ : ℕ}
    (hli : LinearIndependent ℂ fun x => fun σ : Fin L₀ → Fin d => mpv (A x) σ)
    (a : ι) (x y : κ) : ∃ m : ℕ, M a x y = m := by
  classical
  refine exists_nat_eq_of_forall_trace_evalWord_eq_sum_mul (actTensor (O a) (A x)) A hA hD
    (pairwise_isEmpty_linearEquiv_of_linearIndependent A hli) (M a x) (fun w hw => ?_) y
  have hlen : 0 < w.length := List.length_pos_iff.mpr hw
  have hw' : w = List.ofFn w.get := (List.ofFn_get w).symm
  have hσ := congrFun ((mpo_mulVec_mpv (O a) (A x) w.length).symm.trans
    (hsym a x w.length hlen)) w.get
  simp only [MPSTensor.mpv, MPSTensor.coeff] at hσ
  rw [hw']
  exact hσ

/-- The symmetry condition at one length, as an identity of vectors. -/
theorem IsMPOSymmetricFamily.mulVec_eq_sum {O : ∀ a, MPOTensor d (χ a)}
    {A : ∀ x, MPSTensor d (D x)} {M : ι → κ → κ → ℂ} (hsym : IsMPOSymmetricFamily O A M)
    (a : ι) (x : κ) {L : ℕ} (hL : 0 < L) :
    mpo (O a) L *ᵥ (fun σ : Fin L → Fin d => mpv (A x) σ) =
      ∑ y, M a x y • fun σ : Fin L → Fin d => mpv (A y) σ := by
  rw [hsym a x L hL]
  funext σ
  simp [Finset.sum_apply]

variable [Fintype ι]

/-- **The action coefficients represent the fusion ring.**

Source: arXiv:2203.12563, lines 491–492 and line 683: associativity `(a × b) · x = a · (b · x)`
of the action gives `∑_c N_{ab}^c M_{c,x}^y = ∑_z M_{b,x}^z M_{a,z}^y`. Here it follows from the
fusion rules of the periodic operators and linear independence of the periodic block vectors at
one positive length. -/
theorem sum_fusion_mul_eq_sum_mul_of_isMPOSymmetricFamily {O : ∀ a, MPOTensor d (χ a)}
    {N : ι → ι → ι → ℕ} (hfus : IsMPOFusionAlgebra O N) {A : ∀ x, MPSTensor d (D x)}
    {M : ι → κ → κ → ℂ} (hsym : IsMPOSymmetricFamily O A M) {L₀ : ℕ} (hL₀ : 0 < L₀)
    (hli : LinearIndependent ℂ fun x => fun σ : Fin L₀ → Fin d => mpv (A x) σ)
    (a b : ι) (x y : κ) :
    ∑ c, (N a b c : ℂ) * M c x y = ∑ z, M b x z * M a z y := by
  have h1 : (mpo (O a) L₀ * mpo (O b) L₀) *ᵥ (fun σ : Fin L₀ → Fin d => mpv (A x) σ) =
      ∑ y, (∑ z, M b x z * M a z y) • fun σ : Fin L₀ → Fin d => mpv (A y) σ := by
    rw [← Matrix.mulVec_mulVec, hsym.mulVec_eq_sum b x hL₀, Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul, hsym.mulVec_eq_sum a _ hL₀, Finset.smul_sum, smul_smul,
      Finset.sum_smul]
    exact Finset.sum_comm
  have h2 : (mpo (O a) L₀ * mpo (O b) L₀) *ᵥ (fun σ : Fin L₀ → Fin d => mpv (A x) σ) =
      ∑ y, (∑ c, (N a b c : ℂ) * M c x y) • fun σ : Fin L₀ → Fin d => mpv (A y) σ := by
    rw [hfus a b L₀ hL₀, Matrix.sum_mulVec]
    simp_rw [Matrix.smul_mulVec, hsym.mulVec_eq_sum _ x hL₀, Finset.smul_sum, smul_smul,
      Finset.sum_smul]
    exact Finset.sum_comm
  exact Fintype.linearIndependent_iffₛ.1 hli _ _ (h2.symm.trans h1) y

/-- **Nonnegative integer representation of the fusion ring on the blocks.**

Source: arXiv:2203.12563, line 460 and lines 491–492 (for groups, line 683): the action
coefficients of a family of normal tensors with linearly independent periodic vectors at one
positive length, symmetric under a matrix product operator fusion algebra, are nonnegative
integers `M_{a,x}^y` forming a representation of the fusion ring. -/
theorem exists_isNIMRep_of_isMPOSymmetricFamily {O : ∀ a, MPOTensor d (χ a)}
    {N : ι → ι → ι → ℕ} (hfus : IsMPOFusionAlgebra O N) {A : ∀ x, MPSTensor d (D x)}
    {M : ι → κ → κ → ℂ} (hsym : IsMPOSymmetricFamily O A M)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x) {L₀ : ℕ} (hL₀ : 0 < L₀)
    (hli : LinearIndependent ℂ fun x => fun σ : Fin L₀ → Fin d => mpv (A x) σ) :
    ∃ M' : ι → κ → κ → ℕ, (∀ a x y, M a x y = M' a x y) ∧ IsNIMRep N M' := by
  choose M' hM' using exists_nat_eq_of_isMPOSymmetricFamily O A M hsym hA hD hli
  refine ⟨M', hM', fun a b x y => ?_⟩
  have h := sum_fusion_mul_eq_sum_mul_of_isMPOSymmetricFamily hfus hsym hL₀ hli a b x y
  simp only [hM'] at h
  exact_mod_cast h

end MPOTensor
