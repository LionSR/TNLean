/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.IntegralRankOneAction
import TNLean.MPS.Symmetry.MPOSymmetry.Defs

/-!
# Matrix product operator symmetries: integrality and the representation of the fusion ring

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), Section 3,
`Papers/2203.12563/REsubmission.tex` lines 458–460 (the action of a block `a` of the algebra on a
block `x` of the state decomposes into blocks `y` with nonnegative integer multiplicities
`M_{a,x}^y`), lines 491–492 (associativity `(a × b) · x = a · (b · x)` of the action), lines
564–565 (its consequence `∑_c N_{ab}^c M_{c,x}^y = ∑_z M_{a,z}^y M_{b,x}^z` for the
multiplicities) and lines 567–568 (the periodic-boundary action
`O_a ψ_{A_x} = ∑_y M_{a,x}^y ψ_{A_y}`); for groups, line 683.

**Formalized here.** For a family of normal tensors with linearly independent periodic vectors
at one positive length whose periodic vectors are carried by the periodic operators of a matrix
product operator fusion algebra to length-independent combinations of the family, the
coefficients are nonnegative integers and satisfy the associativity relation of the source: they
form a nonnegative integer representation of the fusion ring on the block labels. The source
obtains integrality from the arbitrary-boundary action tensors; here it is derived from the
periodic-boundary action alone, through the trace characters of the word modules.

**Scope restriction (periodic boundary):** the symmetry hypothesis is the periodic-boundary
form `MPOTensor.IsMPOSymmetricFamily` of the source's invariance of the arbitrary-boundary
subspace (lines 431–434), the form evaluated at lines 567–568; documented in
`docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`.

## Main results

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

namespace MPOTensor

open MPSTensor

variable {d : ℕ} {ι κ : Type*} {χ : ι → ℕ} {D : κ → ℕ} [Fintype κ]

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
    (a : ι) (x y : κ) : ∃ m : ℕ, M a x y = m :=
  exists_nat_eq_of_forall_trace_evalWord_eq_sum_mul (actTensor (O a) (A x)) A hA hD
    (pairwise_isEmpty_linearEquiv_of_linearIndependent A hli) (M a x)
    (trace_evalWord_actTensor_of_mpo_mulVec_eq (O a) (A x) A (M a x) (hsym a x)) y

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

Source: arXiv:2203.12563, lines 564–565: associativity `(a × b) · x = a · (b · x)` of the
action (lines 491–492) gives `∑_c N_{ab}^c M_{c,x}^y = ∑_z M_{a,z}^y M_{b,x}^z`. Here it follows
from the fusion rules of the periodic operators and linear independence of the periodic block
vectors at one positive length. -/
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

Source: arXiv:2203.12563, line 460 and lines 564–565 (for groups, line 683): the action
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
