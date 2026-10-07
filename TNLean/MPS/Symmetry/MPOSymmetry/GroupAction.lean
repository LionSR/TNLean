/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Group.Action.End
import TNLean.MPS.Symmetry.MPOSymmetry.Character

/-!
# The group action determined by a nonnegative integer representation

For the group fusion rule `N_{g,h}^k = δ_{k,gh}`, a nonnegative integer representation whose
unit is the identity determines a unique action of the group on the block labels. The
permutations supplied by the invertible-label theorem satisfy both the identity law and the
multiplication law. They therefore give Mathlib's `MulAction`, rather than just an unrelated
permutation for each group element.

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563v3),
`Papers/2203.12563/REsubmission.tex`, line 683: the multiplicity matrices form a representation
of the group, and each is a permutation matrix. The periodic-vector consequence is the action
`O_g ψ_{A_x} = ψ_{A_{g • x}}` of lines 1062–1064.

**Scope restriction (periodic boundary):** the tensor-family theorem uses the periodic-boundary
symmetry hypothesis, as in `Character.lean`; see
`docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`. The algebraic construction from a
nonnegative integer representation has no boundary restriction.

## Main results

* `MPOTensor.IsNIMRep.groupPerm`: the permutation determined by a group label.
* `MPOTensor.IsNIMRep.groupPerm_mul`: these permutations obey the group multiplication law.
* `MPOTensor.IsNIMRep.toMulAction`: the resulting Mathlib action on the block labels.
* `MPOTensor.IsNIMRep.toMulAction_spec`: its multiplicity coefficients are `δ_{y,g • x}`.
* `MPOTensor.IsNIMRep.existsUnique_mulAction`: the coefficients uniquely determine the action.
* `MPOTensor.exists_mulAction_mpo_mulVec_eq_of_isMPOSymmetricFamily`: one coherent group action
  permutes the periodic vectors at every positive length.
-/

open scoped Matrix

namespace MPOTensor

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq G] [DecidableEq X]
  {M : G → X → X → ℕ}

namespace IsNIMRep

variable (hM : IsNIMRep (fun g h k : G ↦ if k = g * h then 1 else 0) M)
  (he : ∀ x y, M 1 x y = if y = x then 1 else 0)

include hM in
omit [DecidableEq X] in
/-- The group form of the nonnegative integer representation identity.

Source: arXiv:2203.12563, line 683: `M_{gh,x}^y = ∑_z M_{h,x}^z M_{g,z}^y`. -/
theorem group_mul_apply (g h : G) (x y : X) :
    M (g * h) x y = ∑ z, M h x z * M g z y := by
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    using hM g h x y

/-- The permutation determined by a group label in a unital nonnegative integer
representation. Its choice is unique by `groupPerm_eq_of_coefficients`.

Source: arXiv:2203.12563, line 683. -/
noncomputable def groupPerm (g : G) : Equiv.Perm X :=
  Classical.choose (hM.exists_equiv_of_isInvertibleLabel he
    (GroupFamily.isInvertibleLabel_groupFusion g))

/-- The multiplicity matrix of a group label is the permutation matrix of its action.

Source: arXiv:2203.12563, line 683. -/
theorem groupPerm_spec (g : G) (x y : X) :
    M g x y = if y = hM.groupPerm he g x then 1 else 0 :=
  Classical.choose_spec (hM.exists_equiv_of_isInvertibleLabel he
    (GroupFamily.isInvertibleLabel_groupFusion g)) x y

/-- A block is the image under the selected permutation exactly when its multiplicity is one.

Source: arXiv:2203.12563, line 683. -/
theorem groupPerm_apply_eq_iff (g : G) (x y : X) :
    hM.groupPerm he g x = y ↔ M g x y = 1 := by
  rw [hM.groupPerm_spec he]
  simp [eq_comm]

/-- The identity group element fixes every block.

Source: arXiv:2203.12563, line 683, the hypothesis `M_e = 1`. -/
@[simp] theorem groupPerm_one : hM.groupPerm he 1 = 1 := by
  ext x
  apply (hM.groupPerm_apply_eq_iff he 1 x x).2
  simp [he]

/-- The permutations determined by the multiplicity matrices compose in group order.

Source: arXiv:2203.12563, line 683. The convention
`M_{gh,x}^y = ∑_z M_{h,x}^z M_{g,z}^y` gives the left action `g • (h • x)`. -/
@[simp] theorem groupPerm_mul (g h : G) :
    hM.groupPerm he (g * h) = hM.groupPerm he g * hM.groupPerm he h := by
  ext x
  apply (hM.groupPerm_apply_eq_iff he (g * h) x
    (hM.groupPerm he g (hM.groupPerm he h x))).2
  rw [hM.group_mul_apply]
  simp [hM.groupPerm_spec he]

/-- The permutation representation determined by a unital nonnegative integer representation
of a group fusion ring.

Source: arXiv:2203.12563, line 683. -/
noncomputable def groupPermHom : G →* Equiv.Perm X where
  toFun := hM.groupPerm he
  map_one' := hM.groupPerm_one he
  map_mul' := hM.groupPerm_mul he

/-- The canonical group action determined by a unital nonnegative integer representation of a
group fusion ring. No action on the block labels is assumed.

Source: arXiv:2203.12563, line 683. -/
noncomputable abbrev toMulAction : MulAction G X :=
  MulAction.compHom X (hM.groupPermHom he)

/-- The multiplicities of the constructed action are exactly its permutation coefficients.

Source: arXiv:2203.12563, line 683. -/
theorem toMulAction_spec :
    letI := hM.toMulAction he
    ∀ g x y, M g x y = if y = g • x then 1 else 0 :=
  hM.groupPerm_spec he

/-- The coefficient formula uniquely determines the map of blocks for each group element.
In particular the constructed action does not depend on the choice of permutation witnesses.

Source: arXiv:2203.12563, line 683, uniqueness of the block with nonzero multiplicity. -/
theorem groupPerm_eq_of_coefficients (g : G) (f : X → X)
    (hf : ∀ x y, M g x y = if y = f x then 1 else 0) :
    ⇑(hM.groupPerm he g) = f := by
  funext x
  apply (hM.groupPerm_apply_eq_iff he g x (f x)).2
  simp [hf]

/-- Any group action with the prescribed multiplicities is the constructed action.

Source: arXiv:2203.12563, line 683, uniqueness of each image block. -/
theorem toMulAction_unique (μ : MulAction G X)
    (hμ : letI := μ; ∀ g x y, M g x y = if y = g • x then 1 else 0) :
    hM.toMulAction he = μ := by
  let := μ
  apply MulAction.ext
  funext g x
  exact congrFun (hM.groupPerm_eq_of_coefficients he g (g • ·) (hμ g)) x

include hM he in
/-- A unital nonnegative integer representation of a group fusion ring determines exactly one
group action on the block labels.

Source: arXiv:2203.12563, line 683. -/
theorem existsUnique_mulAction :
    ∃! μ : MulAction G X, letI := μ
      ∀ g x y, M g x y = if y = g • x then 1 else 0 := by
  refine ⟨hM.toMulAction he, hM.toMulAction_spec he, ?_⟩
  intro μ hμ
  exact (hM.toMulAction_unique he μ hμ).symm

end IsNIMRep

/-! ### Coherent action on a symmetric family of periodic vectors -/

open MPSTensor

/-- **A group of matrix product operators acts coherently on its symmetric normal blocks.**

Source: arXiv:2203.12563, line 683 and lines 1062–1064. A symmetric family of normal blocks
with linearly independent periodic vectors at one positive length, on which the identity group
element acts trivially, carries a single group action satisfying
`M_{g,x}^y = δ_{y,g • x}` and `O_g ψ_{A_x} = ψ_{A_{g • x}}` at every positive length.
The group action, including its identity and composition laws, is derived from the symmetry
coefficients. The source's injective, asymptotically orthogonal blocks (line 317) imply the
normality and linear independence hypotheses used here.

**Scope restriction (periodic boundary):** this uses the periodic symmetry condition of lines
567–568; see `docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`. -/
theorem exists_mulAction_mpo_mulVec_eq_of_isMPOSymmetricFamily
    {d : ℕ} {χ : G → ℕ} {D : X → ℕ} {O : ∀ g, MPOTensor d (χ g)}
    (hfus : IsMPOFusionAlgebra O fun g h k ↦ if k = g * h then 1 else 0)
    {A : ∀ x, MPSTensor d (D x)} {C : G → X → X → ℂ}
    (hsym : IsMPOSymmetricFamily O A C) (hA : ∀ x, Kraus.IsNormal (A x))
    (hD : ∀ x, 0 < D x) {L₀ : ℕ} (hL₀ : 0 < L₀)
    (hli : LinearIndependent ℂ fun x ↦ fun σ : Fin L₀ → Fin d ↦ mpv (A x) σ)
    (hunit : ∀ x, ∀ L : ℕ, 0 < L →
      mpo (O 1) L *ᵥ (fun τ : Fin L → Fin d ↦ mpv (A x) τ) =
        fun σ : Fin L → Fin d ↦ mpv (A x) σ) :
    ∃ μ : MulAction G X, letI := μ
      (∀ g x y, C g x y = if y = g • x then 1 else 0) ∧
      ∀ g x, ∀ L : ℕ, 0 < L →
        mpo (O g) L *ᵥ (fun τ : Fin L → Fin d ↦ mpv (A x) τ) =
          fun σ : Fin L → Fin d ↦ mpv (A (g • x)) σ := by
  obtain ⟨M, hCM, hM⟩ := exists_isNIMRep_of_isMPOSymmetricFamily hfus hsym hA hD hL₀ hli
  have he : ∀ x y, M 1 x y = if y = x then 1 else 0 := by
    intro x y
    have hcoeff := Fintype.linearIndependent_iffₛ.1 hli (C 1 x)
      (fun z ↦ if z = x then (1 : ℂ) else 0)
      (by rw [← hsym.mulVec_eq_sum 1 x hL₀]; simpa using hunit x L₀ hL₀) y
    rw [hCM] at hcoeff
    split_ifs at hcoeff ⊢ <;> exact_mod_cast hcoeff
  let := hM.toMulAction he
  have hcoeff : ∀ g x y, C g x y = if y = g • x then 1 else 0 := by
    intro g x y
    rw [hCM, hM.toMulAction_spec he]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  refine ⟨hM.toMulAction he, hcoeff, fun g x L hL ↦ ?_⟩
  rw [hsym g x L hL]
  funext σ
  simp [hcoeff]

end MPOTensor
