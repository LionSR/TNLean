/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PermutationMatrixUnitary
import TNLean.MPS.Preparation.CircuitComposition

/-!
# Gates permuting the computational basis

A permutation `σ` of the configurations of the chain acts on vectors by its permutation
matrix, `(P_σ v)(x) = v (σ x)`. When `σ` changes only the sites of a set `S`, by a rule that
reads only the sites of `S`, the permutation matrix is a unitary acting on `S`
(`MPSPreparation.IsLocalPerm.permMatrix_mem_supportedOperators`). A layer of such gates on
pairwise disjoint neighbouring pairs acts as a single permutation of the configurations, given
site by site by the gate of the pair containing the site
(`MPSPreparation.exists_permLayer_op_mulVec`).

These are the gates of the measurement-assisted preparation of GHZ-type states in
arXiv:2103.13367, Example 1: controlled shifts `|k⟩|a⟩ ↦ |k⟩|a ± k⟩` and single-site shifts
`X^c`, generalizing the CNOT and Pauli corrections from qubits to qudits. A product of
single-site permutation matrices acts by permuting the label of every site
(`MPSPreparation.finKronecker_permMatrix_mulVec`).

## Main definitions

* `MPSPreparation.IsLocalPerm` — a permutation of configurations changing and reading only
  the sites of a set.
* `MPSPreparation.shiftPerm` — adding a value computed from the other sites to one site.
* `MPSPreparation.permLayer` — the layer of permutation gates on disjoint pairs.

## Main results

* `MPSPreparation.IsLocalPerm.permMatrix_mem_supportedOperators`.
* `MPSPreparation.exists_permLayer_op_mulVec`, `MPSPreparation.exists_shiftLayer_op_mulVec`.
* `MPSPreparation.finKronecker_permMatrix_mulVec`.
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d N : ℕ}

/-- The permutation `σ` of the configurations changes only the sites of `S`, and the new values
at the sites of `S` depend only on the old values at the sites of `S`. -/
def IsLocalPerm (S : Set (Fin N)) (σ : Equiv.Perm (Cfg d N)) : Prop :=
  (∀ x, ∀ i ∉ S, σ x i = x i) ∧
    ∀ x y, (∀ j ∈ S, x j = y j) → ∀ i ∈ S, σ x i = σ y i

private theorem permMatrix_cfg_apply (σ : Equiv.Perm (Cfg d N)) (x y : Cfg d N) :
    σ.permMatrix ℂ x y = if σ x = y then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

/-- The permutation matrix of a permutation changing and reading only the sites of `S` acts
on `S`. -/
theorem IsLocalPerm.permMatrix_mem_supportedOperators {S : Set (Fin N)}
    {σ : Equiv.Perm (Cfg d N)} (h : IsLocalPerm S σ) :
    σ.permMatrix ℂ ∈ supportedOperators d S := by
  classical
  let e : Fin (Fintype.card S) → Fin N := fun j => ((Fintype.equivFin S).symm j : Fin N)
  have he : Function.Injective e :=
    Subtype.val_injective.comp (Fintype.equivFin S).symm.injective
  have hmem : ∀ i, i ∈ S ↔ ∃ j, e j = i := fun i => by
    constructor
    · intro hi
      exact ⟨Fintype.equivFin S ⟨i, hi⟩, by simp [e]⟩
    · rintro ⟨j, rfl⟩
      exact ((Fintype.equivFin S).symm j).prop
  have hrange : Set.range e = S := Set.ext fun i => (hmem i).symm
  let X : Matrix (Cfg d (Fintype.card S)) (Cfg d (Fintype.card S)) ℂ :=
    of fun u w => if ∃ x : Cfg d N, x ∘ e = u ∧ σ x ∘ e = w then 1 else 0
  have hX : σ.permMatrix ℂ = embedOp e X := by
    ext x y
    rw [permMatrix_cfg_apply, embedOp_apply]
    simp only [X, of_apply]
    by_cases hxy : σ x = y
    · subst hxy
      have hag : AgreeOff e x (σ x) := fun i hi =>
        (h.1 x i fun hiS => by obtain ⟨j, hj⟩ := (hmem i).mp hiS; exact hi j hj).symm
      simp only [hag, ite_true,
        show ∃ x' : Cfg d N, x' ∘ e = x ∘ e ∧ σ x' ∘ e = σ x ∘ e from ⟨x, rfl, rfl⟩]
    · simp only [hxy, ite_false]
      split_ifs with hag hex
      · exfalso
        obtain ⟨x', hx', hσ⟩ := hex
        refine hxy (funext fun i => ?_)
        by_cases hi : i ∈ S
        · obtain ⟨j, rfl⟩ := (hmem _).mp hi
          have hagree : ∀ k ∈ S, x k = x' k := fun k hk => by
            obtain ⟨j', rfl⟩ := (hmem k).mp hk
            exact (congrFun hx' j').symm
          rw [h.2 x x' hagree _ hi]
          exact congrFun hσ j
        · rw [h.1 x i hi]
          exact hag i fun j hj => hi ((hmem i).mpr ⟨j, hj⟩)
      · rfl
      · rfl
  have hmemX := embedOp_mem_supportedOperators (d := d) he X
  rw [hrange] at hmemX
  rwa [hX]

/-! ### Shifting one site -/

section Shift

variable [NeZero d]

/-- The permutation `x ↦ x + f(x) e_t` adding the value `f x` to the site `t`, where `f` does
not read the site `t`. -/
def shiftPerm (t : Fin N) (f : Cfg d N → Fin d)
    (hf : ∀ x c, f (Function.update x t c) = f x) : Equiv.Perm (Cfg d N) where
  toFun x := Function.update x t (x t + f x)
  invFun x := Function.update x t (x t - f x)
  left_inv x := by simp [hf]
  right_inv x := by simp [hf]

theorem shiftPerm_apply (t : Fin N) (f : Cfg d N → Fin d)
    (hf : ∀ x c, f (Function.update x t c) = f x) (x : Cfg d N) :
    shiftPerm t f hf x = Function.update x t (x t + f x) :=
  rfl

theorem isLocalPerm_shiftPerm {S : Set (Fin N)} {t : Fin N} (ht : t ∈ S) (f : Cfg d N → Fin d)
    (hf : ∀ x c, f (Function.update x t c) = f x)
    (hfS : ∀ x y, (∀ j ∈ S, x j = y j) → f x = f y) : IsLocalPerm S (shiftPerm t f hf) := by
  refine ⟨fun x i hi => ?_, fun x y hxy i hi => ?_⟩
  · rw [shiftPerm_apply, Function.update_of_ne (by rintro rfl; exact hi ht)]
  · simp only [shiftPerm_apply]
    by_cases hit : i = t
    · subst hit; simp [hxy i ht, hfS x y hxy]
    · rw [Function.update_of_ne hit, Function.update_of_ne hit, hxy i hi]

end Shift

/-! ### Layers of permutation gates -/

section Layer

variable [NeZero N]

/-- The layer of permutation gates `τ k` on the pairwise disjoint neighbouring pairs
`{k, k + 1}`, `k ∈ K`. -/
noncomputable def permLayer (K : Finset (Fin N)) (hK : (K : Set (Fin N)).PairwiseDisjoint bond)
    (τ : Fin N → Equiv.Perm (Cfg d N)) (hτ : ∀ k ∈ K, IsLocalPerm (bond k) (τ k)) :
    Layer d N where
  bonds := K
  gate k := (τ k).permMatrix ℂ
  gate_mem_unitary _ _ := Equiv.Perm.permMatrix_mem_unitaryGroup _
  gate_mem_supportedOperators k hk := (hτ k hk).permMatrix_mem_supportedOperators
  pairwiseDisjoint := hK

private theorem exists_partialOp_permLayer (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) (τ : Fin N → Equiv.Perm (Cfg d N))
    (hτ : ∀ k ∈ K, IsLocalPerm (bond k) (τ k)) :
    ∀ (s : Finset (Fin N)) (hs : s ⊆ K), ∃ P : Equiv.Perm (Cfg d N),
      (permLayer K hK τ hτ).partialOp s hs = P.permMatrix ℂ ∧
      (∀ x, ∀ k ∈ s, ∀ i ∈ bond k, P x i = τ k x i) ∧
      ∀ x i, (∀ k ∈ s, i ∉ bond k) → P x i = x i := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    exact ⟨1, by simp [Layer.partialOp], by simp, fun _ _ _ => rfl⟩
  | insert a s ha ih =>
    intro hs
    have hsK : s ⊆ K := (Finset.subset_insert a s).trans hs
    have haK : a ∈ K := hs (Finset.mem_insert_self a s)
    obtain ⟨P, hP, h1, h2⟩ := ih hsK
    have hdisj : ∀ k ∈ s, ∀ i ∈ bond a, i ∉ bond k := fun k hk i hia hik => by
      have hne : a ≠ k := fun h => ha (h ▸ hk)
      exact Set.disjoint_left.mp (hK haK (hsK hk) hne) hia hik
    refine ⟨P * τ a, ?_, ?_, ?_⟩
    · change (insert a s).noncommProd _ _ = _
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Matrix.permMatrix_mul]
      congr 1
    · intro x k hk i hi
      rw [Equiv.Perm.mul_apply]
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact h2 _ i fun k' hk' => hdisj k' hk' i hi
      · rw [h1 _ k hk i hi]
        refine (hτ k (hsK hk)).2 _ _ (fun j hj => ?_) i hi
        exact (hτ a haK).1 x j fun hja => hdisj k hk j hja hj
    · intro x i hi
      rw [Equiv.Perm.mul_apply, h2 _ i fun k hk => hi k (Finset.mem_insert_of_mem hk)]
      exact (hτ a haK).1 x i (hi a (Finset.mem_insert_self a s))

/-- **A layer of permutation gates is a permutation.** The layer of the gates `τ k` on the
disjoint pairs `{k, k + 1}`, `k ∈ K`, acts on vectors as `v ↦ v ∘ P`, where `P` agrees with
`τ k` on the pair `{k, k + 1}` and with the identity on the sites outside all pairs. -/
theorem exists_permLayer_op_mulVec (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) (τ : Fin N → Equiv.Perm (Cfg d N))
    (hτ : ∀ k ∈ K, IsLocalPerm (bond k) (τ k)) :
    ∃ P : Cfg d N → Cfg d N, (∀ v : Cfg d N → ℂ, (permLayer K hK τ hτ).op *ᵥ v = v ∘ P) ∧
      (∀ x, ∀ k ∈ K, ∀ i ∈ bond k, P x i = τ k x i) ∧
      ∀ x i, (∀ k ∈ K, i ∉ bond k) → P x i = x i := by
  obtain ⟨P, hP, h1, h2⟩ := exists_partialOp_permLayer K hK τ hτ K subset_rfl
  refine ⟨P, fun v => ?_, h1, h2⟩
  change (permLayer K hK τ hτ).partialOp K subset_rfl *ᵥ v = _
  rw [hP, permMatrix_mulVec]

variable [NeZero d]

/-- **A layer of shifts.** If the gate on `{k, k + 1}` adds `f k x` to the site `t k` of the
pair, the layer acts as `v ↦ v ∘ P`, where `P` adds `f k x` at each site `t k` and leaves the
other sites unchanged. -/
theorem exists_shiftLayer_op_mulVec (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) (t : Fin N → Fin N)
    (f : Fin N → Cfg d N → Fin d) (hf : ∀ k x c, f k (Function.update x (t k) c) = f k x)
    (hτ : ∀ k ∈ K, IsLocalPerm (bond k) (shiftPerm (t k) (f k) (hf k))) :
    ∃ P : Cfg d N → Cfg d N,
      (∀ v : Cfg d N → ℂ,
        (permLayer K hK (fun k => shiftPerm (t k) (f k) (hf k)) hτ).op *ᵥ v = v ∘ P) ∧
      (∀ x, ∀ k ∈ K, t k ∈ bond k → P x (t k) = x (t k) + f k x) ∧
      ∀ x i, (∀ k ∈ K, t k ≠ i) → P x i = x i := by
  obtain ⟨P, hv, h1, h2⟩ := exists_permLayer_op_mulVec K hK _ hτ
  refine ⟨P, hv, fun x k hk ht => ?_, fun x i hi => ?_⟩
  · rw [h1 x k hk _ ht, shiftPerm_apply, Function.update_self]
  · by_cases hb : ∃ k ∈ K, i ∈ bond k
    · obtain ⟨k, hk, hik⟩ := hb
      rw [h1 x k hk i hik, shiftPerm_apply, Function.update_of_ne (hi k hk).symm]
    · exact h2 x i fun k hk hik => hb ⟨k, hk, hik⟩

end Layer

/-! ### Single-site permutations -/

/-- **Single-site permutations.** The Kronecker product of the permutation matrices of
permutations `σ i` of the labels of the sites `i` acts on vectors as `v ↦ v ∘ σ`, where `σ`
applies `σ i` at every site `i`. -/
theorem finKronecker_permMatrix_mulVec (σ : Fin N → Equiv.Perm (Fin d)) (v : Cfg d N → ℂ) :
    finKronecker (fun i => (σ i).permMatrix ℂ) *ᵥ v = fun x => v fun i => σ i (x i) := by
  classical
  funext x
  have h : ∀ y : Cfg d N, finKronecker (fun i => (σ i).permMatrix ℂ) x y =
      if y = (fun i => σ i (x i)) then 1 else 0 := fun y => by
    simp only [finKronecker_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    rw [Finset.prod_boole]
    simp only [Finset.mem_univ, true_implies, funext_iff, eq_comm]
  simp only [mulVec, dotProduct, h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

end MPSPreparation
