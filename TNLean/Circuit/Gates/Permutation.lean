/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.PermutationMatrixUnitary
import TNLean.Circuit.Composition
import TNLean.Circuit.SitePermutation

/-!
# Gates permuting the computational basis

A permutation `σ` of the configurations of a finite set of sites acts on vectors by its permutation
matrix, `(P_σ v)(x) = v (σ x)`. When `σ` changes only the sites of a set `S`, by a rule that
reads only the sites of `S`, the permutation matrix is a unitary acting on `S`
(`QuantumCircuit.IsLocalPerm.permMatrix_mem_supportedOperators`, in
`TNLean.Circuit.SitePermutation`). A layer of such gates on
pairwise disjoint neighbouring pairs acts as a single permutation of the configurations, given
site by site by the gate of the pair containing the site
(`QuantumCircuit.exists_permLayer_op_mulVec`).

These are the gates of the measurement-assisted preparation of GHZ-type states in
arXiv:2103.13367, Example 1: controlled shifts `|k⟩|a⟩ ↦ |k⟩|a ± k⟩` and single-site shifts
`X^c`, generalizing the CNOT and Pauli corrections from qubits to qudits. A product of
single-site permutation matrices acts by permuting the label of every site
(`Matrix.finKronecker_permMatrix_mulVec`).

## Main definitions

* `QuantumCircuit.permLayer` — the layer of permutation gates on disjoint pairs.

## Main results

* `QuantumCircuit.exists_permLayer_op_mulVec`, `QuantumCircuit.exists_shiftLayer_op_mulVec`.
* `Matrix.finKronecker_permMatrix_mulVec`.
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Layers of permutation gates -/

section Layer

variable {N : ℕ} [NeZero N]

/-- The layer of permutation gates `τ k` on the pairwise disjoint neighbouring pairs
`{k, k + 1}`, `k ∈ K`. -/
noncomputable def permLayer (K : Finset (Fin N)) (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond)
    (τ : Fin N → Equiv.Perm (Fin N → Fin d)) (hτ : ∀ k ∈ K, IsLocalPerm (ringBond k) (τ k)) :
    RingLayer d N where
  bonds := K
  gate k := (τ k).permMatrix ℂ
  gate_mem_unitary _ _ := Equiv.Perm.permMatrix_mem_unitaryGroup _
  gate_mem_supportedOperators k hk := (hτ k hk).permMatrix_mem_supportedOperators
  pairwiseDisjoint := hK

private theorem exists_partialOp_permLayer (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) (τ : Fin N → Equiv.Perm (Fin N → Fin d))
    (hτ : ∀ k ∈ K, IsLocalPerm (ringBond k) (τ k)) :
    ∀ (s : Finset (Fin N)) (hs : s ⊆ K), ∃ P : Equiv.Perm (Fin N → Fin d),
      (permLayer K hK τ hτ).partialOp s hs = P.permMatrix ℂ ∧
      (∀ x, ∀ k ∈ s, ∀ i ∈ ringBond k, P x i = τ k x i) ∧
      ∀ x i, (∀ k ∈ s, i ∉ ringBond k) → P x i = x i := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    exact ⟨1, by simp [BondLayer.partialOp], by simp, fun _ _ _ => rfl⟩
  | insert a s ha ih =>
    intro hs
    have hsK : s ⊆ K := (Finset.subset_insert a s).trans hs
    have haK : a ∈ K := hs (Finset.mem_insert_self a s)
    obtain ⟨P, hP, h1, h2⟩ := ih hsK
    have hdisj : ∀ k ∈ s, ∀ i ∈ ringBond a, i ∉ ringBond k := fun k hk i hia hik => by
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
    (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) (τ : Fin N → Equiv.Perm (Fin N → Fin d))
    (hτ : ∀ k ∈ K, IsLocalPerm (ringBond k) (τ k)) :
    ∃ P : (Fin N → Fin d) → (Fin N → Fin d),
    (∀ v : (Fin N → Fin d) → ℂ, (permLayer K hK τ hτ).op *ᵥ v = v ∘ P) ∧
      (∀ x, ∀ k ∈ K, ∀ i ∈ ringBond k, P x i = τ k x i) ∧
      ∀ x i, (∀ k ∈ K, i ∉ ringBond k) → P x i = x i := by
  obtain ⟨P, hP, h1, h2⟩ := exists_partialOp_permLayer K hK τ hτ K subset_rfl
  refine ⟨P, fun v => ?_, h1, h2⟩
  change (permLayer K hK τ hτ).partialOp K subset_rfl *ᵥ v = _
  rw [hP, permMatrix_mulVec]

variable [NeZero d]

/-- **A layer of shifts.** If the gate on `{k, k + 1}` adds `f k x` to the site `t k` of the
pair, the layer acts as `v ↦ v ∘ P`, where `P` adds `f k x` at each site `t k` and leaves the
other sites unchanged. -/
theorem exists_shiftLayer_op_mulVec (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) (t : Fin N → Fin N)
    (f : Fin N → (Fin N → Fin d) → Fin d) (hf : ∀ k x c, f k (Function.update x (t k) c) = f k x)
    (hτ : ∀ k ∈ K, IsLocalPerm (ringBond k) (shiftPerm (t k) (f k) (hf k))) :
    ∃ P : (Fin N → Fin d) → (Fin N → Fin d),
      (∀ v : (Fin N → Fin d) → ℂ,
        (permLayer K hK (fun k => shiftPerm (t k) (f k) (hf k)) hτ).op *ᵥ v = v ∘ P) ∧
      (∀ x, ∀ k ∈ K, t k ∈ ringBond k → P x (t k) = x (t k) + f k x) ∧
      ∀ x i, (∀ k ∈ K, t k ≠ i) → P x i = x i := by
  obtain ⟨P, hv, h1, h2⟩ := exists_permLayer_op_mulVec K hK _ hτ
  refine ⟨P, hv, fun x k hk ht => ?_, fun x i hi => ?_⟩
  · rw [h1 x k hk _ ht, shiftPerm_apply, Function.update_self]
  · by_cases hb : ∃ k ∈ K, i ∈ ringBond k
    · obtain ⟨k, hk, hik⟩ := hb
      rw [h1 x k hk i hik, shiftPerm_apply, Function.update_of_ne (hi k hk).symm]
    · exact h2 x i fun k hk hik => hb ⟨k, hk, hik⟩

end Layer

/-! ### Single-site permutations -/

/-- **Single-site permutations.** The Kronecker product of the permutation matrices of
permutations `σ i` of the labels of the sites `i` acts on vectors as `v ↦ v ∘ σ`, where `σ`
applies `σ i` at every site `i`. -/
theorem _root_.Matrix.finKronecker_permMatrix_mulVec {N : ℕ} (σ : Fin N → Equiv.Perm (Fin d))
    (v : (Fin N → Fin d) → ℂ) :
    finKronecker (fun i => (σ i).permMatrix ℂ) *ᵥ v = fun x => v fun i => σ i (x i) := by
  classical
  funext x
  have h : ∀ y : Fin N → Fin d, finKronecker (fun i => (σ i).permMatrix ℂ) x y =
      if y = (fun i => σ i (x i)) then 1 else 0 := fun y => by
    simp only [finKronecker_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    rw [Finset.prod_boole]
    simp only [Finset.mem_univ, true_implies, funext_iff, eq_comm]
  simp only [mulVec, dotProduct, h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

end QuantumCircuit
