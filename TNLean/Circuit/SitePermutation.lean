/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.PermutationMatrixUnitary
import QICLean.ManyBody.Sites.PlacedConfiguration

/-!
# Permutations of configurations and of sites

A permutation `σ` of the configurations of a finite set of sites acts on vectors by its
permutation matrix, `(P_σ v)(x) = v (σ x)`. This file collects the permutations that are
notions about sites alone:

* a permutation that changes only the sites of a set `S`, by a rule that reads only the sites
  of `S`, has a permutation matrix acting on `S`
  (`QuantumCircuit.IsLocalPerm.permMatrix_mem_supportedOperators`);
* a permutation `π` of the sites induces the permutation `x ↦ x ∘ π` of the configurations
  (`QuantumCircuit.cfgPerm`);
* on the chain `Fin n`, the operator `QuantumCircuit.permOp τ` permuting the sites by `τ`, which
  is unitary.

QICLean's `ManyBody.sitePermOp π` (`QICLean.ManyBody.Sites.Relabel`) has the entries of both
`(cfgPerm π).permMatrix ℂ` and `permOp π`, with its multiplicativity, adjoint and conjugation
lemmas, and `ManyBody.sitePermOp_mul_placeAlong_mul_conjTranspose` moves placed operators.

## Main definitions

* `QuantumCircuit.IsLocalPerm` — a permutation of configurations changing and reading only
  the sites of a set.
* `QuantumCircuit.cfgPerm` — the permutation of configurations induced by a permutation of
  the sites.
* `QuantumCircuit.permOp` — the operator of a permutation of the sites of a chain.

## References

* arXiv:2103.13367 (Piroli, Styliaris, Cirac), Example 1 (controlled shifts and single-site
  shifts).
* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraph "Tree-RG circuit with
  measurements" (relabelling of sites).
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Permutations changing and reading only a set of sites -/

/-- The permutation `σ` of the configurations changes only the sites of `S`, and the new values
at the sites of `S` depend only on the old values at the sites of `S`. -/
def IsLocalPerm (S : Finset ι) (σ : Equiv.Perm (ι → Fin d)) : Prop :=
  (∀ x, ∀ i ∉ S, σ x i = x i) ∧
    ∀ x y, (∀ j ∈ S, x j = y j) → ∀ i ∈ S, σ x i = σ y i

omit [DecidableEq ι] in
private theorem permMatrix_cfg_apply (σ : Equiv.Perm (ι → Fin d)) (x y : ι → Fin d) :
    σ.permMatrix ℂ x y = if σ x = y then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

/-- The permutation matrix of a permutation changing and reading only the sites of `S` acts
on `S`. -/
theorem IsLocalPerm.permMatrix_mem_supportedOperators {S : Finset ι}
    {σ : Equiv.Perm (ι → Fin d)} (h : IsLocalPerm S σ) :
    σ.permMatrix ℂ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S := by
  have key : ∀ x y x' y' : ι → Fin d, (∀ i ∈ S, x i = x' i) → (∀ i ∈ S, y i = y' i) →
      (∀ i ∉ S, x' i = y' i) → σ x = y → σ x' = y' := fun x y x' y' hx hy h' hσ ↦
    funext fun i ↦ by
      by_cases hi : i ∈ S
      · rw [h.2 x' x (fun j hj ↦ (hx j hj).symm) i hi, hσ, hy i hi]
      · rw [h.1 x' i hi, h' i hi]
  refine ManyBody.mem_supportedOperators_iff.mpr ⟨fun x y ⟨v, hv, hne⟩ ↦ ?_,
    fun x y x' y' h₁ h₂ h₃ h₄ ↦ ?_⟩
  · rw [permMatrix_cfg_apply, ite_eq_right_iff]
    rintro rfl
    exact absurd (h.1 x v hv).symm hne
  · rw [permMatrix_cfg_apply, permMatrix_cfg_apply]
    exact if_congr ⟨key x y x' y' h₁ h₂ h₄, key x' y' x y (fun i hi ↦ (h₁ i hi).symm)
      (fun i hi ↦ (h₂ i hi).symm) h₃⟩ rfl rfl

/-! ### Permutations of configurations induced by permutations of the sites -/

section SitePermutation

/-- The permutation `x ↦ x ∘ π` of the configurations induced by a permutation `π` of the
sites. -/
def cfgPerm (π : Equiv.Perm ι) : Equiv.Perm (ι → Fin d) where
  toFun x := x ∘ π
  invFun x := x ∘ π.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

theorem permMatrix_cfgPerm_mul_permMatrix_cfgPerm (π σ : Equiv.Perm ι) :
    (cfgPerm (d := d) π).permMatrix ℂ * (cfgPerm σ).permMatrix ℂ =
      (cfgPerm (π * σ)).permMatrix ℂ := by
  rw [← Matrix.permMatrix_mul]
  congr 1

omit [DecidableEq ι] in
theorem permMatrix_cfgPerm_one : (cfgPerm (d := d) (1 : Equiv.Perm ι)).permMatrix ℂ = 1 := by
  have : cfgPerm (d := d) (1 : Equiv.Perm ι) = 1 := by ext x i; rfl
  rw [this, Matrix.permMatrix_one]

end SitePermutation

/-! ### Permutations of the sites of a chain -/

section Chain

variable {m n N : ℕ}

/-- The operator permuting the sites of the chain by `τ`: `|x⟩ ↦ |x ∘ τ⁻¹⟩`. -/
def permOp (τ : Equiv.Perm (Fin n)) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  of fun x y => if y = x ∘ τ then 1 else 0

theorem permOp_mul_mul_conjTranspose (τ : Equiv.Perm (Fin n))
    (X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    permOp τ * X * (permOp τ)ᴴ = X.submatrix (· ∘ τ) (· ∘ τ) := by
  ext x y
  simp only [mul_apply, permOp, of_apply, conjTranspose_apply, submatrix_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp [apply_ite star]

/-- Two sites `i ≠ j` as a map `Fin 2 → Fin n`. -/
def pairSites (i j : Fin n) : Fin 2 → Fin n := ![i, j]

/-- The site permutation `permOp τ` is the permutation matrix of `x ↦ x ∘ τ` on
configurations. -/
theorem permOp_eq_permMatrix (τ : Equiv.Perm (Fin n)) :
    permOp (d := d) τ = Equiv.Perm.permMatrix ℂ (τ.symm.arrowCongr (Equiv.refl (Fin d))) := by
  ext x y
  simp only [permOp, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, PEquiv.toMatrix_apply,
    Option.mem_def, Option.some.injEq, of_apply]
  exact if_congr eq_comm rfl rfl

theorem permOp_mem_unitary (τ : Equiv.Perm (Fin n)) :
    permOp (d := d) τ ∈ unitary (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) := by
  rw [permOp_eq_permMatrix]
  exact Equiv.Perm.permMatrix_mem_unitaryGroup _

/-- The adjoint chain permutation reverses the site permutation. -/
@[simp] theorem permOp_conjTranspose (π : Equiv.Perm (Fin N)) :
    (permOp (d := d) π)ᴴ = permOp π.symm := by
  ext x y
  simp only [permOp, of_apply, conjTranspose_apply, apply_ite star, star_one, star_zero]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    have := congrFun h (π.symm i)
    simpa using this.symm
  · intro h
    funext i
    have := congrFun h (π i)
    simpa using this.symm

/-- The permutation of sites `τ` acts on vectors by precomposing configurations with `τ`. -/
theorem permOp_mulVec (τ : Equiv.Perm (Fin n)) (v : (Fin n → Fin d) → ℂ) :
    permOp τ *ᵥ v = v ∘ fun x => x ∘ τ := by
  classical
  funext x
  simp [permOp, mulVec, dotProduct]

end Chain

end QuantumCircuit
