/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.PermutationMatrixUnitary
import TNLean.Circuit.SiteEmbedding

/-!
# Permutations of configurations and of sites

A permutation `σ` of the configurations of a finite set of sites acts on vectors by its
permutation matrix, `(P_σ v)(x) = v (σ x)`. This file collects the permutations that are
notions about sites alone:

* a permutation that changes only the sites of a set `S`, by a rule that reads only the sites
  of `S`, has a permutation matrix acting on `S`
  (`QuantumCircuit.IsLocalPerm.permMatrix_mem_supportedOperators`); adding to one site a value
  computed from the other sites is of this kind (`QuantumCircuit.shiftPerm`);
* a permutation `π` of the sites induces the permutation `x ↦ x ∘ π` of the configurations
  (`QuantumCircuit.cfgPerm`), whose matrix moves product operators and embedded operators to
  the permuted sites;
* on the chain `Fin n`, the operator `QuantumCircuit.permOp τ` permuting the sites by `τ`, which
  is multiplicative in `τ`, unitary, and equal to an embedded two-site SWAP when `τ` is a
  transposition.

## Main definitions

* `QuantumCircuit.IsLocalPerm` — a permutation of configurations changing and reading only
  the sites of a set.
* `QuantumCircuit.shiftPerm` — adding a value computed from the other sites to one site.
* `QuantumCircuit.cfgPerm` — the permutation of configurations induced by a permutation of
  the sites.
* `QuantumCircuit.permOp`, `QuantumCircuit.permOpHom` — the operator of a permutation of the
  sites of a chain.

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
at the sites of `S` depend only on the old values at the sites of `S`.
The site type and `S` need not be finite. -/
def IsLocalPerm (S : Set ι) (σ : Equiv.Perm (ι → Fin d)) : Prop :=
  (∀ x, ∀ i ∉ S, σ x i = x i) ∧
    ∀ x y, (∀ j ∈ S, x j = y j) → ∀ i ∈ S, σ x i = σ y i

omit [DecidableEq ι] in
private theorem permMatrix_cfg_apply (σ : Equiv.Perm (ι → Fin d)) (x y : ι → Fin d) :
    σ.permMatrix ℂ x y = if σ x = y then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

/-- The permutation matrix of a permutation changing and reading only the sites of `S` acts
on `S`. -/
theorem IsLocalPerm.permMatrix_mem_supportedOperators {S : Finset ι}
    {σ : Equiv.Perm (ι → Fin d)} (h : IsLocalPerm (S : Set ι) σ) :
    σ.permMatrix ℂ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S := by
  classical
  let e : Fin (Fintype.card S) → ι := fun j => ((Fintype.equivFin S).symm j : ι)
  have he : Function.Injective e :=
    Subtype.val_injective.comp (Fintype.equivFin S).symm.injective
  have hmem : ∀ i, i ∈ S ↔ ∃ j, e j = i := fun i => by
    constructor
    · intro hi
      exact ⟨Fintype.equivFin S ⟨i, hi⟩, by simp [e]⟩
    · rintro ⟨j, rfl⟩
      exact ((Fintype.equivFin S).symm j).prop
  have hrange : Finset.univ.image e = S := Finset.ext fun i => by simpa using (hmem i).symm
  let X : Matrix (Fin (Fintype.card S) → Fin d) (Fin (Fintype.card S) → Fin d) ℂ :=
    of fun u w => if ∃ x : ι → Fin d, x ∘ e = u ∧ σ x ∘ e = w then 1 else 0
  have hX : σ.permMatrix ℂ = embedOp e X := by
    ext x y
    rw [permMatrix_cfg_apply, embedOp_apply]
    simp only [X, of_apply]
    by_cases hxy : σ x = y
    · subst hxy
      have hag : AgreeOff e x (σ x) := fun i hi =>
        (h.1 x i fun hiS => by obtain ⟨j, hj⟩ := (hmem i).mp hiS; exact hi j hj).symm
      simp only [hag, ite_true,
        show ∃ x' : ι → Fin d, x' ∘ e = x ∘ e ∧ σ x' ∘ e = σ x ∘ e from ⟨x, rfl, rfl⟩]
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
def shiftPerm (t : ι) (f : (ι → Fin d) → Fin d)
    (hf : ∀ x c, f (Function.update x t c) = f x) : Equiv.Perm (ι → Fin d) where
  toFun x := Function.update x t (x t + f x)
  invFun x := Function.update x t (x t - f x)
  left_inv x := by simp [hf]
  right_inv x := by simp [hf]

omit [Fintype ι] in
theorem shiftPerm_apply (t : ι) (f : (ι → Fin d) → Fin d)
    (hf : ∀ x c, f (Function.update x t c) = f x) (x : ι → Fin d) :
    shiftPerm t f hf x = Function.update x t (x t + f x) :=
  rfl

omit [Fintype ι] in
theorem isLocalPerm_shiftPerm {S : Set ι} {t : ι} (ht : t ∈ S)
    (f : (ι → Fin d) → Fin d)
    (hf : ∀ x c, f (Function.update x t c) = f x)
    (hfS : ∀ x y, (∀ j ∈ S, x j = y j) → f x = f y) : IsLocalPerm S (shiftPerm t f hf) := by
  refine ⟨fun x i hi => ?_, fun x y hxy i hi => ?_⟩
  · rw [shiftPerm_apply, Function.update_of_ne (by rintro rfl; exact hi ht)]
  · simp only [shiftPerm_apply]
    by_cases hit : i = t
    · subst hit; simp [hxy i ht, hfS x y hxy]
    · rw [Function.update_of_ne hit, Function.update_of_ne hit, hxy i hi]

end Shift

/-! ### Permutations of configurations induced by permutations of the sites -/

section SitePermutation

/-- The permutation `x ↦ x ∘ π` of the configurations induced by a permutation `π` of the
sites. -/
def cfgPerm (π : Equiv.Perm ι) : Equiv.Perm (ι → Fin d) where
  toFun x := x ∘ π
  invFun x := x ∘ π.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

omit [Fintype ι] [DecidableEq ι] in
theorem cfgPerm_apply (π : Equiv.Perm ι) (x : ι → Fin d) : cfgPerm π x = x ∘ π := rfl

theorem permMatrix_cfgPerm_mul_permMatrix_cfgPerm (π σ : Equiv.Perm ι) :
    (cfgPerm (d := d) π).permMatrix ℂ * (cfgPerm σ).permMatrix ℂ =
      (cfgPerm (π * σ)).permMatrix ℂ := by
  rw [← Matrix.permMatrix_mul]
  congr 1

omit [DecidableEq ι] in
theorem permMatrix_cfgPerm_one : (cfgPerm (d := d) (1 : Equiv.Perm ι)).permMatrix ℂ = 1 := by
  have : cfgPerm (d := d) (1 : Equiv.Perm ι) = 1 := by ext x i; rfl
  rw [this, Matrix.permMatrix_one]

/-- **Moving single-site operators across a permutation of sites.** -/
theorem permMatrix_cfgPerm_mul_rectKronecker (π : Equiv.Perm ι)
    (g : ι → Matrix (Fin d) (Fin d) ℂ) :
    (cfgPerm π).permMatrix ℂ * rectKronecker g =
      rectKronecker (fun i => g (π.symm i)) * (cfgPerm π).permMatrix ℂ := by
  classical
  ext x y
  simp only [mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, rectKronecker_apply]
  rw [Finset.sum_eq_single ((cfgPerm π).symm y)]
  · simp only [Equiv.apply_symm_apply, ite_true]
    refine Fintype.prod_equiv π _ _ fun i => ?_
    simp [cfgPerm]
  · intro z _ hz
    rw [ite_eq_right fun h => hz (by rw [← h, Equiv.symm_apply_apply])]
  · simp

/-- The chain form of `permMatrix_cfgPerm_mul_rectKronecker`, for the sites `Fin N`. -/
theorem permMatrix_cfgPerm_mul_finKronecker {N : ℕ} (π : Equiv.Perm (Fin N))
    (g : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    (cfgPerm π).permMatrix ℂ * finKronecker g =
      finKronecker (fun i => g (π.symm i)) * (cfgPerm π).permMatrix ℂ :=
  permMatrix_cfgPerm_mul_rectKronecker π g

/-- **Relabelling the sites of an embedded operator.** Conjugating `X` at the sites `e` by the
permutation of configurations `x ↦ x ∘ σ` places `X` at the sites `σ ∘ e`. -/
theorem permMatrix_cfgPerm_mul_embedOp_mul {κ : Type*} [Fintype κ]
    (σ : Equiv.Perm ι) (e : κ → ι) (X : Matrix (κ → Fin d) (κ → Fin d) ℂ) :
    (cfgPerm σ).permMatrix ℂ * embedOp e X * (cfgPerm σ.symm).permMatrix ℂ =
      embedOp (σ ∘ e) X := by
  classical
  ext x y
  simp only [mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_eq_single ((cfgPerm σ.symm).symm y), ite_eq_left (Equiv.apply_symm_apply _ _)]
  rotate_left
  · intro w _ hw
    rw [ite_eq_right fun h => hw (by rw [← h, Equiv.symm_apply_apply])]
  · simp
  rw [embedOp_apply, embedOp_apply]
  have hy : (cfgPerm σ.symm).symm y = y ∘ σ := by
    funext i; simp [cfgPerm]
  rw [hy]
  have hag : AgreeOff e (cfgPerm σ x) (y ∘ σ) ↔ AgreeOff (σ ∘ e) x y := by
    constructor
    · intro h i hi
      have := h (σ.symm i) fun j hj => hi j (by rw [Function.comp_apply, hj]; simp)
      simpa [cfgPerm] using this
    · intro h i hi
      exact h (σ i) fun j hj => hi j (σ.injective hj)
  by_cases h : AgreeOff (σ ∘ e) x y
  · rw [ite_eq_left (hag.mpr h), ite_eq_left h]; rfl
  · rw [ite_eq_right (fun h' => h (hag.mp h')), ite_eq_right h]

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

/-- The SWAP of the two sites of a two-site chain. -/
def swapTwo : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ := permOp (Equiv.swap 0 1)

/-- Two sites `i ≠ j` as a map `Fin 2 → Fin n`. -/
def pairSites (i j : Fin n) : Fin 2 → Fin n := ![i, j]

theorem pairSites_injective {i j : Fin n} (hij : i ≠ j) : Function.Injective (pairSites i j) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [pairSites, eq_comm]

theorem image_univ_pairSites (i j : Fin n) : Finset.univ.image (pairSites i j) = {i, j} := by
  ext k
  simp [pairSites, Fin.exists_fin_two, eq_comm]

theorem permOp_swap_eq_embedOp {j j' : Fin n} (hjj' : j ≠ j') :
    permOp (d := d) (Equiv.swap j j') = embedOp (pairSites j j') swapTwo := by
  ext x y
  rw [embedOp_apply]
  simp only [permOp, swapTwo, of_apply]
  have key : y = x ∘ Equiv.swap j j' ↔ AgreeOff (pairSites j j') x y ∧
      y ∘ pairSites j j' = (x ∘ pairSites j j') ∘ Equiv.swap 0 1 := by
    constructor
    · rintro rfl
      refine ⟨fun i hi => ?_, ?_⟩
      · have h0 : i ≠ j := fun h => hi 0 (by simp [pairSites, h])
        have h1 : i ≠ j' := fun h => hi 1 (by simp [pairSites, h])
        simp [Equiv.swap_apply_of_ne_of_ne h0 h1]
      · funext a; fin_cases a <;> simp [pairSites]
    · rintro ⟨h, h'⟩
      funext i
      by_cases hi0 : i = j
      · subst hi0; have := congrFun h' 0; simpa [pairSites] using this
      by_cases hi1 : i = j'
      · subst hi1; have := congrFun h' 1; simpa [pairSites] using this
      · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hi0 hi1]
        exact (h i fun a ha => by fin_cases a <;> simp_all [pairSites, eq_comm]).symm
  by_cases h : y = x ∘ Equiv.swap j j'
  · obtain ⟨h1, h2⟩ := key.1 h
    rw [ite_eq_left h, ite_eq_left h1, ite_eq_left h2]
  · rw [ite_eq_right h]
    split_ifs with h1 h2 <;> first | rfl | exact absurd (key.2 ⟨h1, h2⟩) h

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

/-- Site permutations act multiplicatively on the full chain Hilbert space. -/
def permOpHom : Equiv.Perm (Fin N) →* Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ where
  toFun := permOp
  map_one' := by
    ext x y
    simp only [permOp, of_apply, Equiv.Perm.coe_one, Function.comp_id, one_apply, eq_comm]
  map_mul' σ τ := by
    ext x y
    simp only [permOp, of_apply, mul_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (x ∘ σ)]
    simp only [Finset.mem_univ, ite_true, Equiv.Perm.coe_mul]
    rfl

/-- The identity site permutation induces the identity chain operator. -/
@[simp] theorem permOp_one : permOp (d := d) (1 : Equiv.Perm (Fin N)) = 1 :=
  (permOpHom (d := d)).map_one

/-- Composition of site permutations is multiplication of their chain operators. -/
theorem permOp_mul (σ τ : Equiv.Perm (Fin N)) :
    permOp (d := d) (σ * τ) = permOp σ * permOp τ :=
  (permOpHom (d := d)).map_mul σ τ

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

/-- Site permutation operators preserve products exactly, with no scalar
phase discarded. Source: swap routing in Section 5 of the circuit audit. -/
theorem permOp_list_prod (l : List (Equiv.Perm (Fin n))) :
    permOp (d := d) l.prod = (l.map (permOp (d := d))).prod :=
  map_list_prod (permOpHom (d := d)) l

/-- The permutation of sites `τ` acts on vectors by precomposing configurations with `τ`. -/
theorem permOp_mulVec (τ : Equiv.Perm (Fin n)) (v : (Fin n → Fin d) → ℂ) :
    permOp τ *ᵥ v = v ∘ fun x => x ∘ τ := by
  classical
  funext x
  simp [permOp, mulVec, dotProduct]

end Chain

end QuantumCircuit
