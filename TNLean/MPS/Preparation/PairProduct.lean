/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SiteEmbedding

/-!
# Products of two-site gates on an open chain

The circuits of arXiv:2307.01696 are built from unitaries acting on two neighbouring sites.
This file records, on an open chain of `n` sites, the operators that are products of at most
`K` such gates (`MPSPreparation.IsPairProduct`), and shows:

* the class is closed under products, adjoints, and placing the chain inside a larger chain
  as a block of consecutive sites (`MPSPreparation.IsPairProduct.embedOp`);
* every operator acting on the sites `S` of the chain is of the form `X ⊗ 1` with `X` on the
  sites `S` (`MPSPreparation.exists_embedOp_eq_of_mem_supportedOperators`);
* a unitary acting on any two sites `{s, t}`, neighbouring or not, is a product of at most
  `2n` gates on neighbouring sites: it is conjugated to a neighbouring pair by SWAP gates
  (`MPSPreparation.isPairProduct_of_mem_supportedOperators_pair`). This is the use of SWAP
  gates in arXiv:2307.01696, paragraph "The sequential-RG circuit": "the inputs of the
  unitary ... are separated by `O(q)` sites, which requires one to implement SWAP gates".
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d m n : ℕ}

/-- A unitary gate acting on two neighbouring sites `{p, p + 1}` of the open chain of `n`
sites.

Source: arXiv:2307.01696, main text before Theorem 1 (local circuits of two-site gates). -/
def IsNeighbourGate (Z : Matrix (Cfg d n) (Cfg d n) ℂ) : Prop :=
  Z ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ) ∧
    ∃ p p' : Fin n, p'.val = p.val + 1 ∧ Z ∈ supportedOperators d {p, p'}

/-- `X` is a product of at most `K` unitary gates, each acting on two neighbouring sites of
the open chain of `n` sites.

Source: arXiv:2307.01696, main text before Theorem 1 and paragraph "The sequential-RG
circuit" (gates with constant support expressed through local gates). -/
def IsPairProduct (d n K : ℕ) (X : Matrix (Cfg d n) (Cfg d n) ℂ) : Prop :=
  ∃ l : List (Matrix (Cfg d n) (Cfg d n) ℂ), l.length ≤ K ∧ (∀ Z ∈ l, IsNeighbourGate Z) ∧
    X = l.prod

namespace IsPairProduct

theorem one (K : ℕ) : IsPairProduct d n K 1 :=
  ⟨[], by simp, by simp, by simp⟩

theorem mono {K K' : ℕ} (hK : K ≤ K') {X : Matrix (Cfg d n) (Cfg d n) ℂ}
    (hX : IsPairProduct d n K X) : IsPairProduct d n K' X := by
  obtain ⟨l, hl, hg, rfl⟩ := hX
  exact ⟨l, hl.trans hK, hg, rfl⟩

theorem mul {K K' : ℕ} {X Y : Matrix (Cfg d n) (Cfg d n) ℂ} (hX : IsPairProduct d n K X)
    (hY : IsPairProduct d n K' Y) : IsPairProduct d n (K + K') (X * Y) := by
  obtain ⟨l, hl, hg, rfl⟩ := hX
  obtain ⟨l', hl', hg', rfl⟩ := hY
  refine ⟨l ++ l', by simp; omega, fun Z hZ => ?_, by simp⟩
  rcases List.mem_append.mp hZ with h | h
  · exact hg Z h
  · exact hg' Z h

theorem of_isNeighbourGate {Z : Matrix (Cfg d n) (Cfg d n) ℂ} (hZ : IsNeighbourGate Z) :
    IsPairProduct d n 1 Z :=
  ⟨[Z], by simp, by simpa using hZ, by simp⟩

theorem mem_unitary {K : ℕ} {X : Matrix (Cfg d n) (Cfg d n) ℂ} (hX : IsPairProduct d n K X) :
    X ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ) := by
  obtain ⟨l, -, hg, rfl⟩ := hX
  induction l with
  | nil => exact Submonoid.one_mem _
  | cons Z l ih =>
    rw [List.prod_cons]
    exact Submonoid.mul_mem _ (hg Z (by simp)).1 (ih fun Z' h => hg Z' (by simp [h]))

theorem star {K : ℕ} {X : Matrix (Cfg d n) (Cfg d n) ℂ} (hX : IsPairProduct d n K X) :
    IsPairProduct d n K (star X) := by
  obtain ⟨l, hl, hg, rfl⟩ := hX
  refine ⟨(l.map Star.star).reverse, by simpa using hl, fun Z hZ => ?_, ?_⟩
  · simp only [List.mem_reverse, List.mem_map] at hZ
    obtain ⟨Z', hZ', rfl⟩ := hZ
    obtain ⟨hu, p, p', hp, hS⟩ := hg Z' hZ'
    exact ⟨Unitary.star_mem hu, p, p', hp, star_mem_supportedOperators hS⟩
  · clear hl hg
    induction l with
    | nil => simp
    | cons Z l ih =>
      simp only [List.prod_cons, StarMul.star_mul, List.map_cons, List.reverse_cons,
        List.prod_append, List.prod_cons, List.prod_nil, mul_one]
      rw [ih]

theorem list_prod {K : ℕ} (l : List (Matrix (Cfg d n) (Cfg d n) ℂ))
    (hl : ∀ X ∈ l, IsPairProduct d n K X) : IsPairProduct d n (l.length * K) l.prod := by
  induction l with
  | nil => simpa using one 0
  | cons X l ih =>
    rw [List.prod_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact (hl X (by simp)).mul (ih fun Y h => hl Y (by simp [h]))

theorem finset_prod {ι : Type*} (s : Finset ι) {K : ℕ}
    (f : ι → Matrix (Cfg d n) (Cfg d n) ℂ) (hf : ∀ i ∈ s, IsPairProduct d n K (f i))
    (hcomm : (s : Set ι).Pairwise (Function.onFun Commute f)) :
    IsPairProduct d n (s.card * K) (s.noncommProd f hcomm) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one 0
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Finset.card_insert_of_notMem ha,
      Nat.succ_mul, Nat.add_comm]
    exact (hf a (by simp)).mul (ih (fun i hi => hf i (by simp [hi]))
      (hcomm.mono (by simp)))

end IsPairProduct

theorem embedOp_list_prod {e : Fin m → Fin n} (he : Function.Injective e)
    (l : List (Matrix (Cfg d m) (Cfg d m) ℂ)) :
    embedOp e l.prod = (l.map (embedOp e)).prod := by
  induction l with
  | nil => simp
  | cons X l ih => rw [List.prod_cons, ← embedOp_mul he, ih, List.map_cons, List.prod_cons]

/-- Placing the chain of `m` sites as the consecutive sites `a, a + 1, …, a + m - 1` of a chain
of `n` sites keeps products of two-site gates. -/
theorem IsPairProduct.embedOp {K : ℕ} {e : Fin m → Fin n} (he : Function.Injective e) {a : ℕ}
    (hea : ∀ i, (e i).val = a + i.val) {X : Matrix (Cfg d m) (Cfg d m) ℂ}
    (hX : IsPairProduct d m K X) : IsPairProduct d n K (embedOp e X) := by
  obtain ⟨l, hl, hg, rfl⟩ := hX
  refine ⟨l.map (MPSPreparation.embedOp e), by simpa using hl, fun Z hZ => ?_,
    embedOp_list_prod he l⟩
  obtain ⟨Z', hZ', rfl⟩ := List.mem_map.mp hZ
  obtain ⟨hu, p, p', hp, hS⟩ := hg Z' hZ'
  refine ⟨embedOp_mem_unitary he hu, e p, e p', by rw [hea, hea, hp]; ring, ?_⟩
  have := embedOp_mem_supportedOperators_image he hS
  rwa [Set.image_pair] at this

/-! ### Operators acting on a subset of the sites -/

/-- Every operator acting on the range of `e` is `X ⊗ 1` for an operator `X` on the placed
sites. -/
theorem exists_embedOp_eq_of_mem_supportedOperators {e : Fin m → Fin n}
    (he : Function.Injective e) {Z : Matrix (Cfg d n) (Cfg d n) ℂ}
    (hZ : Z ∈ supportedOperators d (Set.range e)) :
    ∃ X : Matrix (Cfg d m) (Cfg d m) ℂ, Z = embedOp e X := by
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨A, hA, rfl⟩ := hx
    refine ⟨finKronecker (A ∘ e), ?_⟩
    rw [embedOp_finKronecker he]
    congr 1
    funext i
    by_cases h : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := h
      rw [he.extend_apply]; rfl
    · rw [Function.extend_apply' _ _ _ h, Pi.one_apply]
      exact hA i fun ⟨j, hj⟩ => h ⟨j, hj⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, rfl⟩ := hx
    obtain ⟨Y, rfl⟩ := hy
    exact ⟨X + Y, (embedOp_add e X Y).symm⟩
  | smul c x _ hx =>
    obtain ⟨X, rfl⟩ := hx
    exact ⟨c • X, (embedOp_smul e c X).symm⟩

/-- `X ↦ X ⊗ 1` is injective. -/
theorem embedOp_injective {e : Fin m → Fin n} (he : Function.Injective e) (hd : 0 < d) :
    Function.Injective (embedOp (d := d) e) := by
  intro X Y h
  ext u v
  let z : Cfg d n := fun _ => ⟨0, hd⟩
  have hAg : AgreeOff e (Function.extend e u z) (Function.extend e v z) := fun i hi => by
    rw [Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => hi j hj,
      Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => hi j hj]
  have := congrFun (congrFun h (Function.extend e u z)) (Function.extend e v z)
  rwa [embedOp_apply, embedOp_apply, ite_eq_left hAg, ite_eq_left hAg, Function.extend_comp he,
    Function.extend_comp he] at this

theorem mem_unitary_of_embedOp_mem_unitary {e : Fin m → Fin n} (he : Function.Injective e)
    (hd : 0 < d) {X : Matrix (Cfg d m) (Cfg d m) ℂ}
    (hX : embedOp e X ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ)) :
    X ∈ unitary (Matrix (Cfg d m) (Cfg d m) ℂ) := by
  rw [Unitary.mem_iff] at hX ⊢
  rw [embedOp_star, embedOp_mul he, embedOp_mul he, ← embedOp_one (d := d) e] at hX
  exact ⟨embedOp_injective he hd hX.1, embedOp_injective he hd hX.2⟩

/-! ### Moving a gate with SWAP gates -/

/-- The operator permuting the sites of the chain by `τ`: `|x⟩ ↦ |x ∘ τ⁻¹⟩`. -/
def permOp (τ : Equiv.Perm (Fin n)) : Matrix (Cfg d n) (Cfg d n) ℂ :=
  of fun x y => if y = x ∘ τ then 1 else 0

theorem permOp_mul_mul_conjTranspose (τ : Equiv.Perm (Fin n))
    (X : Matrix (Cfg d n) (Cfg d n) ℂ) :
    permOp τ * X * (permOp τ)ᴴ = X.submatrix (· ∘ τ) (· ∘ τ) := by
  ext x y
  simp only [mul_apply, permOp, of_apply, conjTranspose_apply, submatrix_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp [apply_ite star]

theorem embedOp_submatrix_perm (e : Fin m → Fin n) (τ : Equiv.Perm (Fin n))
    (X : Matrix (Cfg d m) (Cfg d m) ℂ) :
    (embedOp e X).submatrix (· ∘ τ) (· ∘ τ) = embedOp (τ ∘ e) X := by
  ext x y
  simp only [submatrix_apply, embedOp_apply]
  have : AgreeOff e (x ∘ τ) (y ∘ τ) ↔ AgreeOff (τ ∘ e) x y := by
    constructor
    · intro h i hi
      have := h (τ.symm i) fun j hj => hi j (by
        rw [Function.comp_apply, hj, Equiv.apply_symm_apply])
      simpa using this
    · intro h i hi
      exact h (τ i) fun j hj => hi j (τ.injective hj)
  simp only [this]
  rfl

/-- The SWAP of the two sites of a two-site chain. -/
def swapTwo : Matrix (Cfg d 2) (Cfg d 2) ℂ := permOp (Equiv.swap 0 1)

/-- Two sites `i ≠ j` as a map `Fin 2 → Fin n`. -/
def pairSites (i j : Fin n) : Fin 2 → Fin n := ![i, j]

theorem pairSites_injective {i j : Fin n} (hij : i ≠ j) : Function.Injective (pairSites i j) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [pairSites, eq_comm]

theorem range_pairSites (i j : Fin n) : Set.range (pairSites i j) = {i, j} := by
  ext k
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, pairSites]
  constructor
  · rintro ⟨a, rfl⟩; fin_cases a <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

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

theorem permOp_mem_unitary (τ : Equiv.Perm (Fin n)) :
    permOp (d := d) τ ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ) := by
  have hP : ∀ x z : Cfg d n, (x = z ∘ τ) ↔ (z = x ∘ τ.symm) := fun x z => by
    constructor
    · rintro rfl; funext i; simp
    · rintro rfl; funext i; simp
  rw [Unitary.mem_iff]
  constructor
  · ext x y
    simp only [mul_apply, star_apply, permOp, of_apply, apply_ite star, star_one, star_zero,
      mul_ite, mul_one, mul_zero]
    simp_rw [hP x, hP y]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true, one_apply]
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [ite_eq_right, ite_eq_right hxy]
      intro h; exact hxy (by funext i; simpa using (congrFun h (τ i)).symm)
  · ext x y
    simp only [mul_apply, star_apply, permOp, of_apply, apply_ite star, star_one, star_zero,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true, one_apply]
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [ite_eq_right, ite_eq_right hxy]
      intro h; exact hxy (by funext i; simpa using (congrFun h (τ.symm i)).symm)

/-- The SWAP gate of two neighbouring sites. -/
theorem isNeighbourGate_permOp_swap {j j' : Fin n} (hj : j'.val = j.val + 1) :
    IsNeighbourGate (permOp (d := d) (Equiv.swap j j')) := by
  have hjj' : j ≠ j' := fun h => by rw [h] at hj; omega
  refine ⟨permOp_mem_unitary _, j, j', hj, ?_⟩
  rw [permOp_swap_eq_embedOp hjj', ← range_pairSites]
  exact embedOp_mem_supportedOperators (pairSites_injective hjj') _

theorem embedOp_comp_perm (e : Fin m → Fin n) (σ : Equiv.Perm (Fin m))
    (X : Matrix (Cfg d m) (Cfg d m) ℂ) :
    embedOp (e ∘ σ) X = embedOp e (X.submatrix (· ∘ σ) (· ∘ σ)) := by
  ext x y
  simp only [embedOp_apply, submatrix_apply]
  have : AgreeOff (e ∘ σ) x y ↔ AgreeOff e x y := by
    constructor
    · intro h i hi; exact h i fun j hj => hi (σ j) hj
    · intro h i hi; exact h i fun j hj => hi (σ.symm j) (by simpa using hj)
  simp only [this]
  rfl

private theorem isPairProduct_embedOp_pairSites_of_lt {g : Matrix (Cfg d 2) (Cfg d 2) ℂ}
    (hg : g ∈ unitary (Matrix (Cfg d 2) (Cfg d 2) ℂ)) :
    ∀ k : ℕ, ∀ i j : Fin n, j.val = i.val + k + 1 →
      IsPairProduct d n (2 * k + 1) (embedOp (pairSites i j) g) := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    have hne : i ≠ j := fun h => by rw [h] at hij; omega
    refine IsPairProduct.of_isNeighbourGate ⟨embedOp_mem_unitary (pairSites_injective hne) hg,
      i, j, by omega, ?_⟩
    rw [← range_pairSites]
    exact embedOp_mem_supportedOperators (pairSites_injective hne) _
  | succ k ih =>
    intro i j hij
    let j' : Fin n := ⟨j.val - 1, by omega⟩
    have hj' : j'.val = i.val + k + 1 := by simp only [j']; omega
    have hjj : j.val = j'.val + 1 := by simp only [j']; omega
    have hS := isNeighbourGate_permOp_swap (d := d) hjj
    have hij' : i ≠ j' := fun h => by rw [h] at hj'; omega
    have hij2 : i ≠ j := fun h => by rw [h] at hij; omega
    have hcomp : (Equiv.swap j' j) ∘ pairSites i j' = pairSites i j := by
      funext a
      fin_cases a
      · simp [pairSites, Equiv.swap_apply_of_ne_of_ne hij' hij2]
      · simp [pairSites]
    have heq : embedOp (pairSites i j) g =
        permOp (Equiv.swap j' j) * embedOp (pairSites i j') g * (permOp (Equiv.swap j' j))ᴴ := by
      rw [permOp_mul_mul_conjTranspose, embedOp_submatrix_perm, hcomp]
    rw [heq, show 2 * (k + 1) + 1 = 1 + (2 * k + 1) + 1 by ring]
    exact ((IsPairProduct.of_isNeighbourGate hS).mul (ih i j' hj')).mul
      (IsPairProduct.of_isNeighbourGate hS).star

/-- **Gates on distant sites.** A unitary gate on two distinct sites `i`, `j` of the open chain
of `n` sites is a product of at most `2n` gates on neighbouring sites: SWAP gates bring `j`
next to `i` and back.

Source: arXiv:2307.01696, paragraph "The sequential-RG circuit": the inputs "are separated by
`O(q)` sites, which requires one to implement SWAP gates". -/
theorem isPairProduct_embedOp_pairSites {i j : Fin n} (hij : i ≠ j)
    {g : Matrix (Cfg d 2) (Cfg d 2) ℂ} (hg : g ∈ unitary (Matrix (Cfg d 2) (Cfg d 2) ℂ)) :
    IsPairProduct d n (2 * n) (embedOp (pairSites i j) g) := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact (isPairProduct_embedOp_pairSites_of_lt hg (j.val - i.val - 1) i j (by omega)).mono
      (by omega)
  · have hswap : pairSites i j = pairSites j i ∘ Equiv.swap 0 1 := by
      funext a; fin_cases a <;> simp [pairSites]
    have hg' : g.submatrix (· ∘ Equiv.swap 0 1) (· ∘ Equiv.swap 0 1) ∈
        unitary (Matrix (Cfg d 2) (Cfg d 2) ℂ) := by
      rw [← permOp_mul_mul_conjTranspose]
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (permOp_mem_unitary _) hg)
        (Unitary.star_mem (permOp_mem_unitary _))
    rw [hswap, embedOp_comp_perm]
    exact (isPairProduct_embedOp_pairSites_of_lt hg' (i.val - j.val - 1) j i
      (by omega)).mono (by omega)

/-- A unitary acting on two distinct sites is a product of at most `2n` gates on neighbouring
sites. -/
theorem isPairProduct_of_mem_supportedOperators_pair (hd : 0 < d) {i j : Fin n} (hij : i ≠ j)
    {Z : Matrix (Cfg d n) (Cfg d n) ℂ} (hZu : Z ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ))
    (hZ : Z ∈ supportedOperators d {i, j}) : IsPairProduct d n (2 * n) Z := by
  rw [← range_pairSites] at hZ
  obtain ⟨g, rfl⟩ := exists_embedOp_eq_of_mem_supportedOperators (pairSites_injective hij) hZ
  exact isPairProduct_embedOp_pairSites hij
    (mem_unitary_of_embedOp_mem_unitary (pairSites_injective hij) hd hZu)

end MPSPreparation
