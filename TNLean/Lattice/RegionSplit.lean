/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteEmbedding
import QICLean.Channel.FiniteProduct

/-!
# Operators on a region in the coordinates of the region and its complement

On a finite set `ι` of sites with local dimension `q`, a region `S` splits every configuration
into its restrictions to `S` and to `Sᶜ`. In these coordinates an operator acting on `S` is
`A' ⊗ 1`, and an operator acting on a set disjoint from `S` is `1 ⊗ A'`. Nothing here depends
on a geometry of the sites, so the one-dimensional chain and the square lattice both use it.

## Main definitions

* `TNLean.Lattice.sheetSplit`: the configurations of `ι` as pairs of configurations on `S` and
  on `Sᶜ`.
* `TNLean.Lattice.siteLift`: the operator `X_D ⊗ 1_{ι ∖ D}`.

## Main results

* `TNLean.Lattice.exists_kronecker_one_of_mem_supportedOperators`: an operator acting on `S`
  is `A' ⊗ 1` in the coordinates of `sheetSplit S`.
* `TNLean.Lattice.exists_one_kronecker_of_mem_supportedOperators`: an operator acting on a set
  disjoint from `S` is `1 ⊗ A'`.
* `QuantumCircuit.embedOp_val_eq_kronecker_one_submatrix`: a local matrix placed on `S` is
  `K ⊗ 1` in the coordinates of `S` and its complement.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `05-frames.tex`, lines 352–394, and
  `02-information.tex`, lines 416–424.
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 501–545.

Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The statements and
proofs here are formalized independently from the manuscripts; no upstream Lean proof text was
reused.
-/

open Matrix QuantumCircuit
open scoped Kronecker

namespace TNLean.Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-! ### Two regions -/

/-- The raw configurations of a sheet as pairs of configurations on `S` and on `Sᶜ`. -/
abbrev sheetSplit (q : ℕ) (S : Finset ι) : (ι → Fin q) ≃ (S → Fin q) × (↥Sᶜ → Fin q) :=
  FiniteProduct.splitEquiv (fun _ : ι => Fin q) S

/-- A product operator in the coordinates of `sheetSplit S` is the Kronecker product of its
restrictions to `S` and to `Sᶜ`. -/
theorem rectKronecker_submatrix_sheetSplit (S : Finset ι) (m : ι → Matrix (Fin q) (Fin q) ℂ) :
    (rectKronecker m).submatrix (sheetSplit q S).symm (sheetSplit q S).symm =
      rectKronecker (fun v : S => m v) ⊗ₖ rectKronecker (fun v : ↥Sᶜ => m v) := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  simp only [submatrix_apply, rectKronecker_apply, kroneckerMap_apply]
  rw [← Finset.prod_mul_prod_compl S, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort Sᶜ]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    simp [FiniteProduct.splitEquiv_symm_apply_of_mem _ S _ _ _ v.2]
  · refine Finset.prod_congr rfl fun v _ => ?_
    simp [FiniteProduct.splitEquiv_symm_apply_of_notMem _ S _ _ _ (Finset.mem_compl.mp v.2)]

/-- An operator acting on `S` is `A' ⊗ 1` in the coordinates of `sheetSplit S`. -/
theorem exists_kronecker_one_of_mem_supportedOperators {S : Finset ι}
    {A : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hA : A ∈ supportedOperators q (S : Set ι)) :
    ∃ A' : Matrix (S → Fin q) (S → Fin q) ℂ,
      A.submatrix (sheetSplit q S).symm (sheetSplit q S).symm =
        A' ⊗ₖ (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ) := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨rectKronecker fun v : S => m v, ?_⟩
    rw [rectKronecker_submatrix_sheetSplit]
    congr 1
    rw [← rectKronecker_one (ν := ↥Sᶜ) (ι := Fin q)]
    congr 1
    funext v
    exact hm v (Finset.mem_compl.mp v.2)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    exact ⟨X + Y, by rw [add_kronecker, ← hX, ← hY]; rfl⟩
  | smul c x _ hx =>
    obtain ⟨X, hX⟩ := hx
    exact ⟨c • X, by rw [smul_kronecker, ← hX]; rfl⟩

/-- An operator acting on a set disjoint from `S` is `1 ⊗ A'` in the coordinates of
`sheetSplit S`. -/
theorem exists_one_kronecker_of_mem_supportedOperators {S : Finset ι} {D : Set ι}
    (hD : Disjoint D (S : Set ι)) {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ supportedOperators q D) :
    ∃ A' : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ,
      A.submatrix (sheetSplit q S).symm (sheetSplit q S).symm =
        (1 : Matrix (S → Fin q) (S → Fin q) ℂ) ⊗ₖ A' := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨rectKronecker fun v : ↥Sᶜ => m v, ?_⟩
    rw [rectKronecker_submatrix_sheetSplit]
    congr 1
    rw [← rectKronecker_one (ν := ↥S) (ι := Fin q)]
    congr 1
    funext v
    exact hm v fun hv => Set.disjoint_left.mp hD hv v.2
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    exact ⟨X + Y, by rw [kronecker_add, ← hX, ← hY]; rfl⟩
  | smul c x _ hx =>
    obtain ⟨X, hX⟩ := hx
    exact ⟨c • X, by rw [kronecker_smul, ← hX]; rfl⟩

/-! ### Operators on a set of sites -/

/-- The operator `X_D ⊗ 1_{Λ ∖ D}` on the raw registers of a sheet, for an operator `X` on the
sites of `D`. -/
noncomputable def siteLift (D : Finset ι) (X : Matrix (D → Fin q) (D → Fin q) ℂ) :
    Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  embedOp (Subtype.val : D → ι) X

theorem siteLift_mul (D : Finset ι) (X Y : Matrix (D → Fin q) (D → Fin q) ℂ) :
    siteLift D X * siteLift D Y = siteLift D (X * Y) :=
  embedOp_mul Subtype.val_injective X Y

theorem siteLift_conjTranspose (D : Finset ι) (X : Matrix (D → Fin q) (D → Fin q) ℂ) :
    (siteLift D X)ᴴ = siteLift D Xᴴ :=
  embedOp_conjTranspose _ X

/-- An operator lifted from `D` acts on the sites of `D`. -/
theorem siteLift_mem_supportedOperators (D : Finset ι)
    (X : Matrix (D → Fin q) (D → Fin q) ℂ) :
    siteLift D X ∈ supportedOperators q (D : Set ι) := by
  have h := embedOp_mem_supportedOperators (d := q) (Subtype.val_injective (p := (· ∈ D))) X
  rwa [Subtype.range_coe_subtype] at h

end TNLean.Lattice

namespace QuantumCircuit

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- A local matrix placed on a region `S` is `K ⊗ 1` in the coordinates of `S` and its
complement. -/
theorem embedOp_val_eq_kronecker_one_submatrix (S : Finset ι)
    (K : Matrix (S → Fin q) (S → Fin q) ℂ) :
    embedOp (fun x : S => x.val) K = (K ⊗ₖ (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ)).submatrix
      (FiniteProduct.splitEquiv (fun _ : ι => Fin q) S)
      (FiniteProduct.splitEquiv (fun _ : ι => Fin q) S) := by
  ext c c'
  simp only [embedOp_apply, submatrix_apply, kroneckerMap_apply, one_apply]
  have hagree : AgreeOff (fun x : S => x.val) c c' ↔
      (FiniteProduct.splitEquiv (fun _ : ι => Fin q) S c).2 =
        (FiniteProduct.splitEquiv (fun _ : ι => Fin q) S c').2 := by
    constructor
    · intro h
      funext v
      exact h v fun j hj => (Finset.mem_compl.mp v.2) (hj ▸ j.2)
    · intro h i hi
      have hiS : i ∉ S := fun hiS => hi ⟨i, hiS⟩ rfl
      exact congrFun h ⟨i, Finset.mem_compl.mpr hiS⟩
  by_cases h : AgreeOff (fun x : S => x.val) c c'
  · simp only [h, hagree.mp h, ite_true, mul_one]
    rfl
  · simp only [h, hagree.not.mp h, ite_false, mul_zero]

/-- A matrix of the form `K ⊗ 1` in the coordinates of `S` acts on `S`. -/
theorem kronecker_one_submatrix_mem_supportedOperators (S : Finset ι)
    (K : Matrix (S → Fin q) (S → Fin q) ℂ) :
    (K ⊗ₖ (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ)).submatrix
        (FiniteProduct.splitEquiv (fun _ : ι => Fin q) S)
        (FiniteProduct.splitEquiv (fun _ : ι => Fin q) S) ∈
      supportedOperators q (S : Set ι) := by
  rw [← embedOp_val_eq_kronecker_one_submatrix]
  simpa using embedOp_mem_supportedOperators (e := fun x : S => x.val) Subtype.val_injective K

end QuantumCircuit
