/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.RegionMatrix
import TNLean.Circuit.SupportedOperators

/-!
# Operators on a region in the coordinates of the region and its complement

On a finite set `ι` of sites with local dimension `q`, a region `S` splits every configuration
into its restrictions to `S` and to `Sᶜ`. In these coordinates an operator acting on `S` is
`A' ⊗ 1`, and an operator acting on a set disjoint from `S` is `1 ⊗ A'`. Nothing here depends
on a geometry of the sites, so the one-dimensional chain and the square lattice both use it.

## Main definitions

* `TNLean.Lattice.sheetSplit`: the configurations of `ι` as pairs of configurations on `S` and
  on `Sᶜ`.

## Main results

* `TNLean.Lattice.exists_kronecker_one_of_mem_supportedOperators`: an operator acting on `S`
  is `A' ⊗ 1` in the coordinates of `sheetSplit S`.
* `TNLean.Lattice.exists_one_kronecker_of_mem_supportedOperators`: an operator acting on a set
  disjoint from `S` is `1 ⊗ A'`.
* `QuantumCircuit.kronecker_one_submatrix_mem_supportedOperators`: a matrix `K ⊗ 1` in the
  coordinates of `S` and its complement acts on `S`.

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
abbrev sheetSplit (q : ℕ) (S : Finset ι) :
    (ι → Fin q) ≃ (S → Fin q) × ({v // v ∉ S} → Fin q) :=
  ManyBody.cutEquiv (fun _ : ι => Fin q) S

/-- A product operator in the coordinates of `sheetSplit S` is the Kronecker product of its
restrictions to `S` and to `Sᶜ`. -/
theorem rectKronecker_submatrix_sheetSplit (S : Finset ι) (m : ι → Matrix (Fin q) (Fin q) ℂ) :
    (Matrix.piKronecker m).submatrix (sheetSplit q S).symm (sheetSplit q S).symm =
      Matrix.piKronecker (fun v : S => m v) ⊗ₖ Matrix.piKronecker (fun v : {v // v ∉ S} => m
          v) := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  simp only [submatrix_apply, Matrix.piKronecker_apply, kroneckerMap_apply]
  rw [← Fintype.prod_subtype_mul_prod_subtype (· ∈ S)]
  congr 1
  · refine Finset.prod_congr (Finset.ext fun _ => by simp) fun v _ => ?_
    simp [ManyBody.cutEquiv_symm_apply_mem _ _ v.2]
  · refine Finset.prod_congr rfl fun v _ => ?_
    simp [ManyBody.cutEquiv_symm_apply_not_mem _ _ v.2]

/-- An operator acting on `S` is `A' ⊗ 1` in the coordinates of `sheetSplit S`. -/
theorem exists_kronecker_one_of_mem_supportedOperators {S : Finset ι}
    {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S) :
    ∃ A' : Matrix (S → Fin q) (S → Fin q) ℂ,
      A.submatrix (sheetSplit q S).symm (sheetSplit q S).symm =
        A' ⊗ₖ (1 : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ) := by
  induction hA using ManyBody.supportedOperators_induction with
  | prod m hm =>
    refine ⟨Matrix.piKronecker fun v : S => m v, ?_⟩
    rw [rectKronecker_submatrix_sheetSplit]
    congr 1
    rw [← Matrix.piKronecker_one (ν := {v // v ∉ S}) (ι := fun _ ↦ Fin q)]
    congr 1
    funext v
    exact hm v v.2
  | add x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    exact ⟨X + Y, by rw [add_kronecker, ← hX, ← hY]; rfl⟩
  | smul c x _ hx =>
    obtain ⟨X, hX⟩ := hx
    exact ⟨c • X, by rw [smul_kronecker, ← hX]; rfl⟩

/-- An operator acting on a set disjoint from `S` is `1 ⊗ A'` in the coordinates of
`sheetSplit S`. -/
theorem exists_one_kronecker_of_mem_supportedOperators {S : Finset ι} {D : Finset ι}
    (hD : Disjoint D S) {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) D) :
    ∃ A' : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ,
      A.submatrix (sheetSplit q S).symm (sheetSplit q S).symm =
        (1 : Matrix (S → Fin q) (S → Fin q) ℂ) ⊗ₖ A' := by
  induction hA using ManyBody.supportedOperators_induction with
  | prod m hm =>
    refine ⟨Matrix.piKronecker fun v : {v // v ∉ S} => m v, ?_⟩
    rw [rectKronecker_submatrix_sheetSplit]
    congr 1
    rw [← Matrix.piKronecker_one (ν := ↥S) (ι := fun _ ↦ Fin q)]
    congr 1
    funext v
    exact hm v fun hv => Finset.disjoint_left.mp hD hv v.2
  | add x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    exact ⟨X + Y, by rw [kronecker_add, ← hX, ← hY]; rfl⟩
  | smul c x _ hx =>
    obtain ⟨X, hX⟩ := hx
    exact ⟨c • X, by rw [kronecker_smul, ← hX]; rfl⟩

end TNLean.Lattice

namespace QuantumCircuit

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- A matrix of the form `K ⊗ 1` in the coordinates of `S` acts on `S`: it is the placement
`ManyBody.place S K`. -/
theorem kronecker_one_submatrix_mem_supportedOperators (S : Finset ι)
    (K : Matrix (S → Fin q) (S → Fin q) ℂ) :
    (K ⊗ₖ (1 : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ)).submatrix
        (ManyBody.cutEquiv (fun _ : ι => Fin q) S)
        (ManyBody.cutEquiv (fun _ : ι => Fin q) S) ∈
      ManyBody.supportedOperators (fun _ ↦ Fin q) S := by
  have h := ManyBody.place_mem_supportedOperators (X := fun _ : ι ↦ Fin q) (D := S) K
  rwa [ManyBody.place, reindex_apply, Equiv.symm_symm] at h

end QuantumCircuit
