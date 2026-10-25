/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixKroneckerContraction
import TNLean.Lattice.RegionSplit
import TNLean.Lattice.Sheet.Operators
import QICLean.Entropy.FiniteProduct
import QICLean.Entropy.PurificationSplitting

/-!
# Splitting a sheet along three regions

The changes of ownership of §6.4 of the polynomial-PEPS manuscript act on a sheet whose sites
are partitioned into three regions `T`, `E` and `U = Λ ∖ (T ∪ E)`. This file provides the
coordinates of such a partition and the splitting consequence of Lemma 6.4 in them. Nothing here
depends on a geometry of the sites.

* `Sheet.threeSplit T E` identifies the raw configurations of the sheet with triples
  `((t, e), u)` of configurations on `T`, `E` and `(T ∪ E)ᶜ`. It refines the two-region
  coordinates `TNLean.Lattice.sheetSplit`, in which an operator on `S` is `A' ⊗ 1` and an
  operator on a set disjoint from `S` is `1 ⊗ A'`.
* An operator acting on `T ∪ E` is `A' ⊗ 1_U` in these coordinates, and an operator on a subset
  of `E` is `(1_T ⊗ A') ⊗ 1_U`. An operator supported disjointly from `T` is
  `1_T ⊗ V` after reassociating these same coordinates.
* `Sheet.one_kronecker_mul_stack`: the operator `1 ⊗ B` passes through a tagged stack
  `∑_t |t⟩ ⊗ S_t` whenever `B` commutes with every `S_t`.
* `Sheet.exists_sheetSplitting`: Lemma 6.4 `lem:splitting` for the regional mutual
  information `I_Ω(T:E)` of a unit vector `Ω` on the sheet: if `I_Ω(T:E) ≤ L^{-60}` there are an
  isometry `V` on the configurations of `U` and unit vectors `s`, `s'` with
  `‖(1_{TE} ⊗ V) Ω - s ⊗ s'‖ ≤ L^{-30}`. It is QICLean's
  `Matrix.exists_isIsometry_norm_sub_tensorPurification_le` read in the coordinates
  `threeSplit T E`, with the relative entropy of the source identified with the regional mutual
  information `FiniteProduct.mutualInformation`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.4 `lem:splitting`,
  `05-frames.tex`, lines 352–394.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator ComplexOrder
open TNLean.Lattice (sheetSplit)

noncomputable section

namespace TNLean.Lattice.Sheet

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-! ### Coordinates and operators -/

section Transport

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- The defect `‖(M - 1) ψ‖` of an operator does not depend on the coordinates. -/
theorem norm_act_submatrix_sub (M : Matrix n n ℂ) (e : m ≃ n) (ψ : EuclideanSpace ℂ m) :
    ‖act (M.submatrix e e) ψ - ψ‖ =
      ‖act M (WithLp.toLp 2 (ψ ∘ e.symm)) - WithLp.toLp 2 (ψ ∘ e.symm)‖ := by
  have h : act (M.submatrix e e) ψ - ψ =
      WithLp.toLp 2 ((M *ᵥ (ψ ∘ e.symm) - ψ ∘ e.symm) ∘ e) := by
    ext x
    simp [act_apply, submatrix_mulVec_equiv]
  rw [h, EuclideanSpace.norm_toLp_comp_equiv]
  rfl

end Transport

/-- The operator `1 ⊗ B`, acting as `B` on the second factor and as the identity on the tags,
passes through a tagged stack `∑_t |t⟩ ⊗ S_t` whenever `B` commutes with every `S_t`. -/
theorem one_kronecker_mul_stack {τ n : Type*} [Fintype τ] [DecidableEq τ] [Fintype n]
    {S : τ → Matrix n n ℂ} {B : Matrix n n ℂ} (hB : ∀ t, Commute B (S t)) :
    ((1 : Matrix τ τ ℂ) ⊗ₖ B) * stack S = stack S * B := by
  rw [stack_mul]
  ext ⟨t, x⟩ y
  simp only [mul_apply, kroneckerMap_apply, one_apply, stack_apply, Fintype.sum_prod_type,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single t (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  have h := congrFun (congrFun (hB t).eq x) y
  simp only [mul_apply] at h
  simpa using h

/-! ### Three regions -/

/-- The raw configurations of a sheet as triples `((t, e), u)` of configurations on `T`, on `E`
and on `U = (T ∪ E)ᶜ`, for disjoint `T` and `E`. -/
def threeSplit (q : ℕ) (T E : Finset ι) (h : Disjoint T E) :
    (ι → Fin q) ≃ ((T → Fin q) × (E → Fin q)) × (↥(T ∪ E)ᶜ → Fin q) :=
  (sheetSplit q (T ∪ E)).trans
    ((FiniteProduct.unionEquiv (fun _ : ι => Fin q) T E h).prodCongr (Equiv.refl _))

section ThreeSplit

variable {T E : Finset ι} (h : Disjoint T E)

@[simp]
theorem threeSplit_apply_fst_fst (x : ι → Fin q) (v : T) : (threeSplit q T E h x).1.1 v = x v :=
  rfl

@[simp]
theorem threeSplit_apply_fst_snd (x : ι → Fin q) (v : E) : (threeSplit q T E h x).1.2 v = x v :=
  rfl

@[simp]
theorem threeSplit_apply_snd (x : ι → Fin q) (v : ↥(T ∪ E)ᶜ) :
    (threeSplit q T E h x).2 v = x v :=
  rfl

theorem threeSplit_symm_apply_of_mem_left (t : T → Fin q) (e : E → Fin q)
    (u : ↥(T ∪ E)ᶜ → Fin q) {v : ι} (hv : v ∈ T) :
    (threeSplit q T E h).symm ((t, e), u) v = t ⟨v, hv⟩ := by
  simp [threeSplit, FiniteProduct.splitEquiv_symm_apply_of_mem _ _ _ _ _
    (Finset.mem_union_left E hv), FiniteProduct.unionEquiv, hv]

theorem threeSplit_symm_apply_of_mem_right (t : T → Fin q) (e : E → Fin q)
    (u : ↥(T ∪ E)ᶜ → Fin q) {v : ι} (hv : v ∈ E) :
    (threeSplit q T E h).symm ((t, e), u) v = e ⟨v, hv⟩ := by
  have hvT : v ∉ T := fun hvT => Finset.disjoint_left.mp h hvT hv
  simp [threeSplit, FiniteProduct.splitEquiv_symm_apply_of_mem _ _ _ _ _
    (Finset.mem_union_right T hv), FiniteProduct.unionEquiv, hvT]

theorem threeSplit_symm_apply_of_notMem (t : T → Fin q) (e : E → Fin q)
    (u : ↥(T ∪ E)ᶜ → Fin q) {v : ι} (hv : v ∉ T ∪ E) :
    (threeSplit q T E h).symm ((t, e), u) v = u ⟨v, Finset.mem_compl.mpr hv⟩ := by
  simp [threeSplit, FiniteProduct.splitEquiv_symm_apply_of_notMem _ _ _ _ _ hv]

/-- A product operator in the coordinates of `threeSplit T E` is the Kronecker product of its
restrictions to `T`, to `E` and to `(T ∪ E)ᶜ`. -/
theorem rectKronecker_submatrix_threeSplit (m : ι → Matrix (Fin q) (Fin q) ℂ) :
    (rectKronecker m).submatrix (threeSplit q T E h).symm (threeSplit q T E h).symm =
      (rectKronecker (fun v : T => m v) ⊗ₖ rectKronecker (fun v : E => m v)) ⊗ₖ
        rectKronecker (fun v : ↥(T ∪ E)ᶜ => m v) := by
  ext ⟨⟨t, e⟩, u⟩ ⟨⟨t', e'⟩, u'⟩
  simp only [submatrix_apply, rectKronecker_apply, kroneckerMap_apply]
  rw [← Finset.prod_mul_prod_compl (T ∪ E), Finset.prod_union (M := ℂ) h, ← Finset.prod_coe_sort T,
    ← Finset.prod_coe_sort E, ← Finset.prod_coe_sort (T ∪ E)ᶜ]
  congr 1
  · congr 1
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [threeSplit_symm_apply_of_mem_left h _ _ _ v.2,
        threeSplit_symm_apply_of_mem_left h _ _ _ v.2]
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [threeSplit_symm_apply_of_mem_right h _ _ _ v.2,
        threeSplit_symm_apply_of_mem_right h _ _ _ v.2]
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [threeSplit_symm_apply_of_notMem h _ _ _ (Finset.mem_compl.mp v.2),
      threeSplit_symm_apply_of_notMem h _ _ _ (Finset.mem_compl.mp v.2)]

end ThreeSplit

/-! ### Product forms of supported operators -/

omit [DecidableEq ι] in
/-- If every product operator acting on `D` has the form `Φ A'` in the coordinates `e`, for a
linear map `Φ`, then so does every operator acting on `D`. -/
theorem exists_eq_of_mem_supportedOperators {κ M : Type*} [AddCommMonoid M] [Module ℂ M]
    {D : Set ι} (e : (ι → Fin q) ≃ κ) (Φ : M →ₗ[ℂ] Matrix κ κ ℂ)
    (hgen : ∀ m : ι → Matrix (Fin q) (Fin q) ℂ, (∀ i ∉ D, m i = 1) →
      ∃ A', (rectKronecker m).submatrix e.symm e.symm = Φ A')
    {A : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hA : A ∈ supportedOperators q D) :
    ∃ A', A.submatrix e.symm e.symm = Φ A' := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact hgen m hm
  | zero => exact ⟨0, by rw [map_zero]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    exact ⟨X + Y, by rw [map_add, ← hX, ← hY]; rfl⟩
  | smul c x _ hx =>
    obtain ⟨X, hX⟩ := hx
    exact ⟨c • X, by rw [map_smul, ← hX]; rfl⟩

/-- An operator acting on `T ∪ E` is `A' ⊗ 1_U` in the coordinates of `threeSplit T E`. -/
theorem exists_threeSplit_eq_kronecker_one {T E : Finset ι} (h : Disjoint T E)
    {A : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hA : A ∈ supportedOperators q (↑(T ∪ E) : Set ι)) :
    ∃ A' : Matrix ((T → Fin q) × (E → Fin q)) ((T → Fin q) × (E → Fin q)) ℂ,
      A.submatrix (threeSplit q T E h).symm (threeSplit q T E h).symm =
        A' ⊗ₖ (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) := by
  refine exists_eq_of_mem_supportedOperators (threeSplit q T E h)
    ((kroneckerBilinear (R := ℂ)).flip (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ))
    (fun m hm => ?_) hA
  refine ⟨rectKronecker (fun v : T => m v) ⊗ₖ rectKronecker (fun v : E => m v), ?_⟩
  rw [rectKronecker_submatrix_threeSplit h]
  change _ = _ ⊗ₖ (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ)
  congr 1
  rw [← rectKronecker_one (ν := ↥(T ∪ E)ᶜ) (ι := Fin q)]
  congr 1
  funext v
  exact hm v (Finset.mem_compl.mp v.2)

/-- An operator acting on a subset of `E` is `(1_T ⊗ A') ⊗ 1_U` in the coordinates of
`threeSplit T E`. -/
theorem exists_threeSplit_eq_one_kronecker_kronecker_one {T E : Finset ι} (h : Disjoint T E)
    {D : Set ι} (hD : D ⊆ E) {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ supportedOperators q D) :
    ∃ A' : Matrix (E → Fin q) (E → Fin q) ℂ,
      A.submatrix (threeSplit q T E h).symm (threeSplit q T E h).symm =
        ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ A') ⊗ₖ
          (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) := by
  refine exists_eq_of_mem_supportedOperators (threeSplit q T E h)
    (((kroneckerBilinear (R := ℂ)).flip
      (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ)).comp
      (kroneckerBilinear (R := ℂ) (1 : Matrix (T → Fin q) (T → Fin q) ℂ)))
    (fun m hm => ?_) hA
  have hT : ∀ v : T, m v = 1 := fun v =>
    hm v fun hv => Finset.disjoint_left.mp h v.2 (hD hv)
  have hU : ∀ v : ↥(T ∪ E)ᶜ, m v = 1 := fun v =>
    hm v fun hv => (Finset.mem_compl.mp v.2) (Finset.mem_union_right T (hD hv))
  refine ⟨rectKronecker (fun v : E => m v), ?_⟩
  rw [rectKronecker_submatrix_threeSplit h]
  change _ = ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ _) ⊗ₖ
    (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ)
  simp only [hT, hU, rectKronecker_one]

/-- An operator supported disjointly from T is `1_T ⊗ V` in the existing
three-region coordinates. Empty regions and zero local dimension are included.

Supporting tensor-partition algebra for AKLV, arXiv:1301.1162v1,
Lemma 4.2 (`l:agsp`), lines 646–654, and ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821, and `prop:Cheby-AGSP-eff`, lines 1324–1332. -/
theorem exists_threeSplit_eq_reindex_one_kronecker
    {T E : Finset ι} (h : Disjoint T E) {D : Set ι}
    (hD : Disjoint D (T : Set ι))
    {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ supportedOperators q D) :
    ∃ V : Matrix ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
        ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ,
      A.submatrix (threeSplit q T E h).symm (threeSplit q T E h).symm =
        ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ V).reindex
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            (↥(T ∪ E)ᶜ → Fin q)).symm
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            (↥(T ∪ E)ᶜ → Fin q)).symm := by
  obtain ⟨B, hB⟩ :=
    TNLean.Lattice.exists_one_kronecker_of_mem_supportedOperators
      (q := q) (S := T) hD hA
  let c := FiniteProduct.complementUnionEquiv (fun _ : ι ↦ Fin q) T E h
  refine ⟨B.submatrix c.symm c.symm, ?_⟩
  ext ⟨⟨t, e⟩, u⟩ ⟨⟨t', e'⟩, u'⟩
  change A
      ((FiniteProduct.splitEquiv (fun _ : ι ↦ Fin q) (T ∪ E)).symm
        ((FiniteProduct.unionEquiv (fun _ : ι ↦ Fin q) T E h).symm (t, e), u))
      ((FiniteProduct.splitEquiv (fun _ : ι ↦ Fin q) (T ∪ E)).symm
        ((FiniteProduct.unionEquiv (fun _ : ι ↦ Fin q) T E h).symm (t', e'), u')) =
    (1 : Matrix (T → Fin q) (T → Fin q) ℂ) t t' *
      B (c.symm (e, u)) (c.symm (e', u'))
  rw [FiniteProduct.split_union_symm (fun _ : ι ↦ Fin q) T E h t e u,
    FiniteProduct.split_union_symm (fun _ : ι ↦ Fin q) T E h t' e' u']
  exact congrFun
    (congrFun hB (t, c.symm (e, u))) (t', c.symm (e', u'))

/-! ### The splitting consequence on a sheet -/

section Splitting

variable {T E : Finset ι} (h : Disjoint T E)

/-- A vector on the sheet in the coordinates of `threeSplit T E`. -/
abbrev splitVec (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    ((T → Fin q) × (E → Fin q)) × (↥(T ∪ E)ᶜ → Fin q) → ℂ :=
  fun w => Ω ((threeSplit q T E h).symm w)

theorem star_splitVec_dotProduct_splitVec {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) :
    star (splitVec h Ω) ⬝ᵥ splitVec h Ω = 1 := by
  rw [← star_dotProduct_self_of_norm_eq_one hΩ]
  exact (threeSplit q T E h).symm.sum_comp fun x => star (Ω x) * Ω x

/-- The reduced state of `Ω` on `T ∪ E`, in the coordinates `(t, e)`, is the reduced state of the
coordinate vector `splitVec Ω`. -/
theorem partialTraceRight_splitVec (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    partialTraceRight (vecMulVec (splitVec h Ω) (star (splitVec h Ω))) =
      (FiniteProduct.reducedPure (fun _ : ι => Fin q) Ω (T ∪ E)).submatrix
        (FiniteProduct.unionEquiv (fun _ : ι => Fin q) T E h).symm
        (FiniteProduct.unionEquiv (fun _ : ι => Fin q) T E h).symm := by
  ext a b
  rfl

/-- The relative entropy of the reduced state on `T ∪ E` with respect to the product of its
marginals is the regional mutual information `I_Ω(T:E)` (Lemma 2.2 `lem:fidelity`,
`01-preliminaries.tex`, lines 92–139). -/
theorem quantumRelativeEntropy_splitVec_eq_mutualInformation (Ω : EuclideanSpace ℂ (ι → Fin q))
    {ρ : Matrix ((T → Fin q) × (E → Fin q)) ((T → Fin q) × (E → Fin q)) ℂ}
    (hρ : partialTraceRight (vecMulVec (splitVec h Ω) (star (splitVec h Ω))) = ρ) :
    quantumRelativeEntropy ρ (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) =
      FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T E := by
  have hpsd : ρ.PosSemidef := hρ ▸ (posSemidef_vecMulVec_self_star _).partialTraceRight
  have hρeq := hρ.symm.trans (partialTraceRight_splitVec h Ω)
  have hR : partialTraceRight ρ = FiniteProduct.reducedPure (fun _ : ι => Fin q) Ω T := by
    rw [hρeq]
    exact FiniteProduct.partialTraceRight_reducedMatrix_union _ _ T E h
  have hL : partialTraceLeft ρ = FiniteProduct.reducedPure (fun _ : ι => Fin q) Ω E := by
    rw [hρeq]
    exact FiniteProduct.partialTraceLeft_reducedMatrix_union _ _ T E h
  rw [quantumRelativeEntropy_product_marginals hpsd,
    vonNeumannEntropy_congr hR _ (FiniteProduct.reducedPure_posSemidef _ Ω T).isHermitian,
    vonNeumannEntropy_congr hL _ (FiniteProduct.reducedPure_posSemidef _ Ω E).isHermitian,
    vonNeumannEntropy_congr hρeq _ ((isHermitian_submatrix_equiv _).mpr
      (FiniteProduct.reducedPure_posSemidef _ Ω (T ∪ E)).isHermitian),
    vonNeumannEntropy_submatrix_equiv _ _
      (FiniteProduct.reducedPure_posSemidef _ Ω (T ∪ E)).isHermitian]
  rfl

/-- **Splitting data** for a pair of disjoint sets of sites `T`, `E` with `U = (T ∪ E)ᶜ`
(Lemma 6.4 `lem:splitting`): an isometry `V` from the configurations of `U` to `B_T × B_E`, where
`B_T` is the configuration space of `T` and `B_E` that of `E` or `U`, and unit vectors `s` on
`T × B_T` and `s'` on `E × B_E`.

Polynomial-PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex`, lines 352–365. -/
structure SplittingData (q : ℕ) (T E : Finset ι) where
  /-- The isometry `V : H_U → B_T ⊗ B_E`. -/
  V : Matrix ((T → Fin q) × ((E → Fin q) ⊕ (↥(T ∪ E)ᶜ → Fin q))) (↥(T ∪ E)ᶜ → Fin q) ℂ
  /-- The unit vector `s` on `T × B_T`. -/
  s : (T → Fin q) × (T → Fin q) → ℂ
  /-- The unit vector `s'` on `E × B_E`. -/
  s' : (E → Fin q) × ((E → Fin q) ⊕ (↥(T ∪ E)ᶜ → Fin q)) → ℂ
  /-- `V` is an isometry. -/
  isIsometry : V.IsIsometry
  /-- `s` is a unit vector. -/
  star_s : star s ⬝ᵥ s = 1
  /-- `s'` is a unit vector. -/
  star_s' : star s' ⬝ᵥ s' = 1

/-- The splitting error `‖(1_{TE} ⊗ V) Ω - s ⊗ s'‖` of splitting data on a vector of the sheet. -/
def SplittingData.error (σ : SplittingData q T E) (Ω : EuclideanSpace ℂ (ι → Fin q)) : ℝ :=
  ‖(WithLp.toLp 2 ((((1 : Matrix ((T → Fin q) × (E → Fin q))
      ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ σ.V) *ᵥ splitVec h Ω) -
      tensorPurification σ.s σ.s') : EuclideanSpace ℂ _)‖

/-- **Splitting consequence on a sheet** (Lemma 6.4 `lem:splitting`). Let `T`, `E` be disjoint
sets of sites, `U = (T ∪ E)ᶜ`, and `b = I_Ω(T:E)` for a unit vector `Ω` on the sheet. There are
splitting data with `‖(1_{TE} ⊗ V) Ω - s ⊗ s'‖ ≤ √(2(1 - e^{-b/2})) ≤ √b`. No bound on the
dimensions is imposed.

Polynomial-PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex`, lines 352–368. -/
theorem exists_sheetSplitting {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) :
    ∃ σ : SplittingData q T E,
      σ.error h Ω ≤
        √(2 * (1 - Real.exp (-(FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T E
          / 2)))) ∧
      √(2 * (1 - Real.exp (-(FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T E
          / 2)))) ≤ √(FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T E) := by
  obtain ⟨V, s, s', hV, hs, hs', hnorm⟩ :=
    exists_isIsometry_norm_sub_tensorPurification_le (splitVec h Ω)
      (star_splitVec_dotProduct_splitVec h hΩ) rfl
  refine ⟨⟨V, s, s', hV, hs, hs'⟩, ?_, Real.sqrt_two_mul_one_sub_exp_neg_half_le_sqrt _⟩
  rw [← quantumRelativeEntropy_splitVec_eq_mutualInformation h Ω rfl]
  exact hnorm

/-- **Splitting at a polynomially small mutual information** (Lemma 6.4 `lem:splitting`, last
sentence). If `I_Ω(T:E) ≤ L^{-60}`, the splitting error is at most `L^{-30}`.

Polynomial-PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex`, lines 366–367. -/
theorem exists_sheetSplitting_zpow {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T E ≤ L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T E, σ.error h Ω ≤ L ^ (-30 : ℤ) := by
  obtain ⟨σ, h₁, h₂⟩ := exists_sheetSplitting h hΩ
  refine ⟨σ, h₁.trans (h₂.trans ?_)⟩
  have hsq : L ^ (-60 : ℤ) = (L ^ (-30 : ℤ)) ^ 2 := by
    rw [← zpow_natCast, ← _root_.zpow_mul]; norm_num
  rw [← Real.sqrt_sq (Even.zpow_nonneg ⟨-15, by norm_num⟩ L), ← hsq]
  exact Real.sqrt_le_sqrt hI

/-- **Splitting at a polynomially small mutual information, any exponent** (Lemma 6.4
`lem:splitting`, last sentence, and the splitting step of Lemmas `lem:birth` and `lem:exchange` of
the one-dimensional note, `part2b_mps_protocol.tex`, lines 70–158). For `0 ≤ L` and any real
exponent `p`, if `I_Ω(T:E) ≤ L^{-2p}`, the splitting error is at most `L^{-p}`.

Polynomial-PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex`, lines 366–367, there
with `p = 30`. -/
theorem exists_sheetSplitting_rpow {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L p : ℝ} (hL : 0 ≤ L)
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T E ≤ L ^ (-(2 * p))) :
    ∃ σ : SplittingData q T E, σ.error h Ω ≤ L ^ (-p) := by
  obtain ⟨σ, h₁, h₂⟩ := exists_sheetSplitting h hΩ
  refine ⟨σ, h₁.trans (h₂.trans ?_)⟩
  have hsq : L ^ (-(2 * p)) = (L ^ (-p)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
    congr 1
    push_cast
    ring
  rw [← Real.sqrt_sq (Real.rpow_nonneg hL _), ← hsq]
  exact Real.sqrt_le_sqrt hI

end Splitting

end TNLean.Lattice.Sheet
