/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularOpenRegion
import TNLean.Algebra.FinSumPermutation
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Local expansion of the Gram operator of a contracted region

The Gram matrix of the actual open-region map is obtained by contracting two
copies of the virtual labels, conjugating the first copy. The physical sum
factors into one site Gram kernel per region vertex. Boundary labels remain
fixed in both copies; labels on exterior edges do not occur.

This is the finite contraction underlying Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, proof of Theorem 6.9 (`Papers/1001.3807/paper_v3.tex`,
lines 1935–1957 and 2062–2072). The expansion is valid for arbitrary local
tensors and contains no assumption about the Gram operator of the region.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- The local physical pairing of two virtual configurations at one vertex.
Source: SCP10, local isometric contraction in the proof of Theorem 6.9,
lines 2062–2072. -/
noncomputable def tensorSiteGram (A : Tensor Γ d) (v : V)
    (η θ : (e : IncidentEdge Γ v) → Fin (A.bondDim e.1)) : ℂ :=
  ∑ s : Fin d, star (A.component v η s) * A.component v θ s

omit [Fintype V] in
/-- Summing the physical configurations factors the pairing of the region vertex
products into their individual site Gram kernels. -/
theorem sum_star_regionIncidentWeight_mul
    (A : Tensor Γ d) (R : Finset V) (η θ : RegionIncidentConfig A R) :
    (∑ σ : RegionPhysicalConfig (d := d) R,
      star (regionIncidentWeight A R η σ) * regionIncidentWeight A R θ σ) =
      ∏ w : {w : V // w ∈ R}, tensorSiteGram A w.1
        (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩)
        (fun e => θ ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩) := by
  classical
  simp only [regionIncidentWeight, star_prod, ← Finset.prod_mul_distrib, tensorSiteGram]
  exact (Fintype.prod_sum (fun (w : {w : V // w ∈ R}) (s : Fin d) =>
    star (A.component w.1
      (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩) s) *
    A.component w.1 (fun e => θ ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩) s)).symm

/-- Source: SCP10, proof of Theorem 6.9, lines 1935–1957 and 2062–2072.
The Gram matrix of the actual open-region map is the double contraction of its
incident bond labels, with each physical sum replaced by a site Gram kernel. -/
theorem openRegionCoefficientMatrix_gram_apply
    (A : Tensor Γ d) (R : Finset V) (μ ν : RegionBoundaryConfig A R) :
    ((openRegionCoefficientMatrix A R).conjTranspose *
        openRegionCoefficientMatrix A R) μ ν =
      ∑ η : RegionIncidentConfig A R, ∑ θ : RegionIncidentConfig A R,
        if regionIncidentBoundaryLabel A R η = μ ∧
            regionIncidentBoundaryLabel A R θ = ν then
          ∏ w : {w : V // w ∈ R}, tensorSiteGram A w.1
            (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩)
            (fun e => θ ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩)
        else 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    openRegionCoefficientMatrix, openRegionWeight, star_sum,
    Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_reverse_three]
  apply Finset.sum_congr₂
  intro η _ θ _
  by_cases hη : regionIncidentBoundaryLabel A R η = μ <;>
    by_cases hθ : regionIncidentBoundaryLabel A R θ = ν <;>
    simp only [hη, hθ, true_and, false_and, and_false, ite_true, ite_false,
      star_zero, mul_zero, zero_mul, Finset.sum_const_zero]
  exact sum_star_regionIncidentWeight_mul A R η θ

/-- Source: SCP10, proof of Theorem 6.9, lines 1935–1957 and 2062–2072.
The same local Gram expansion in the ordered regular group coordinates of the
actual open-region matrix. The crossing-bond enumeration changes only the two
fixed boundary configurations. -/
theorem regularOpenRegionMatrix_gram_apply
    {G : Type*} [Group G] [Fintype G]
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b)
    (x y : Fin b → G) :
    ((regularOpenRegionMatrix a R e).conjTranspose * regularOpenRegionMatrix a R e) x y =
      ∑ η : RegionIncidentConfig (groupBondTensor a) R,
        ∑ θ : RegionIncidentConfig (groupBondTensor a) R,
          if regionIncidentBoundaryLabel (groupBondTensor a) R η =
                regularRegionBoundaryConfigEquiv a R e x ∧
              regionIncidentBoundaryLabel (groupBondTensor a) R θ =
                regularRegionBoundaryConfigEquiv a R e y then
            ∏ w : {w : V // w ∈ R}, tensorSiteGram (groupBondTensor a) w.1
              (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩)
              (fun f => θ ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩)
          else 0 := by
  classical
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, regularOpenRegionMatrix,
    openRegionCoefficientMatrix] using
    openRegionCoefficientMatrix_gram_apply (groupBondTensor a) R
      (regularRegionBoundaryConfigEquiv a R e x) (regularRegionBoundaryConfigEquiv a R e y)

/-- Group coordinates for the configurations of the edges touching a region. -/
noncomputable def regularRegionIncidentConfigEquiv
    {G : Type*} [Group G] [Fintype G]
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V) :
    ({f : Edge Γ // IsRegionIncidentEdge R f} → G) ≃
      RegionIncidentConfig (groupBondTensor a) R :=
  Equiv.piCongrRight fun _ => Fintype.equivFin G

omit [Fintype V] in
/-- Decoding the fixed boundary in an incident configuration gives its group restriction. -/
theorem regionIncidentBoundaryLabel_regular_iff
    {G : Type*} [Group G] [Fintype G]
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    {b : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b)
    (η : {f : Edge Γ // IsRegionIncidentEdge R f} → G) (x : Fin b → G) :
    regionIncidentBoundaryLabel (groupBondTensor a) R
        (regularRegionIncidentConfigEquiv a R η) = regularRegionBoundaryConfigEquiv a R e x ↔
      (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
        η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = fun f => x (e f) := by
  constructor
  · intro h
    funext f
    exact (Fintype.equivFin G).injective (congrFun h f)
  · intro h
    funext f
    exact congrArg (Fintype.equivFin G) (congrFun h f)

open scoped Classical in
/-- Source: SCP10, proof of Theorem 6.9, lines 1935–1957 and 2062–2072.
The actual regular-region Gram matrix is a double sum of group-valued bond
configurations with fixed crossing labels and the original local tensor pairings. -/
theorem regularOpenRegionMatrix_gram_apply_group
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) (x y : Fin b → G) :
    ((regularOpenRegionMatrix a R e).conjTranspose * regularOpenRegionMatrix a R e) x y =
      ∑ η : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
        ∑ θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
          if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => x (e f)) ∧
              (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                θ ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => y (e f)) then
            ∏ w : {w : V // w ∈ R}, ∑ s : Fin d,
              star (a w.1
                (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩) s) *
              a w.1 (fun f => θ ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩) s
          else 0 := by
  classical
  rw [regularOpenRegionMatrix_gram_apply,
    ← Equiv.sum_comp (regularRegionIncidentConfigEquiv a R)]
  apply Finset.sum_congr rfl
  intro η _
  rw [← Equiv.sum_comp (regularRegionIncidentConfigEquiv a R)]
  apply Finset.sum_congr rfl
  intro θ _
  simp only [regionIncidentBoundaryLabel_regular_iff]
  simp only [tensorSiteGram, groupBondTensor, regularRegionIncidentConfigEquiv,
    Equiv.piCongrRight_apply, Pi.map_apply, Equiv.symm_apply_apply]

end TNLean.PEPS



