/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionGram

/-!
# Regular-bond operators in an actual open-region contraction

An edge is oriented from its smaller endpoint to its larger endpoint. Inserting
left multiplication by a group element on that bond changes the label at the
larger endpoint and leaves the label at the smaller endpoint unchanged. Applying
this change to the site coefficients gives an ordinary `groupBondTensor`; its
open-region map is the existing contraction over internal bonds.

The cross-Gram expansion below uses the original local Gram kernels, evaluated
on these changed labels. It is an auxiliary calculation for the twisted-region
argument of Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
`eq:2d:peps-with-ug-uh` and proof of Theorem 6.9, lines 1935–1990 and 2062–2072.
No entropy or parent-Hamiltonian assertion is made here.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Source: SCP10, bond operators in `eq:2d:peps-with-ug-uh`.
The head label of an oriented regular bond is its group operator times its tail label. -/
def regularTwistedLabels (u : Edge Γ → G) (v : V) (η : IncidentEdge Γ v → G) :
    IncidentEdge Γ v → G :=
  fun f => if v = f.1.1.2 then u f.1 * η f else η f

/-- The original site coefficient with regular-bond operators inserted at the
larger endpoints. Source: SCP10, `eq:2d:peps-with-ug-uh`. -/
def regularTwistedSite
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (u : Edge Γ → G)
    (v : V) (η : IncidentEdge Γ v → G) (s : Fin d) : ℂ :=
  a v (regularTwistedLabels u v η) s

/-- The actual open-region contraction with inserted regular-bond operators.
It is the existing region matrix of the transformed `groupBondTensor`.
Source: SCP10, twisted-region contraction, lines 1935–1990. -/
noncomputable abbrev regularTwistedOpenRegionMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (u : Edge Γ → G)
    (R : Finset V) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :=
  regularOpenRegionMatrix (regularTwistedSite a u) R e

/-- The local translation equations after the two bond operators are inserted.
Source: SCP10, twisted-sector contraction, lines 1935–1990. -/
def IsTwistedRegionLabelCompatible (R : Finset V) (u w : Edge Γ → G)
    (q : {v : V // v ∈ R} → G)
    (η θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G) : Prop :=
  ∀ (v : {v : V // v ∈ R}),
    regularTwistedLabels u v.1
        (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) =
      fun f => q v * regularTwistedLabels w v.1
        (fun f => θ ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) f

instance (R : Finset V) (u w : Edge Γ → G) (q : {v : V // v ∈ R} → G)
    (η θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G) :
    Decidable (IsTwistedRegionLabelCompatible R u w q η θ) :=
  inferInstanceAs (Decidable (∀ (v : {v : V // v ∈ R}),
    regularTwistedLabels u v.1
        (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) =
      fun f => q v * regularTwistedLabels w v.1
        (fun f => θ ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) f))

open scoped Classical in
/-- The actual regular-region coefficient, with only incident group labels summed.
Source: SCP10, region contraction in the proof of Theorem 6.9, lines 1935–1957. -/
theorem regularOpenRegionMatrix_apply_group
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b)
    (σ : RegionPhysicalConfig (d := d) R) (x : Fin b → G) :
    regularOpenRegionMatrix a R e σ x =
      ∑ η : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
        if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
            η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => x (e f)) then
          ∏ v : {v : V // v ∈ R},
            a v.1 (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) (σ v)
        else 0 := by
  classical
  unfold regularOpenRegionMatrix openRegionWeight
  rw [← Equiv.sum_comp (regularRegionIncidentConfigEquiv a R)]
  apply Finset.sum_congr rfl
  intro η _
  simp only [regionIncidentBoundaryLabel_regular_iff]
  simp only [regionIncidentWeight, groupBondTensor, regularRegionIncidentConfigEquiv,
    Equiv.piCongrRight_apply, Pi.map_apply, Equiv.symm_apply_apply]

open scoped Classical in
/-- Cross pairing of two actual regular-region maps, factored into the original
site pairings. Source: SCP10, proof of Theorem 6.9, lines 1935–1990 and 2062–2072. -/
theorem regularOpenRegionMatrix_crossGram_apply_group
    (a a' : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) (x y : Fin b → G) :
    ((regularOpenRegionMatrix a R e).conjTranspose * regularOpenRegionMatrix a' R e) x y =
      ∑ η : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
        ∑ θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
          if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => x (e f)) ∧
              (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                θ ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => y (e f)) then
            ∏ v : {v : V // v ∈ R}, ∑ s : Fin d,
              star (a v.1
                (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) s) *
              a' v.1 (fun f => θ ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) s
          else 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    regularOpenRegionMatrix_apply_group, star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_reverse_three]
  apply Finset.sum_congr₂
  intro η _ θ _
  by_cases hη : (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
    η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => x (e f)) <;>
    by_cases hθ : (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
      θ ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => y (e f)) <;>
    simp only [hη, hθ, true_and, false_and, and_false, ite_true, ite_false,
      star_zero, mul_zero, zero_mul, Finset.sum_const_zero]
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (v : {v : V // v ∈ R}) (s : Fin d) =>
    star (a v.1 (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) s) *
      a' v.1 (fun f => θ ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) s)).symm

open scoped Classical in
/-- Expanding the original local group-average kernels after bond insertion
retains their exact normalization. Source: SCP10, lines 1935–1990 and 2062–2072. -/
theorem prod_twistedSiteGram_eq_sum_compatible
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (c : V → ℂ)
    (R : Finset V) (u w : Edge Γ → G)
    (hlocal : ∀ (v : {v : V // v ∈ R}) (η θ : IncidentEdge Γ v.1 → G),
      (∑ s : Fin d, star (a v.1 η s) * a v.1 θ s) =
        (c v.1 / (Fintype.card G : ℂ)) *
          ∑ g : G, if η = (fun f => g * θ f) then (1 : ℂ) else 0)
    (η θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G) :
    (∏ v : {v : V // v ∈ R}, ∑ s : Fin d,
      star (regularTwistedSite a u v.1
        (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) s) *
      regularTwistedSite a w v.1
        (fun f => θ ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) s) =
      ((∏ v : {v : V // v ∈ R}, c v.1) / (Fintype.card G : ℂ) ^ R.card) *
        ∑ q : {v : V // v ∈ R} → G,
          if IsTwistedRegionLabelCompatible R u w q η θ then (1 : ℂ) else 0 := by
  classical
  simp only [regularTwistedSite, hlocal, Finset.prod_mul_distrib,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  congr 1
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Fintype.prod_boole, IsTwistedRegionLabelCompatible]
  rfl

open scoped Classical in
/-- The actual twisted-region cross-Gram matrix is a sum over compatible local
translations, with the two boundary configurations fixed. This derives the
matrix from the original site kernels; it assumes no region Gram identity.
Source: SCP10, proof of Theorem 6.9, lines 1935–1990 and 2062–2072. -/
theorem regularTwistedOpenRegionMatrix_crossGram_eq_sum_compatible
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (c : V → ℂ)
    (R : Finset V) (u w : Edge Γ → G) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b)
    (hlocal : ∀ (v : {v : V // v ∈ R}) (η θ : IncidentEdge Γ v.1 → G),
      (∑ s : Fin d, star (a v.1 η s) * a v.1 θ s) =
        (c v.1 / (Fintype.card G : ℂ)) *
          ∑ g : G, if η = (fun f => g * θ f) then (1 : ℂ) else 0)
    (x y : Fin b → G) :
    ((regularTwistedOpenRegionMatrix a u R e).conjTranspose *
        regularTwistedOpenRegionMatrix a w R e) x y =
      ∑ η : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
        ∑ θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
          if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => x (e f)) ∧
              (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                θ ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => y (e f)) then
            ((∏ v : {v : V // v ∈ R}, c v.1) / (Fintype.card G : ℂ) ^ R.card) *
              ∑ q : {v : V // v ∈ R} → G,
                if IsTwistedRegionLabelCompatible R u w q η θ then (1 : ℂ) else 0
          else 0 := by
  classical
  rw [regularOpenRegionMatrix_crossGram_apply_group]
  simp only [prod_twistedSiteGram_eq_sum_compatible a c R u w hlocal]

end TNLean.PEPS
