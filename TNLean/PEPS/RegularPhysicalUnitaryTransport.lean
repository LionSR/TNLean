/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularProjectorOpenRegion
import QICLean.Algebra.MatrixGramUnitary

/-!
# Transport of supported canonical unitaries to the original physical region

The product of the original local physical maps has Gram matrix equal to a
positive scalar times the product of the local regular averaging projectors.
A canonical unitary commuting with this product projector can therefore be
implemented by a unitary on the original physical region. The action on unused
physical directions is supplied by the finite-dimensional isometry extension
theorem; no surjectivity of the local maps is required.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Lemma 6.3 and
Observation `obs:iso:accessible-virt`, local source lines 1729–1820.
This is an auxiliary form of physical accessibility for product local maps.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {κ : V → Type*} [∀ v, Fintype (κ v)] [∀ v, DecidableEq (κ v)]

omit [∀ v, DecidableEq (κ v)] in
/-- The Gram matrix of the product physical map is a positive multiple of the
product of the local regular invariant projectors. No block Gram assumption is
supplied. Source: SCP10, Definition 6.1 and accessible virtual coordinates,
lines 1692–1700 and 1765–1820. -/
theorem exists_positive_regionPhysicalProductMatrix_gram
    (a : (v : V) → (IncidentEdge Γ v → G) → κ v → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V) :
    ∃ c : ℝ, 0 < c ∧
      (regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s)).conjTranspose *
          regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s) =
        (c : ℂ) • regionPhysicalProductMatrix R
          (fun v => regularLegProjector (G := G) (IncidentEdge Γ v)) := by
  classical
  choose c hc h using fun v => (ha v).exists_regularSiteGram
  have hlocal (v : V) :
      (Matrix.of fun s α => a v α s).conjTranspose *
        (Matrix.of fun s α => a v α s) =
      (c v : ℂ) • regularLegProjector (IncidentEdge Γ v) := by
    ext α β
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, regularLegProjector_apply, div_eq_mul_inv,
      mul_assoc] using h v α β
  refine ⟨∏ v : {v // v ∈ R}, c v.1, Finset.prod_pos (fun v _ => hc v.1), ?_⟩
  rw [regionPhysicalProductMatrix_conjTranspose, regionPhysicalProductMatrix_mul]
  simp_rw [hlocal]
  ext α β
  simp only [regionPhysicalProductMatrix, Matrix.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Complex.ofReal_prod]

/-- A unitary commuting with the product of the canonical local invariant
projectors has a unitary implementation on the original physical region.
The product Gram identity is derived from the local isometry assumptions.
Source: SCP10, Lemma 6.3 and accessible virtual coordinates, lines 1729–1820. -/
theorem exists_unitary_regionPhysicalProductMatrix_mul_of_projector_commute
    (a : (v : V) → (IncidentEdge Γ v → G) → κ v → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (U : Matrix (RegionHalfEdgeConfig (Γ := Γ) G R)
      (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ)
    (hcomm : U * regionPhysicalProductMatrix R
        (fun v => regularLegProjector (IncidentEdge Γ v)) =
      regionPhysicalProductMatrix R
        (fun v => regularLegProjector (IncidentEdge Γ v)) * U) :
    ∃ W : Matrix ((v : {v // v ∈ R}) → κ v.1) ((v : {v // v ∈ R}) → κ v.1) ℂ,
      W ∈ Matrix.unitaryGroup ((v : {v // v ∈ R}) → κ v.1) ℂ ∧
      W * regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s) =
        regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s) * U := by
  classical
  obtain ⟨c, _, hGram⟩ := exists_positive_regionPhysicalProductMatrix_gram a ha R
  let T := regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s)
  let P := regionPhysicalProductMatrix R
    (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))
  change T.conjTranspose * T = (c : ℂ) • P at hGram
  have hunit : U.conjTranspose * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hU)
  have heq : (T * U).conjTranspose * (T * U) = T.conjTranspose * T := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T.conjTranspose T U, hGram]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    rw [← hcomm, ← Matrix.mul_assoc, hunit, Matrix.one_mul]
  obtain ⟨W, hW⟩ := Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq (T * U) T heq
  exact ⟨W, W.2, hW.symm⟩

end TNLean.PEPS
