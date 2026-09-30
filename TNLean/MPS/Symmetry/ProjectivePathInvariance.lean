/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CocycleCohomology
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Field
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix

/-!
# Cohomology along a continuous virtual projective path

At a fixed positive virtual dimension, the factor system of a continuous
family of projective matrices cannot change cohomology class. The argument
lifts the determinant of each virtual matrix through the finite covering
`z ↦ z ^ D` of the nonzero complex numbers. After determinant-one
normalization, the factor system takes values among the `D`th roots of
unity and is therefore constant along the interval.

This is the virtual-path part of Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Section II.F.2. It does not assert that an arbitrary
physical Hamiltonian path produces such a continuous virtual family.
-/

namespace MPSTensor

open scoped Matrix

/-- A continuous family of `D`th roots of unity on the unit interval is
constant. This is the discreteness step in the virtual-path argument of
arXiv:1010.3732, Section II.F.2. -/
theorem continuous_rootOfUnity_path_const
    {D : ℕ} (hD : 0 < D) (f : unitInterval → ℂ)
    (hf : Continuous f) (hpow : ∀ t, f t ^ D = 1)
    (s t : unitInterval) : f s = f t := by
  have hfinite : ({z : ℂ | z ^ D = 1} : Set ℂ).Finite := by
    convert (Polynomial.nthRootsFinset D (1 : ℂ)).finite_toSet using 1
    ext z
    exact (Polynomial.mem_nthRootsFinset hD (1 : ℂ)).symm
  have hmaps : Set.MapsTo f Set.univ {z : ℂ | z ^ D = 1} :=
    fun t _ => hpow t
  exact isPreconnected_univ.constant_of_mapsTo hfinite.isDiscrete
    hf.continuousOn hmaps (Set.mem_univ s) (Set.mem_univ t)

/-- Every continuous nonvanishing complex path has a continuous `D`th root
when `D>0`. The proof uses the `D`th-power covering of the punctured plane.
This is the determinant-lifting step in arXiv:1010.3732, Section II.F.2. -/
theorem exists_continuous_pow_root_path
    {D : ℕ} (hD : 0 < D) (d : unitInterval → ℂ)
    (hdcont : Continuous d) (hdnz : ∀ t, d t ≠ 0) :
    ∃ β : unitInterval → ℂ,
      Continuous β ∧ (∀ t, β t ^ D = d t) ∧ ∀ t, β t ≠ 0 := by
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  let p : {z : ℂ // z ≠ 0} → {z : ℂ // z ≠ 0} :=
    fun z => ⟨z.1 ^ D, pow_ne_zero D z.2⟩
  have hcover : IsCoveringMap p := isCoveringMap_npow D hDc
  let dpath : C(unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun t => ⟨d t, hdnz t⟩, by fun_prop⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (d 0) hD
  have hznz : z ≠ 0 := by
    intro hz0
    exact hdnz 0 (by simpa [hz0, Nat.ne_of_gt hD] using hz.symm)
  let z₀ : {z : ℂ // z ≠ 0} := ⟨z, hznz⟩
  have hbase : p z₀ = dpath 0 := Subtype.ext hz
  let βpath := hcover.liftPath dpath z₀ hbase.symm
  refine ⟨fun t => (βpath t).1, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp βpath.continuous
  · intro t
    have hlift := congrArg Subtype.val
      (congrFun (hcover.liftPath_lifts dpath z₀ hbase.symm) t)
    exact hlift
  · intro t
    exact (βpath t).2

/-- A continuous family of unitary projective matrices has a continuous
factor at each pair of group elements. A nonempty virtual index extracts the
factor from the matrix equality. Source: arXiv:1010.3732, Section II.F.2,
virtual-path argument following the projective multiplication law. -/
theorem continuous_projectiveFactor_of_unitaryMatrixPath
    {G : Type*} [Group G] {D : ℕ} (hD : 0 < D)
    (V : unitInterval → G → Matrix (Fin D) (Fin D) ℂ)
    (ω : unitInterval → G → G → Units ℂ)
    (hV : ∀ g, Continuous fun t => V t g)
    (hunitary : ∀ t g, V t g ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hmul : ∀ t g h, V t g * V t h = (ω t g h : ℂ) • V t (g * h))
    (g h : G) : Continuous fun t => (ω t g h : ℂ) := by
  let i : Fin D := ⟨0, hD⟩
  have hformula (t : unitInterval) :
      (ω t g h : ℂ) = ((V t g * V t h) * (V t (g * h))ᴴ) i i := by
    rw [hmul t g h, Matrix.smul_mul]
    have hu : V t (g * h) * (V t (g * h))ᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using
        Matrix.mem_unitaryGroup_iff.mp (hunitary t (g * h))
    rw [hu]
    simp [Matrix.smul_apply]
  have hc : Continuous
      (fun t => ((V t g * V t h) * (V t (g * h))ᴴ) i i) :=
    (((hV g).matrix_mul (hV h)).matrix_mul
      ((hV (g * h)).matrix_conjTranspose)).matrix_elem i i
  exact hc.congr (fun t => (hformula t).symm)

/-- Endpoint factor systems are cohomologous when their `D`th powers are
the determinant coboundary of a continuous nonvanishing path. This is the
algebraic core of the fixed-dimension obstruction argument in
arXiv:1010.3732, Section II.F.2. -/
theorem projectiveFactor_endpoints_cohomologous_of_det_path
    {G : Type*} [Group G] {D : ℕ} (hD : 0 < D)
    (ω : unitInterval → TNLean.Algebra.ScalarCocycle G)
    (d : unitInterval → G → ℂ)
    (hωcont : ∀ g h, Continuous fun t => (ω t g h : ℂ))
    (hdcont : ∀ g, Continuous fun t => d t g)
    (hdnz : ∀ t g, d t g ≠ 0)
    (hdet : ∀ t g h, d t g * d t h = (ω t g h : ℂ) ^ D * d t (g * h)) :
    (ω 1).CohomologousTo (ω 0) := by
  have hroot (g : G) : ∃ β : unitInterval → ℂ,
      Continuous β ∧ (∀ t, β t ^ D = d t g) ∧ ∀ t, β t ≠ 0 :=
    exists_continuous_pow_root_path hD (fun t => d t g) (hdcont g)
      (fun t => hdnz t g)
  choose β hβcont hβpow hβnz using hroot
  let η : unitInterval → G → G → ℂ := fun t g h =>
    (ω t g h : ℂ) * β (g * h) t * (β g t * β h t)⁻¹
  have hηpow (t : unitInterval) (g h : G) : η t g h ^ D = 1 := by
    have hdeteq : β g t ^ D * β h t ^ D =
        (ω t g h : ℂ) ^ D * β (g * h) t ^ D := by
      simpa only [hβpow] using hdet t g h
    calc
      η t g h ^ D = ((ω t g h : ℂ) ^ D * β (g * h) t ^ D) *
          (β g t ^ D * β h t ^ D)⁻¹ := by
        simp only [η, mul_pow, inv_pow, mul_assoc]
      _ = (β g t ^ D * β h t ^ D) *
          (β g t ^ D * β h t ^ D)⁻¹ := by rw [← hdeteq]
      _ = 1 := by field_simp [hβnz g t, hβnz h t]
  have hηcont (g h : G) : Continuous fun t => η t g h := by
    have hden : Continuous fun t => β g t * β h t :=
      (hβcont g).mul (hβcont h)
    have hdennz : ∀ t, β g t * β h t ≠ 0 :=
      fun t => mul_ne_zero (hβnz g t) (hβnz h t)
    exact ((hωcont g h).mul (hβcont (g * h))).mul
      (hden.inv₀ hdennz)
  have hηeq (g h : G) : η 0 g h = η 1 g h :=
    continuous_rootOfUnity_path_const hD (fun t => η t g h)
      (hηcont g h) (fun t => hηpow t g h) 0 1
  let φ : G → Units ℂ := fun g =>
    Units.mk0 (β g 1 / β g 0)
      (div_ne_zero (hβnz g 1) (hβnz g 0))
  refine ⟨φ, ?_⟩
  intro g h
  apply Units.ext
  have hc := hηeq g h
  dsimp only [η] at hc
  change (ω 1 g h : ℂ) =
    (β g 1 / β g 0) * (β h 1 / β h 0) *
      (β (g * h) 1 / β (g * h) 0)⁻¹ * (ω 0 g h : ℂ)
  field_simp [hβnz g 0, hβnz h 0, hβnz (g * h) 1,
    hβnz g 1, hβnz h 1, hβnz (g * h) 0] at hc ⊢
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hc.symm

/-- A continuous path of unitary projective matrices of fixed positive
dimension has cohomologous factor systems at its endpoints. No topology or
finiteness assumption is imposed on the symmetry group: continuity is
required only in the path parameter, separately for each group element.

This is the fixed-dimension virtual obstruction in Schuch–Pérez-García–
Cirac, arXiv:1010.3732, Section II.F.2, lines 930–946. The passage from a
physical gapped path to a continuous virtual path is a separate theorem. -/
theorem unitary_projectivePath_factor_endpoints_cohomologous
    {G : Type*} [Group G] {D : ℕ} (hD : 0 < D)
    (V : unitInterval → G → Matrix (Fin D) (Fin D) ℂ)
    (ω : unitInterval → TNLean.Algebra.ScalarCocycle G)
    (hV : ∀ g, Continuous fun t => V t g)
    (hunitary : ∀ t g, V t g ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hmul : ∀ t g h, V t g * V t h = (ω t g h : ℂ) • V t (g * h)) :
    (ω 1).CohomologousTo (ω 0) := by
  let d : unitInterval → G → ℂ := fun t g => (V t g).det
  have hdcont (g : G) : Continuous fun t => d t g :=
    (hV g).matrix_det
  have hdnz (t : unitInterval) (g : G) : d t g ≠ 0 := by
    have hu : V t g * (V t g)ᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using
        Matrix.mem_unitaryGroup_iff.mp (hunitary t g)
    exact Matrix.det_ne_zero_of_right_inverse hu
  have hdet (t : unitInterval) (g h : G) :
      d t g * d t h = (ω t g h : ℂ) ^ D * d t (g * h) := by
    have heq := congrArg Matrix.det (hmul t g h)
    simpa only [d, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin] using heq
  exact projectiveFactor_endpoints_cohomologous_of_det_path hD ω d
    (continuous_projectiveFactor_of_unitaryMatrixPath hD V ω hV hunitary hmul)
    hdcont hdnz hdet

end MPSTensor
