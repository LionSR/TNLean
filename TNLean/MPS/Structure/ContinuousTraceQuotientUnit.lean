/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Algebra.Group.InjSurj
import TNLean.MPS.Structure.TraceQuotientTripleContinuity

/-!
# Continuous units of trace-quotient algebras

Continuous two- and three-site trace data with injective pointwise realizations
of constant minimal dimension determine a continuous quotient multiplication.
The pointwise matrix-algebra identifications give two-sided units. Near a base
point, left multiplication by its unit stays invertible; applying its inverse
to the base unit recovers the nearby units continuously. No continuous choice
of a minimal tensor, normalization scalar, or algebra identification is used.

**Scope restriction (constant minimal dimension):** This is an auxiliary
finite-dimensional construction for arXiv:1010.3732,
Section II.F.2, lines 953–993. It does not infer constant minimal dimension from
a physical gap or construct a continuous realization at a change of dimension;
see `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix Matrix.Norms.L2Operator

namespace LinearMap

/-- Pointwise unital bilinear multiplications admit a continuous unit near a
recorded base unit. Only continuity of left multiplication by that base unit
is needed. -/
private theorem exists_local_continuous_unit
    {T : Type*} [TopologicalSpace T] {n : ℕ}
    (μ : T → (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (hUnits : ∀ t, ∃ e, (∀ x, μ t e x = x) ∧ (∀ x, μ t x e = x))
    (t₀ : T) (u₀ : Fin n → ℂ) (hu₀ : ∀ x, μ t₀ u₀ x = x)
    (hM : Continuous fun t => LinearMap.toMatrix' (μ t u₀)) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => (LinearMap.toMatrix' (μ t u₀))⁻¹ *ᵥ u₀) S ∧
      ∀ t ∈ S,
        (∀ x, μ t ((LinearMap.toMatrix' (μ t u₀))⁻¹ *ᵥ u₀) x = x) ∧
        (∀ x, μ t x ((LinearMap.toMatrix' (μ t u₀))⁻¹ *ᵥ u₀) = x) := by
  let M := fun t => LinearMap.toMatrix' (μ t u₀)
  let S := {t | IsUnit (M t)}
  have hBase : M t₀ = 1 := by
    have hμ : μ t₀ u₀ = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact hu₀ x
    simp only [M, hμ, LinearMap.toMatrix'_id]
  refine ⟨S, Units.isOpen.preimage hM, ?_, ?_, ?_⟩
  · change IsUnit (M t₀)
    rw [hBase]
    exact isUnit_one
  · rw [continuousOn_iff_continuous_domRestrict]
    have hInv : Continuous fun t : S => (M t)⁻¹ := by
      apply continuous_iff_continuousAt.mpr
      intro t
      obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mp t.property
      have hDet : ContinuousAt Ring.inverse (M t).det := by
        rw [← hu]
        exact NormedRing.inverse_continuousAt u
      exact (continuousAt_matrix_inv _ hDet).comp'
        (f := fun s : S => M s) (hM.comp continuous_subtype_val).continuousAt
    exact hInv.matrix_mulVec continuous_const
  · intro t ht
    obtain ⟨e, heL, heR⟩ := hUnits t
    have he : (M t)⁻¹ *ᵥ u₀ = e := by
      rw [← heR u₀, ← LinearMap.toMatrix'_mulVec]
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
        ((Matrix.isUnit_iff_isUnit_det _).mp ht), Matrix.one_mulVec]
    simpa only [M, he] using And.intro heL heR

end LinearMap


namespace Matrix

private theorem bilinearCoordinates_apply {r : ℕ}
    (M : Matrix (Fin r) (Fin r × Fin r) ℂ) (x y : Fin r → ℂ) :
    Matrix.toLinearMap₂' ℂ (Matrix.of fun a b => fun i => M i (a, b)) x y =
      M *ᵥ (fun ij => x ij.1 * y ij.2) := by
  rw [Matrix.toLinearMap₂'_apply (R := ℂ)]
  ext i
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.of_apply, mul_assoc, mul_comm]

private theorem exists_local_continuous_unit_of_matrixAlgebra
    {T : Type*} [TopologicalSpace T] {r : ℕ}
    (M : T → Matrix (Fin r) (Fin r × Fin r) ℂ) (hM : Continuous M)
    (D : T → ℕ)
    (hAlg : ∀ t, ∃ E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin (D t)) (Fin (D t)) ℂ,
      ∀ x y, E (M t *ᵥ (fun ij => x ij.1 * y ij.2)) = E x * E y)
    (t₀ : T) :
    ∃ (S : Set T) (u : T → Fin r → ℂ), IsOpen S ∧ t₀ ∈ S ∧ ContinuousOn u S ∧
      ∀ t ∈ S, ∀ x,
        M t *ᵥ (fun ij => u t ij.1 * x ij.2) = x ∧
        M t *ᵥ (fun ij => x ij.1 * u t ij.2) = x := by
  let μ : T → (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
    fun t => Matrix.toLinearMap₂' ℂ (Matrix.of fun a b => fun i => M t i (a, b))
  have hUnits : ∀ t, ∃ e, (∀ x, μ t e x = x) ∧ (∀ x, μ t x e = x) := by
    intro t
    obtain ⟨E, hE⟩ := hAlg t
    let : Mul (Fin r → ℂ) := ⟨fun x y => μ t x y⟩
    let : One (Fin r → ℂ) := ⟨E.symm 1⟩
    let : MulOneClass (Fin r → ℂ) := E.injective.mulOneClass E
      (E.apply_symm_apply 1) (fun x y => by
        change E (μ t x y) = E x * E y
        simpa only [μ, bilinearCoordinates_apply] using hE x y)
    exact ⟨E.symm 1, one_mul, mul_one⟩
  obtain ⟨u₀, hu₀, _⟩ := hUnits t₀
  have hLeft : Continuous fun t => LinearMap.toMatrix' (μ t u₀) := by
    apply continuous_matrix
    intro i j
    simpa only [LinearMap.toMatrix'_apply, μ, bilinearCoordinates_apply,
      Function.comp_def] using
      (continuous_apply i).comp (hM.matrix_mulVec (continuous_const
        (y := fun ij : Fin r × Fin r => u₀ ij.1 * (Pi.single j (1 : ℂ) : Fin r → ℂ) ij.2)))
  obtain ⟨S, hS, ht₀, hCont, hUnit⟩ :=
    LinearMap.exists_local_continuous_unit μ hUnits t₀ u₀ hu₀ hLeft
  refine ⟨S, fun t => (LinearMap.toMatrix' (μ t u₀))⁻¹ *ᵥ u₀, hS, ht₀, hCont, ?_⟩
  intro t ht x
  exact ⟨(bilinearCoordinates_apply _ _ _).symm.trans ((hUnit t ht).1 x),
    (bilinearCoordinates_apply _ _ _).symm.trans ((hUnit t ht).2 x)⟩

end Matrix


namespace Matrix

/-- Continuous raw trace data with injective pointwise realizations of constant
minimal dimension admit local continuous quotient multiplication and a local
continuous two-sided unit. The matrix-algebra identifications and the unit are
derived; no continuous choice of a minimal tensor is assumed.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem exists_local_continuous_traceQuotientUnit
    {T : Type*} [TopologicalSpace T] {d r K : ℕ}
    (B : T → MPSTensor d K) (hB : Continuous B)
    (G : T → Matrix (Fin d) (Fin d) ℂ)
    (hG : ∀ t j i, G t j i = Matrix.trace (B t i * B t j))
    (D : T → ℕ) (hD : ∀ t, D t * D t = r)
    (A : ∀ t, MPSTensor d (D t)) (hA : ∀ t, Kraus.IsInjective (A t))
    (α₂ α₃ : T → ℂ) (hα₂ : ∀ t, α₂ t ≠ 0) (hα₃ : ∀ t, α₃ t ≠ 0)
    (hPair : ∀ t i j, Matrix.trace (B t i * B t j) =
      α₂ t * Matrix.trace (A t i * A t j))
    (hTriple : ∀ t i k j, Matrix.trace (B t i * B t k * B t j) =
      α₃ t * Matrix.trace (A t i * A t k * A t j)) (t₀ : T) :
    ∃ (F : Matrix (Fin d) (Fin r) ℂ) (S : Set T) (u : T → Fin r → ℂ),
      IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => traceQuotientProductCoordinates (G t) F
        (traceQuotientTripleColumns (B t) F)) S ∧ ContinuousOn u S ∧
      ∀ t ∈ S,
        let μ := fun x y : Fin r → ℂ =>
          traceQuotientProductCoordinates (G t) F (traceQuotientTripleColumns (B t) F) *ᵥ
            (fun ij => x ij.1 * y ij.2)
        (∀ x, μ (u t) x = x ∧ μ x (u t) = x) ∧
        ∃ E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin (D t)) (Fin (D t)) ℂ,
          (∀ x, E x = (α₃ t / α₂ t) • Fintype.linearCombination ℂ (A t) (F *ᵥ x)) ∧
          (∀ x y, E (μ x y) = E x * E y) ∧
          (∀ x y z, μ (μ x y) z = μ x (μ y z)) := by
  classical
  obtain ⟨F, S₀, hS₀, ht₀, hM, hRecovery⟩ :=
    exists_local_continuous_traceQuotientAlgebra B hB G hG D hD A hA
      α₂ α₃ hα₂ hα₃ hPair hTriple t₀
  let M := fun t => traceQuotientProductCoordinates (G t) F
    (traceQuotientTripleColumns (B t) F)
  have hAlg : ∀ t : S₀, ∃ E : (Fin r → ℂ) ≃ₗ[ℂ]
      Matrix (Fin (D t)) (Fin (D t)) ℂ,
      ∀ x y, E (M t *ᵥ (fun ij => x ij.1 * y ij.2)) = E x * E y := by
    intro t
    obtain ⟨E, _, hMul, _⟩ := hRecovery t t.property
    exact ⟨E, hMul⟩
  obtain ⟨R, v, hR, ht₀R, hv, hUnit⟩ :=
    exists_local_continuous_unit_of_matrixAlgebra (fun t : S₀ => M t)
      (continuousOn_iff_continuous_domRestrict.mp hM) (fun t : S₀ => D t) hAlg ⟨t₀, ht₀⟩
  let u := fun t : T => if ht : t ∈ S₀ then v ⟨t, ht⟩ else 0
  have hCont : ContinuousOn u (Subtype.val '' R) := by
    apply Topology.IsInducing.subtypeVal.continuousOn_image_iff.mpr
    simpa [u, Function.comp_def] using hv
  have hSub : Subtype.val '' R ⊆ S₀ := by
    rintro t ⟨s, _, rfl⟩
    exact s.property
  refine ⟨F, Subtype.val '' R, u, hS₀.isOpenMap_subtype_val R hR,
    ⟨⟨t₀, ht₀⟩, ht₀R, rfl⟩, hM.mono hSub, hCont, ?_⟩
  rintro t ⟨s, hs, rfl⟩
  refine ⟨?_, hRecovery s s.property⟩
  intro x
  simpa only [u, dite_eq_left s.property] using hUnit s hs x

end Matrix
