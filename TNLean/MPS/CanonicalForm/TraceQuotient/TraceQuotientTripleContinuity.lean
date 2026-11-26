/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.TraceQuotient.TraceQuotientAlgebraRecovery
import QICLean.Algebra.MatrixAlgebra.MatrixAlgebraCoordinates
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import QICLean.Analysis.Topology.NewtonIdempotent
import QICLean.Analysis.Topology.ContinuousIdempotentFrames
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Continuous multiplication on finite-ring trace quotients

For a continuous raw tensor family, the two-site trace form and the contracted
three-site columns are continuous. Pointwise injective realizations identify
its trace quotient with the minimal bond matrix algebra. On a neighborhood
where that dimension is constant, a fixed physical coefficient section yields
continuous associative multiplication coordinates and pointwise normalized
multiplicative linear equivalences with the matrix algebra.

**Scope restriction (constant minimal dimension):** The family theorem assumes
that the square of the pointwise minimal bond dimension has a fixed value.
Neither the minimal tensors nor their scalar normalizations are required to
be continuous. This is a finite-data reconstruction consequence relevant to
arXiv:1010.3732, Section II.F.2, lines 953–993, rather than the varying-dimension
phase converse. Continuous unital realization through changes of rank remains
separate; see `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.

The raw trace form is complex bilinear. Its positive Hermitian coordinate
Gram matrix is used only to invert the chosen section.

It also contains the following results.

* `Matrix.exists_local_continuous_traceQuotientPrimitive`: continuous primitive elements of a trace
  quotient.
* `Matrix.exists_local_continuous_traceQuotientUnit`: continuous units of trace-quotient algebras.
-/

section TraceQuotientTripleContinuity

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix BigOperators
namespace Matrix

/-- Contracting a continuous raw tensor family against a fixed physical
section gives continuous three-site trace columns. Auxiliary context:
arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem continuous_traceQuotientTripleColumns
    {T : Type*} [TopologicalSpace T] {d r D : ℕ}
    (B : T → MPSTensor d D) (hB : Continuous B)
    (F : Matrix (Fin d) (Fin r) ℂ) :
    Continuous fun t => traceQuotientTripleColumns (B t) F := by
  have hLC : ∀ x : Fin d → ℂ,
      Continuous fun t => Fintype.linearCombination ℂ (B t) x := by
    intro x
    simpa only [Fintype.linearCombination_apply, Pi.smul_apply, Function.comp_apply] using
      continuous_finsetSum Finset.univ fun i _ =>
        ((continuous_apply i).comp hB).const_smul (x i)
  apply continuous_matrix
  intro j ab
  exact ((hLC (F *ᵥ Pi.single ab.1 1)).matrix_mul
    (hLC (F *ᵥ Pi.single ab.2 1))).matrix_mul
      ((continuous_apply j).comp hB) |>.matrix_trace

private theorem rank_traceGram_of_pair {d D : ℕ} (A : MPSTensor d D)
    (hA : Kraus.IsInjective A) (G : Matrix (Fin d) (Fin d) ℂ)
    (α₂ : ℂ) (hα₂ : α₂ ≠ 0)
    (hG : ∀ j i, G j i = α₂ * Matrix.trace (A i * A j)) :
    G.rank = D * D := by
  have hMap : G.mulVecLin =
      α₂ • (MPSTensor.traceMulRightPi A).comp (Fintype.linearCombination ℂ A) :=
    LinearMap.ext fun x => by
      simpa only [Matrix.mul_one, Matrix.one_mulVec, Matrix.coe_mulVecLin, LinearMap.comp_apply,
        LinearMap.smul_apply] using traceQuotientSection_pair A G
        (1 : Matrix (Fin d) (Fin d) ℂ) α₂ hG x
  rw [Matrix.rank, hMap, LinearMap.range_smul _ α₂ hα₂,
    LinearMap.range_comp_of_range_eq_top _
      ((Fintype.range_linearCombination ℂ A).trans hA),
    LinearMap.finrank_range_of_inj
      (LinearMap.ker_eq_bot.mp (MPSTensor.traceMulRightPi_ker_eq_bot hA))]
  simp [Module.finrank_matrix]

/-- A continuous raw tensor family with injective pointwise realizations of
constant minimal dimension admits locally continuous associative quotient
multiplication. The normalized matrix-algebra identifications are pointwise;
no continuity of the realizations or their normalization scalars is assumed.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem exists_local_continuous_traceQuotientAlgebra
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
    ∃ (F : Matrix (Fin d) (Fin r) ℂ) (S : Set T), IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => traceQuotientProductCoordinates (G t) F
        (traceQuotientTripleColumns (B t) F)) S ∧
      ∀ t ∈ S,
        let μ := fun x y : Fin r → ℂ =>
          traceQuotientProductCoordinates (G t) F (traceQuotientTripleColumns (B t) F) *ᵥ
            (fun ij => x ij.1 * y ij.2)
        ∃ E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin (D t)) (Fin (D t)) ℂ,
          (∀ x, E x = (α₃ t / α₂ t) • Fintype.linearCombination ℂ (A t) (F *ᵥ x)) ∧
          (∀ x y, E (μ x y) = E x * E y) ∧
          (∀ x y z, μ (μ x y) z = μ x (μ y z)) := by
  have hGC : Continuous G := by
    apply continuous_matrix
    intro j i
    simpa only [hG, Function.comp_apply] using (((continuous_apply i).comp hB).matrix_mul
      ((continuous_apply j).comp hB)).matrix_trace
  have hRank : ∀ t, (G t).rank = r := fun t =>
    (rank_traceGram_of_pair (A t) (hA t) (G t) (α₂ t) (hα₂ t)
      (fun j i => (hG t j i).trans (hPair t i j))).trans (hD t)
  obtain ⟨F, S, hS, ht₀, hCont, hSection⟩ :=
    exists_local_continuous_traceQuotientProductCoordinates G hGC hRank t₀
      (fun F t => traceQuotientTripleColumns (B t) F)
      (fun F => continuous_traceQuotientTripleColumns B hB F)
  exact ⟨F, S, hS, ht₀, hCont, fun t ht =>
    traceQuotientProductCoordinates_algebraRecovery_of_two_three_trace_eq
      (A t) (B t) (G t) (hG t) F (α₂ t) (α₃ t) (hα₂ t) (hα₃ t)
      (hD t).symm (hSection t ht).1 (hPair t) (hTriple t)⟩

end Matrix

end TraceQuotientTripleContinuity

section ContinuousTraceQuotientUnit

/-!
## Continuous units of trace-quotient algebras

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
      obtain ⟨u, hu⟩ := t.property
      have hAt : ContinuousAt Ring.inverse (M t) := hu ▸ NormedRing.inverse_continuousAt u
      simpa only [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using
        hAt.comp' (f := fun s : S => M s) (hM.comp continuous_subtype_val).continuousAt
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
        simpa only [μ, toLinearMap₂'_apply_mulVec_prod] using hE x y)
    exact ⟨E.symm 1, one_mul, mul_one⟩
  obtain ⟨u₀, hu₀, _⟩ := hUnits t₀
  have hLeft : Continuous fun t => LinearMap.toMatrix' (μ t u₀) := by
    apply continuous_matrix
    intro i j
    simpa only [LinearMap.toMatrix'_apply, μ, toLinearMap₂'_apply_mulVec_prod,
      Function.comp_def] using
      (continuous_apply i).comp (hM.matrix_mulVec (continuous_const
        (y := fun ij : Fin r × Fin r => u₀ ij.1 * (Pi.single j (1 : ℂ) : Fin r → ℂ) ij.2)))
  obtain ⟨S, hS, ht₀, hCont, hUnit⟩ :=
    LinearMap.exists_local_continuous_unit μ hUnits t₀ u₀ hu₀ hLeft
  refine ⟨S, fun t => (LinearMap.toMatrix' (μ t u₀))⁻¹ *ᵥ u₀, hS, ht₀, hCont, ?_⟩
  intro t ht x
  exact ⟨(toLinearMap₂'_apply_mulVec_prod _ _ _).symm.trans ((hUnit t ht).1 x),
    (toLinearMap₂'_apply_mulVec_prod _ _ _).symm.trans ((hUnit t ht).2 x)⟩

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

end ContinuousTraceQuotientUnit

section ContinuousTraceQuotientPrimitive

/-!
## Continuous primitive elements of a trace quotient

Continuous two-site and three-site trace data determine a continuous quotient
multiplication when their pointwise injective realizations have constant minimal
bond dimension. Starting from a primitive matrix unit at one parameter, polynomial
idempotent correction selects a nearby idempotent in the regular representation.
The selected matrices remain in the regular algebra because they belong to the
algebra generated by the initial regular matrix. Evaluation at the continuous
unit then recovers a continuous element of the quotient algebra.

The corresponding principal left ideals have locally constant dimension. No
continuous choice of a minimal tensor or matrix-algebra identification is assumed.
**Scope restriction (constant minimal dimension):** This is an auxiliary
construction for arXiv:1010.3732, Section II.F.2, lines 953–993. The pointwise
injective representatives have constant positive bond dimension. A physical gap
can coexist with a change of minimal dimension; constructing compatible
continuous canonical data through that change remains separate. See
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix

namespace Matrix

private noncomputable def leftRegularMatrix {r : ℕ}
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ)) :
    (Fin r → ℂ) →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ :=
  LinearMap.toMatrix'.toLinearMap.comp μ

private theorem leftRegularMatrix_mulVec {r : ℕ}
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (x y : Fin r → ℂ) : leftRegularMatrix μ x *ᵥ y = μ x y := by
  simp only [leftRegularMatrix, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.toMatrix'_mulVec]

private theorem leftRegularMatrix_mul {r : ℕ}
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (hAssoc : ∀ x y z, μ (μ x y) z = μ x (μ y z)) (x y : Fin r → ℂ) :
    leftRegularMatrix μ (μ x y) = leftRegularMatrix μ x * leftRegularMatrix μ y := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro z
  simpa only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, leftRegularMatrix_mulVec]
    using hAssoc x y z

private theorem leftRegularMatrix_injective {r : ℕ}
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (u : Fin r → ℂ) (hU : ∀ x, μ x u = x) :
    Function.Injective (leftRegularMatrix μ) := by
  intro x y hxy
  simpa only [leftRegularMatrix_mulVec, hU] using congrArg (fun M => M *ᵥ u) hxy

private theorem exists_leftRegularAlgHom {r D : ℕ}
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : ∀ x y, E (μ x y) = E x * E y) :
    ∃ f : Matrix (Fin D) (Fin D) ℂ →ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ,
      ∀ x, f (E x) = leftRegularMatrix μ x := by
  let : Mul (Fin r → ℂ) := ⟨fun x y => μ x y⟩
  let : Semigroup (Fin r → ℂ) := E.injective.semigroup E hE
  let : One (Fin r → ℂ) := ⟨E.symm 1⟩
  let : MulOneClass (Fin r → ℂ) :=
    E.injective.mulOneClass E (E.apply_symm_apply 1) hE
  have hUnit : ∀ x, μ (E.symm 1) x = x := one_mul
  let T := (leftRegularMatrix μ).comp E.symm.toLinearMap
  have hOne : T 1 = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simpa only [T, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Matrix.toLin'_apply, leftRegularMatrix_mulVec, Matrix.one_mulVec] using
      hUnit x
  have hMul : ∀ x y, T (x * y) = T x * T y := by
    intro x y
    have hInv : E.symm (x * y) = μ (E.symm x) (E.symm y) := by
      apply E.injective
      simp only [E.apply_symm_apply, hE]
    simpa only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, hInv] using
      leftRegularMatrix_mul μ mul_assoc (E.symm x) (E.symm y)
  refine ⟨AlgHom.ofLinearMap T hOne hMul, ?_⟩
  intro x
  simp only [AlgHom.ofLinearMap_apply, T, LinearMap.comp_apply,
    LinearEquiv.coe_coe, E.symm_apply_apply]

private theorem leftRegularMatrix_recover_of_mem_adjoin {r D : ℕ}
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (u : Fin r → ℂ) (hU : ∀ x, μ x u = x)
    (E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : ∀ x y, E (μ x y) = E x * E y) (p₀ : Fin r → ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ)
    (hP : P ∈ Algebra.adjoin ℂ {leftRegularMatrix μ p₀}) :
    leftRegularMatrix μ (P *ᵥ u) = P := by
  obtain ⟨f, hf⟩ := exists_leftRegularAlgHom μ E hE
  have hLe : Algebra.adjoin ℂ {leftRegularMatrix μ p₀} ≤ f.range := by
    apply Algebra.adjoin_le
    intro M hM
    obtain rfl := Set.mem_singleton_iff.mp hM
    rw [← hf]
    exact f.mem_range_self (E p₀)
  obtain ⟨M, hM⟩ := f.mem_range.mp (hLe hP)
  have hx : leftRegularMatrix μ (E.symm M) = P := by
    rw [← hf, E.apply_symm_apply]
    exact hM
  rw [← hx, leftRegularMatrix_mulVec, hU]

private theorem rightRegularMatrix_idempotent {r : ℕ}
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (hAssoc : ∀ x y z, μ (μ x y) z = μ x (μ y z))
    (p : Fin r → ℂ) (hp : μ p p = p) :
    IsIdempotentElem (LinearMap.toMatrix' (μ.flip p)) := by
  change LinearMap.toMatrix' (μ.flip p) * LinearMap.toMatrix' (μ.flip p) =
    LinearMap.toMatrix' (μ.flip p)
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
    LinearMap.toMatrix'_mulVec, LinearMap.flip_apply, hAssoc, hp]

private theorem exists_local_continuous_idempotent_element
    {T : Type*} [TopologicalSpace T] {r k : ℕ}
    (μ : T → (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (hL : ∀ x, Continuous fun t => leftRegularMatrix (μ t) x)
    (hAssoc : ∀ t x y z, μ t (μ t x y) z = μ t x (μ t y z))
    (u : T → Fin r → ℂ) (hu : Continuous u)
    (hUnit : ∀ t x, μ t (u t) x = x ∧ μ t x (u t) = x)
    (D : T → ℕ)
    (hAlg : ∀ t, ∃ E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin (D t)) (Fin (D t)) ℂ,
      ∀ x y, E (μ t x y) = E x * E y)
    (t₀ : T) (p₀ : Fin r → ℂ) (hp₀ : μ t₀ p₀ p₀ = p₀)
    (hRank₀ : (LinearMap.toMatrix' ((μ t₀).flip p₀)).rank = k) :
    ∃ (S : Set T) (p : T → Fin r → ℂ), IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn p S ∧ p t₀ = p₀ ∧
      ContinuousOn (fun t => LinearMap.toMatrix' ((μ t).flip (p t))) S ∧
      ∀ t ∈ S, μ t (p t) (p t) = p t ∧
        (LinearMap.toMatrix' ((μ t).flip (p t))).rank = k := by
  have hBase : IsIdempotentElem (leftRegularMatrix (μ t₀) p₀) := by
    change leftRegularMatrix (μ t₀) p₀ * leftRegularMatrix (μ t₀) p₀ =
      leftRegularMatrix (μ t₀) p₀
    rw [← leftRegularMatrix_mul _ (hAssoc t₀), hp₀]
  obtain ⟨S, P, hS, ht₀, hP, hP₀, hIdem⟩ :=
    exists_local_continuous_idempotent_in_adjoin
      (fun t => leftRegularMatrix (μ t) p₀) (hL p₀) t₀ hBase
  let p := fun t => P t *ᵥ u t
  have hp : ContinuousOn p S := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuousOn_iff_continuous_domRestrict.mp hP).matrix_mulVec
      (hu.comp continuous_subtype_val)
  have hRecover : ∀ t ∈ S, leftRegularMatrix (μ t) (p t) = P t := by
    intro t ht
    obtain ⟨E, hE⟩ := hAlg t
    exact leftRegularMatrix_recover_of_mem_adjoin (μ t) (u t)
      (fun x => (hUnit t x).2) E hE p₀ (P t) (hIdem t ht).2
  have hp₀Eq : p t₀ = p₀ := by
    simp only [p, hP₀, leftRegularMatrix_mulVec]
    exact (hUnit t₀ p₀).2
  have hPIdem : ∀ t ∈ S, μ t (p t) (p t) = p t := by
    intro t ht
    apply leftRegularMatrix_injective (μ t) (u t) (fun x => (hUnit t x).2)
    rw [leftRegularMatrix_mul _ (hAssoc t), hRecover t ht]
    exact (hIdem t ht).1.eq
  let R := fun t => LinearMap.toMatrix' ((μ t).flip (p t))
  have hR : ContinuousOn R S := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_matrix
    intro i j
    simpa only [R, Set.domRestrict_apply, LinearMap.toMatrix'_apply,
      LinearMap.flip_apply, ← leftRegularMatrix_mulVec, Function.comp_def] using
      (continuous_apply i).comp
        (((hL (Pi.single j 1)).comp continuous_subtype_val).matrix_mulVec
          (continuousOn_iff_continuous_domRestrict.mp hp))
  have hRIdem : ∀ t ∈ S, IsIdempotentElem (R t) := fun t ht =>
    rightRegularMatrix_idempotent (μ t) (hAssoc t) (p t) (hPIdem t ht)
  obtain ⟨W, hW, ht₀W, hRank⟩ :=
    exists_open_constantRank_of_idempotent (fun t : S => R t)
      (continuousOn_iff_continuous_domRestrict.mp hR)
      (fun t => hRIdem t t.property) ⟨t₀, ht₀⟩
  have hSub : Subtype.val '' W ⊆ S := by
    rintro t ⟨s, _, rfl⟩
    exact s.property
  refine ⟨Subtype.val '' W, p, hS.isOpenMap_subtype_val W hW,
    ⟨⟨t₀, ht₀⟩, ht₀W, rfl⟩, hp.mono hSub, hp₀Eq, hR.mono hSub, ?_⟩
  rintro t ⟨s, hs, rfl⟩
  refine ⟨hPIdem s s.property, (hRank s hs).trans ?_⟩
  simpa only [R, hp₀Eq] using hRank₀

/-- Continuous raw two-site and three-site trace data with injective pointwise
realizations of constant positive minimal dimension admit a local continuous
primitive idempotent in their reconstructed quotient algebra. Its principal
left ideal has the minimal bond dimension. Neither a continuous minimal tensor
nor a continuous matrix-algebra identification is assumed.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem exists_local_continuous_traceQuotientPrimitive
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
      α₃ t * Matrix.trace (A t i * A t k * A t j))
    (t₀ : T) (hD₀ : 0 < D t₀) :
    ∃ F : Matrix (Fin d) (Fin r) ℂ,
      let M := fun t => traceQuotientProductCoordinates (G t) F
        (traceQuotientTripleColumns (B t) F)
      let μ : T → (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
    fun t => Matrix.toLinearMap₂' ℂ
        (Matrix.of fun a b => fun i => M t i (a, b))
      ∃ (S : Set T) (u p : T → Fin r → ℂ), IsOpen S ∧ t₀ ∈ S ∧
        ContinuousOn M S ∧ ContinuousOn u S ∧ ContinuousOn p S ∧
        ContinuousOn (fun t => LinearMap.toMatrix' ((μ t).flip (p t))) S ∧
        ∀ t ∈ S,
          (∀ x, μ t (u t) x = x ∧ μ t x (u t) = x) ∧
          μ t (p t) (p t) = p t ∧
          (LinearMap.toMatrix' ((μ t).flip (p t))).rank = D t₀ ∧
          ∃ E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin (D t)) (Fin (D t)) ℂ,
            (∀ x, E x = (α₃ t / α₂ t) • Fintype.linearCombination ℂ (A t) (F *ᵥ x)) ∧
            (∀ x y, E (μ t x y) = E x * E y) ∧
            (∀ x y z, μ t (μ t x y) z = μ t x (μ t y z)) := by
  classical
  obtain ⟨F, S₀, u, hS₀, ht₀, hM, hu, hRecovery⟩ :=
    exists_local_continuous_traceQuotientUnit B hB G hG D hD A hA
      α₂ α₃ hα₂ hα₃ hPair hTriple t₀
  let M := fun t => traceQuotientProductCoordinates (G t) F
    (traceQuotientTripleColumns (B t) F)
  let μ : T → (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
    fun t => Matrix.toLinearMap₂' ℂ
    (Matrix.of fun a b => fun i => M t i (a, b))
  have hμ : ∀ t x y, μ t x y = M t *ᵥ (fun ij => x ij.1 * y ij.2) :=
    fun t x y => toLinearMap₂'_apply_mulVec_prod (M t) x y
  have hL : ∀ x, Continuous fun t : S₀ => leftRegularMatrix (μ t) x := by
    intro x
    apply continuous_matrix
    intro i j
    simpa only [leftRegularMatrix, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.toMatrix'_apply, hμ, Function.comp_def, M, Set.domRestrict_apply] using
      (continuous_apply i).comp
        ((continuousOn_iff_continuous_domRestrict.mp hM).matrix_mulVec
          (continuous_const (y := fun ab : Fin r × Fin r =>
            x ab.1 * (Pi.single j (1 : ℂ) : Fin r → ℂ) ab.2)))
  have hRec : ∀ t ∈ S₀,
      (∀ x, μ t (u t) x = x ∧ μ t x (u t) = x) ∧
      ∃ E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin (D t)) (Fin (D t)) ℂ,
        (∀ x, E x = (α₃ t / α₂ t) • Fintype.linearCombination ℂ (A t) (F *ᵥ x)) ∧
        (∀ x y, E (μ t x y) = E x * E y) ∧
        (∀ x y z, μ t (μ t x y) z = μ t x (μ t y z)) := by
    intro t ht
    simpa only [hμ] using hRecovery t ht
  obtain ⟨E₀, _, hE₀, _⟩ := (hRec t₀ ht₀).2
  let i₀ : Fin (D t₀) := ⟨0, hD₀⟩
  let p₀ := E₀.symm (Matrix.single i₀ i₀ 1)
  have hp₀ : μ t₀ p₀ p₀ = p₀ := by
    apply E₀.injective
    simp only [hE₀, p₀, E₀.apply_symm_apply, Matrix.single_mul_single_same, mul_one]
  have hRank₀ : (LinearMap.toMatrix' ((μ t₀).flip p₀)).rank = D t₀ := by
    unfold Matrix.rank
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
    exact finrank_range_rightMul_of_matrixAlgebra (μ t₀) E₀ hE₀ i₀
  have hAssoc : ∀ (t : S₀) x y z,
      μ t (μ t x y) z = μ t x (μ t y z) := by
    intro t
    obtain ⟨_, _, _, hAssoc⟩ := (hRec t t.property).2
    exact hAssoc
  have hAlg : ∀ t : S₀, ∃ E : (Fin r → ℂ) ≃ₗ[ℂ]
      Matrix (Fin (D t)) (Fin (D t)) ℂ,
      ∀ x y, E (μ t x y) = E x * E y := by
    intro t
    obtain ⟨E, _, hE, _⟩ := (hRec t t.property).2
    exact ⟨E, hE⟩
  obtain ⟨W, p, hW, ht₀W, hp, _, hR, hPrimitive⟩ :=
    exists_local_continuous_idempotent_element (fun t : S₀ => μ t) hL hAssoc
      (fun t : S₀ => u t) (continuousOn_iff_continuous_domRestrict.mp hu)
      (fun t x => (hRec t t.property).1 x) (fun t : S₀ => D t) hAlg
      ⟨t₀, ht₀⟩ p₀ hp₀ hRank₀
  let q := fun t => if ht : t ∈ S₀ then p ⟨t, ht⟩ else 0
  have hq : ContinuousOn q (Subtype.val '' W) := by
    apply Topology.IsInducing.subtypeVal.continuousOn_image_iff.mpr
    simpa [q, Function.comp_def] using hp
  have hqR : ContinuousOn (fun t => LinearMap.toMatrix' ((μ t).flip (q t)))
      (Subtype.val '' W) := by
    apply Topology.IsInducing.subtypeVal.continuousOn_image_iff.mpr
    simpa [q, Function.comp_def] using hR
  have hSub : Subtype.val '' W ⊆ S₀ := by
    rintro t ⟨s, _, rfl⟩
    exact s.property
  refine ⟨F, Subtype.val '' W, u, q, hS₀.isOpenMap_subtype_val W hW,
    ⟨⟨t₀, ht₀⟩, ht₀W, rfl⟩, hM.mono hSub, hu.mono hSub, hq, hqR, ?_⟩
  rintro t ⟨s, hs, rfl⟩
  obtain ⟨hIdem, hRank⟩ := hPrimitive s hs
  refine ⟨(hRec s s.property).1, ?_, ?_, (hRec s s.property).2⟩
  · simpa only [q, dite_eq_left s.property] using hIdem
  · simpa only [q, dite_eq_left s.property] using hRank

end Matrix

end ContinuousTraceQuotientPrimitive
