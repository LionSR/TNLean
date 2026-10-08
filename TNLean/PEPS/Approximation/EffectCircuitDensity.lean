/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.EffectCircuitError

/-! # Physical density error for source-only replacement

The actual additional registers are finite-dimensional by construction.
Their normalized vector can be discarded without changing the original
physical density. The resulting trace-norm error is at most four times
the gate budget times the original gate count.

Source: polynomial-PEPS, `04-compression.tex`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2, lines 137–151 and 199–251.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-effectcircuitdensity-01
Matrix.appendAuxiliaryVector
Provenance-ID: 8769-source-resource-effectcircuitdensity-02
Matrix.norm_appendAuxiliaryVector
Provenance-ID: 8769-source-resource-effectcircuitdensity-03
Matrix.partialTraceRight_appendAuxiliaryVector
Provenance-ID: 8769-source-resource-effectcircuitdensity-04
Matrix.rectangularTraceNorm_appendAuxiliaryVector_error_le_two
Provenance-ID: 8769-source-resource-effectcircuitdensity-05
TNLean.PEPS.PairEffect.EffectCircuit.finiteDimensional_auxiliary
Provenance-ID: 8769-source-resource-effectcircuitdensity-06
TNLean.PEPS.PairEffect.EffectCircuit.originalPhysicalDensity
Provenance-ID: 8769-source-resource-effectcircuitdensity-07
TNLean.PEPS.PairEffect.EffectCircuit.rectangularTraceNorm_replacement_density_sub_le
Provenance-ID: 8769-source-resource-effectcircuitdensity-08
TNLean.PEPS.PairEffect.EffectCircuit.replacementPhysicalDensity
Provenance-ID: 8769-source-resource-effectcircuitdensity-09
TNLean.PEPS.PairEffect.PartyChain.finiteDimensional_sources_prepStack
Provenance-ID: 8769-source-resource-effectcircuitdensity-10
TNLean.PEPS.PairEffect.auxiliaryCoordinateIso
Provenance-ID: 8769-source-resource-effectcircuitdensity-11
TNLean.PEPS.PairEffect.auxiliaryCoordinateIso_tmul
Provenance-ID: 8769-source-resource-effectcircuitdensity-12
TNLean.PEPS.PairEffect.auxiliaryCoordinates
Provenance-ID: 8769-source-resource-effectcircuitdensity-13
TNLean.PEPS.PairEffect.extendedPhysicalReadout
Provenance-ID: 8769-source-resource-effectcircuitdensity-14
TNLean.PEPS.PairEffect.extendedPhysicalReadout_append_tmul
Provenance-ID: 8769-source-resource-effectcircuitdensity-15
TNLean.PEPS.PairEffect.finiteDimensional_mem_append
Provenance-ID: 8769-source-resource-effectcircuitdensity-16
TNLean.PEPS.PairEffect.finiteDimensional_sources_comp
Provenance-ID: 8769-source-resource-effectcircuitdensity-17
TNLean.PEPS.PairEffect.finiteDimensional_sources_prepGate
Provenance-ID: 8769-source-resource-effectcircuitdensity-18
TNLean.PEPS.PairEffect.finiteDimensional_sources_prepWord
Provenance-ID: 8769-source-resource-effectcircuitdensity-19
TNLean.PEPS.PairEffect.norm_extendedPhysicalReadout_le_one
Provenance-ID: 8769-source-resource-effectcircuitdensity-20
TNLean.PEPS.PairEffect.rectangularTraceNorm_extendedPhysicalReadout_error_le
-/

noncomputable section
/-! Appending a normalized auxiliary vector preserves the physical density.
Source: polynomial-PEPS, `04-compression.tex:199–229`, immutable revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/
open scoped Matrix ComplexOrder Kronecker InnerProductSpace
noncomputable section
namespace Matrix
variable {Phys Env Aux : Type*} [Fintype Env] [Fintype Aux]

/-- Literal coordinate vector with the auxiliary factor grouped into the environment.
Source: polynomial-PEPS, `04-compression.tex:199–229`. -/
def appendAuxiliaryVector (v : EuclideanSpace ℂ (Phys × Env))
    (γ : EuclideanSpace ℂ Aux) : EuclideanSpace ℂ (Phys × (Env × Aux)) :=
  WithLp.toLp 2 (fun p ↦ v (p.1, p.2.1) * γ p.2.2)

/-- The physical density is unchanged on discarding a normalized auxiliary vector.
Source: polynomial-PEPS, `04-compression.tex:223–227`. -/
theorem partialTraceRight_appendAuxiliaryVector
    (v : EuclideanSpace ℂ (Phys × Env)) (γ : EuclideanSpace ℂ Aux)
    (hγ : ‖γ‖ = 1) :
    partialTraceRight (euclideanOuterProduct (appendAuxiliaryVector v γ)
      (appendAuxiliaryVector v γ)) = partialTraceRight (euclideanOuterProduct v v) := by
  have h := congrArg (@partialTraceRight Phys Env _) (partialTraceRight_tensorVector v γ hγ)
  rw [partialTraceRight_partialTraceRight] at h
  exact h
/-- Actual Euclidean norms multiply under auxiliary tensoring, including zero vectors.
Source: polynomial-PEPS, `04-compression.tex:199–229`. -/
theorem norm_appendAuxiliaryVector [Fintype Phys]
    (v : EuclideanSpace ℂ (Phys × Env)) (γ : EuclideanSpace ℂ Aux) :
    ‖appendAuxiliaryVector v γ‖ = ‖v‖ * ‖γ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simp only [EuclideanSpace.norm_sq_eq, appendAuxiliaryVector,
    Fintype.sum_prod_type, norm_mul, mul_pow]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
/-- Absolute physical density error for a literal approximate extended vector.
There is no division by the original vector norm.
Source: polynomial-PEPS, `eq:compression-effect-circuit-error`,
`04-compression.tex:218–229`. -/
theorem rectangularTraceNorm_appendAuxiliaryVector_error_le_two
    [Fintype Phys] [DecidableEq Phys]
    (v : EuclideanSpace ℂ (Phys × Env)) (γ : EuclideanSpace ℂ Aux)
    (w' : EuclideanSpace ℂ (Phys × (Env × Aux)))
    (hγ : ‖γ‖ = 1) (hv : ‖v‖ ≤ 1) (hw' : ‖w'‖ ≤ 1) :
    rectangularTraceNorm
      (partialTraceRight (euclideanOuterProduct w' w') -
        partialTraceRight (euclideanOuterProduct v v)) ≤
      2 * ‖w' - appendAuxiliaryVector v γ‖ := by
  rw [← partialTraceRight_appendAuxiliaryVector v γ hγ]
  apply rectangularTraceNorm_partialTraceRight_pure_density_sub_le_two _ _ hw'
  simpa only [norm_appendAuxiliaryVector, hγ, mul_one] using hv
end Matrix



open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
open ContinuousLinearMap
variable {P : Type} {Phys Env Aux : Type*}
  [Fintype Phys] [Fintype Env] [Fintype Aux]

/-- Euclidean coordinates for the auxiliary-first tensor product, ordered physical,
environment, auxiliary. Source: polynomial-PEPS, `04-compression.tex:223–227`. -/
def auxiliaryCoordinateIso :
    (EuclideanSpace ℂ Aux ⊗[ℂ] EuclideanSpace ℂ (Phys × Env)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Phys × (Env × Aux)) :=
  (((EuclideanSpace.basisFun Aux ℂ).tensorProduct
    (EuclideanSpace.basisFun (Phys × Env) ℂ)).reindex
      ((Equiv.prodComm Aux (Phys × Env)).trans (Equiv.prodAssoc Phys Env Aux))).repr

/-- These coordinates are the literal product of the physical-environment and
auxiliary entries. Source: polynomial-PEPS, `04-compression.tex:223–227`. -/
theorem auxiliaryCoordinateIso_tmul (γ : EuclideanSpace ℂ Aux)
    (v : EuclideanSpace ℂ (Phys × Env)) :
    auxiliaryCoordinateIso (γ ⊗ₜ[ℂ] v) = Matrix.appendAuxiliaryVector v γ := by
  ext p
  simp only [auxiliaryCoordinateIso, OrthonormalBasis.repr_reindex,
    OrthonormalBasis.tensorProduct_repr_tmul_apply', EuclideanSpace.basisFun_repr]
  rfl
/-- Readout on the actual extended memory, with the auxiliary factor discarded
only when forming the physical density. Source: polynomial-PEPS,
`04-compression.tex:223–227`. -/
def extendedPhysicalReadout {rs b : Layout P}
    (H : Mem rs ≃ₗᵢ[ℂ] EuclideanSpace ℂ Aux)
    (K : Mem b →L[ℂ] EuclideanSpace ℂ (Phys × Env)) :
    Mem (rs ++ b) →L[ℂ] EuclideanSpace ℂ (Phys × (Env × Aux)) :=
  isoL auxiliaryCoordinateIso ∘L TensorProduct.mapL (isoL H) K ∘L isoL (appendIso rs b)

/-- The exact extended memory has the literal tensor-product coordinates.
Source: polynomial-PEPS, `04-compression.tex:223–227`. -/
theorem extendedPhysicalReadout_append_tmul {rs b : Layout P}
    (H : Mem rs ≃ₗᵢ[ℂ] EuclideanSpace ℂ Aux)
    (K : Mem b →L[ℂ] EuclideanSpace ℂ (Phys × Env))
    (γ : Mem rs) (v : Mem b) :
    extendedPhysicalReadout H K ((appendIso rs b).symm (γ ⊗ₜ[ℂ] v)) =
      Matrix.appendAuxiliaryVector (K v) (H γ) := by
  simp only [extendedPhysicalReadout, comp_apply, isoL_apply,
    LinearIsometryEquiv.apply_symm_apply, TensorProduct.mapL_tmul]
  exact auxiliaryCoordinateIso_tmul _ _
/-- A contraction physical readout remains a contraction on the extended memory.
Source: polynomial-PEPS, `04-compression.tex:223–227`. -/
theorem norm_extendedPhysicalReadout_le_one {rs b : Layout P}
    (H : Mem rs ≃ₗᵢ[ℂ] EuclideanSpace ℂ Aux)
    (K : Mem b →L[ℂ] EuclideanSpace ℂ (Phys × Env)) (hK : ‖K‖ ≤ 1) :
    ‖extendedPhysicalReadout H K‖ ≤ 1 := by
  dsimp only [extendedPhysicalReadout]
  apply norm_comp_le_one
    (LinearIsometry.norm_toContinuousLinearMap_le
      (auxiliaryCoordinateIso (Phys := Phys) (Env := Env) (Aux := Aux)).toLinearIsometry)
  apply norm_comp_le_one _
    (LinearIsometry.norm_toContinuousLinearMap_le (appendIso rs b).toLinearIsometry)
  exact (TensorProduct.norm_mapL_le (isoL H) K).trans
    ((mul_le_mul_of_nonneg_right
      (LinearIsometry.norm_toContinuousLinearMap_le H.toLinearIsometry)
      (norm_nonneg K)).trans (by simpa only [one_mul] using hK))
/-- A native Hilbert-space approximation yields an absolute physical density
error after the actual contraction readout. Source: polynomial-PEPS,
`eq:compression-effect-circuit-error`, `04-compression.tex:218–229`. -/
theorem rectangularTraceNorm_extendedPhysicalReadout_error_le
    [DecidableEq Phys] {rs b : Layout P}
    (H : Mem rs ≃ₗᵢ[ℂ] EuclideanSpace ℂ Aux)
    (K : Mem b →L[ℂ] EuclideanSpace ℂ (Phys × Env)) (hK : ‖K‖ ≤ 1)
    (γ : Mem rs) (v : Mem b) (u : Mem (rs ++ b))
    (hγ : ‖γ‖ = 1) (hv : ‖v‖ ≤ 1) (hu : ‖u‖ ≤ 1) {η : ℝ}
    (he : ‖u - (appendIso rs b).symm (γ ⊗ₜ[ℂ] v)‖ ≤ η) :
    Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
        (extendedPhysicalReadout H K u) (extendedPhysicalReadout H K u)) -
        Matrix.partialTraceRight (Matrix.euclideanOuterProduct (K v) (K v))) ≤ 2 * η := by
  have hR := norm_extendedPhysicalReadout_le_one H K hK
  have hKv : ‖K v‖ ≤ 1 := (K.le_opNorm_of_le hv).trans
    (by simpa only [mul_one] using hK)
  have hRu : ‖extendedPhysicalReadout H K u‖ ≤ 1 :=
    ((extendedPhysicalReadout H K).le_opNorm_of_le hu).trans
      (by simpa only [mul_one] using hR)
  have hdist : ‖extendedPhysicalReadout H K u -
      Matrix.appendAuxiliaryVector (K v) (H γ)‖ ≤ η := by
    rw [← extendedPhysicalReadout_append_tmul H K γ v,
      ← map_sub (extendedPhysicalReadout H K)]
    exact ((extendedPhysicalReadout H K).le_opNorm _).trans
      (((mul_le_mul_of_nonneg_right hR (norm_nonneg _)).trans_eq (one_mul _)).trans he)
  exact (Matrix.rectangularTraceNorm_appendAuxiliaryVector_error_le_two
    (K v) (H γ) (extendedPhysicalReadout H K u) ((H.norm_map γ).trans hγ)
    hKv hRu).trans (mul_le_mul_of_nonneg_left hdist (by positivity))
end TNLean.PEPS.PairEffect



namespace TNLean.PEPS.PairEffect
variable {P : Type}
/-- Concatenated finite memories are finite by the actual concatenation isometry.
Source: polynomial-PEPS, `04-compression.tex:199–217`. -/
theorem finiteDimensional_mem_append (a b : Layout P)
    [FiniteDimensional ℂ (Mem a).carrier] [FiniteDimensional ℂ (Mem b).carrier] :
    FiniteDimensional ℂ (Mem (a ++ b)).carrier :=
  (appendIso a b).symm.toLinearEquiv.finiteDimensional

/-- Only the Euclidean source pairs, rather than the private input memory,
enter a prepared stack's source inventory.
Source: polynomial-PEPS, `04-compression.tex:103–112`. -/
theorem finiteDimensional_sources_prepWord {p q : P} (hpq : p ≠ q)
    {α β : Type} [Fintype α] [Fintype β]
    (η : EuclideanSpace ℂ (α × β)) (m : ℕ) (a : Layout P) :
    FiniteDimensional ℂ (Mem (prepWord hpq η m a).sources.layout).carrier := by
  induction m with
  | zero => change FiniteDimensional ℂ ℂ; infer_instance
  | succ m ih =>
      let := ih
      change FiniteDimensional ℂ (EuclideanSpace ℂ α ⊗[ℂ]
        (EuclideanSpace ℂ β ⊗[ℂ] Mem (prepWord hpq η m a).sources.layout))
      infer_instance
/-- Composition concatenates the actual finite source memories.
Source: polynomial-PEPS, `04-compression.tex:103–112`. -/
theorem finiteDimensional_sources_comp {a b c : Layout P} (w : Word a b) (v : Word b c)
    [FiniteDimensional ℂ (Mem w.sources.layout).carrier]
    [FiniteDimensional ℂ (Mem v.sources.layout).carrier] :
    FiniteDimensional ℂ (Mem (Word.comp w v).sources.layout).carrier := by
  let := finiteDimensional_mem_append v.sources.layout w.sources.layout
  exact (Layout.memCongr (SourceInventory.layout_append v.sources w.sources)).symm
    |>.toLinearEquiv.finiteDimensional

namespace PartyChain
/-- Every retained source register of a stack is finite-dimensional;
no dimension assumption is made on the input or output private memories.
Source: polynomial-PEPS, `04-compression.tex:103–112`. -/
theorem finiteDimensional_sources_prepStack {a b : Layout P} (M : PartyChain a b)
    (m : ℕ) : ∀ tail : Layout P,
    FiniteDimensional ℂ (Mem (M.prepStack m tail).sources.layout).carrier := by
  induction M with
  | final => intro tail; change FiniteDimensional ℂ ℂ; infer_instance
  | effect hpq α β ℓS w η rest ih =>
      intro tail
      let := ih tail
      let := finiteDimensional_sources_prepWord hpq η m (rest.stackApp m tail)
      exact finiteDimensional_sources_comp (rest.prepStack m tail) (prepWord hpq η m _)
end PartyChain
/-- A gate's actual retained source inventory is finite-dimensional.
Source: polynomial-PEPS, `04-compression.tex:103–112` and `199–217`. -/
theorem finiteDimensional_sources_prepGate {a b : Layout P} (m : ℕ) (L : PartyGate a b) :
    FiniteDimensional ℂ (Mem (prepGate m L).sources.layout).carrier := by
  induction L with
  | nil => change FiniteDimensional ℂ ℂ; infer_instance
  | cons q L ih =>
      let := ih
      let := q.2.finiteDimensional_sources_prepStack m (gateOut m L)
      exact finiteDimensional_sources_comp (prepGate m L) (q.2.prepStack m _)

namespace EffectCircuit
/-- The auxiliary memory consists of the actual finite Euclidean source pairs
created by gate replacement. Private memories need not be finite-dimensional.
Source: polynomial-PEPS, `04-compression.tex:199–217`. -/
theorem finiteDimensional_auxiliary {a b : Layout P} (w : EffectCircuit a b) (m : ℕ) :
    FiniteDimensional ℂ (Mem (w.auxiliary m)).carrier := by
  induction w with
  | id => change FiniteDimensional ℂ ℂ; infer_instance
  | comp w v ihw ihv =>
      let := ihw
      let := ihv
      exact finiteDimensional_mem_append (w.auxiliary m) (v.auxiliary m)
  | localMap => change FiniteDimensional ℂ ℂ; infer_instance
  | @gate C _ owner a b L tail =>
      let := finiteDimensional_sources_prepGate m L
      exact (Layout.mapOwnerIso owner (prepGate m L).sources.layout).toLinearEquiv.finiteDimensional
  | swap => change FiniteDimensional ℂ ℂ; infer_instance
  | frame t w ih => exact ih
end EffectCircuit

/-- Arbitrarily chosen orthonormal coordinates of the entire retained auxiliary
memory. Its dimension is finite and is not bounded a priori.
Source: polynomial-PEPS 04-compression.tex, lines 210–227. -/
def auxiliaryCoordinates (rs : Layout P) [FiniteDimensional ℂ (Mem rs).carrier] :
    Mem rs ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ (Mem rs).carrier)) :=
  (stdOrthonormalBasis ℂ (Mem rs).carrier).repr

namespace EffectCircuit
variable {Phys Env : Type*} [Fintype Phys] [Fintype Env]

/-- The physical density of the actual original circuit, with subnormalization retained.
Source: polynomial-PEPS 04-compression.tex, lines 218–227. -/
def originalPhysicalDensity {a b : Layout P} (w : EffectCircuit a b)
    (K : Mem b →L[ℂ] EuclideanSpace ℂ (Phys × Env)) (x : Mem a) : Matrix Phys Phys ℂ :=
  Matrix.partialTraceRight (Matrix.euclideanOuterProduct (K (w.eval x)) (K (w.eval x)))

/-- The physical density of the constructed source-only replacement, after discarding
its actual retained auxiliary registers and the original environment.
Source: polynomial-PEPS 04-compression.tex, lines 218–227. -/
def replacementPhysicalDensity {r : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    {a b : Layout P} (w : EffectCircuit a b) (hw : w.IsAllowed)
    (hb : w.IsExpansionBounded r S)
    (K : Mem b →L[ℂ] EuclideanSpace ℂ (Phys × Env)) (x : Mem a) : Matrix Phys Phys ℂ := by
  let := w.finiteDimensional_auxiliary (stackLength r S δ)
  let y := extendedPhysicalReadout (auxiliaryCoordinates (w.auxiliary (stackLength r S δ))) K
    ((w.replacement hδ hw hb).eval x)
  exact Matrix.partialTraceRight (Matrix.euclideanOuterProduct y y)

/-- The source-only replacement has physical density error at most four times
the gate budget times the number of original expanded occurrences. The circuit,
auxiliary vector and final readout are all constructed explicitly.
Source: polynomial-PEPS 04-compression.tex, lines 199–229. -/
theorem rectangularTraceNorm_replacement_density_sub_le [DecidableEq Phys]
    {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) {a b : Layout P}
    (w : EffectCircuit a b) (hw : w.IsAllowed) (hb : w.IsExpansionBounded r S)
    (K : Mem b →L[ℂ] EuclideanSpace ℂ (Phys × Env)) (hK : ‖K‖ ≤ 1)
    (x : Mem a) (hx : ‖x‖ ≤ 1) :
    Matrix.rectangularTraceNorm (w.replacementPhysicalDensity hδ hw hb K x -
      w.originalPhysicalDensity K x) ≤ 4 * δ * w.expandedGateCount := by
  let m := stackLength r S δ
  let := w.finiteDimensional_auxiliary m
  have hR := SourceCircuit.norm_eval_le_one _ (w.isAllowed_replacement hδ hw hb)
  have hu : ‖(w.replacement hδ hw hb).eval x‖ ≤ 1 :=
    ((w.replacement hδ hw hb).eval.le_opNorm_of_le hx).trans
      (by simpa only [mul_one] using hR)
  have hv : ‖w.eval x‖ ≤ 1 := (w.eval.le_opNorm_of_le hx).trans
    (by simpa only [mul_one] using w.norm_eval_le_one hw)
  have herr : ‖(w.replacement hδ hw hb).eval x -
      (appendIso (w.auxiliary m) b).symm (w.auxiliaryVector m ⊗ₜ[ℂ] w.eval x)‖ ≤
      2 * δ * w.expandedGateCount := by
    rw [← w.referenceEval_apply m x]
    exact ((w.replacement hδ hw hb).eval - w.referenceEval m).le_opNorm_of_le hx |>.trans
      (by simpa only [mul_one] using w.norm_replacement_sub_reference_le hδ hw hb)
  have he := rectangularTraceNorm_extendedPhysicalReadout_error_le
    (auxiliaryCoordinates (w.auxiliary m)) K hK (w.auxiliaryVector m) (w.eval x)
    ((w.replacement hδ hw hb).eval x) (w.norm_auxiliaryVector hw m) hv hu herr
  simpa only [replacementPhysicalDensity, originalPhysicalDensity,
    show 2 * (2 * δ * (w.expandedGateCount : ℝ)) = 4 * δ * w.expandedGateCount by ring] using he
end EffectCircuit
end TNLean.PEPS.PairEffect
