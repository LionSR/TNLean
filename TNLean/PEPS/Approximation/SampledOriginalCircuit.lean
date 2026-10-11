/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSourceSampling
import TNLean.PEPS.Approximation.PhysicalFirstReadout
import TNLean.PEPS.Approximation.AuxiliaryRegisterFiniteness

/-!
# Sampling the actual replacement of an original circuit

The original circuit's expansion and lifetime bounds control its actual
physical-first source replacement. Its retained auxiliary registers are finite
by construction, and the private registers require no numerical dimension bound.

Source: polynomial-PEPS, `04-compression.tex`, lines 17–19, 137–151, 199–229 and 342–381.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/

noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped Matrix ComplexConjugate NNReal
open TNLean.PEPS.Approximation
namespace TNLean.PEPS.PairEffect
variable {P : Type}

/-- The triangle inequality through an intermediate physical density.
Source: polynomial-PEPS, `04-compression.tex`, lines 137–151 and 342–381. -/
private theorem rectangularTraceNorm_sub_le_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    {A C Z : Matrix ι ι ℂ} {s t : ℝ}
    (hAC : Matrix.rectangularTraceNorm (A - C) ≤ s)
    (hCZ : Matrix.rectangularTraceNorm (C - Z) ≤ t) :
    Matrix.rectangularTraceNorm (A - Z) ≤ s + t :=
  (congrArg Matrix.rectangularTraceNorm (sub_add_sub_cancel A C Z)).symm.trans_le
    ((Matrix.rectangularTraceNorm_add_le (A - C) (C - Z)).trans (add_le_add hAC hCZ))

namespace OriginalCircuit

/-- Increasing a monomial-count bound preserves the original expansion condition.
Source: polynomial-PEPS, `04-compression.tex`, lines 137–151. -/
theorem isMonomialBounded_mono {a b : Layout P} (w : OriginalCircuit a b)
    {K K' : ℕ} (h : w.IsMonomialBounded K) (hKK : K ≤ K') :
    w.IsMonomialBounded K' := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw h.1, ihv h.2⟩
  | privateMap => trivial
  | nonprivateGate => exact h.trans hKK
  | swap => trivial
  | frame r w ih => exact ih h

/-- The finite original chronology has some finite monomial-count bound.
This bound is derived from its original gate lists, without an additional
hypothesis. Source: polynomial-PEPS, `04-compression.tex`, lines 137–151. -/
theorem exists_isMonomialBounded {a b : Layout P} (w : OriginalCircuit a b) :
    ∃ K, w.IsMonomialBounded K := by
  induction w with
  | id => exact ⟨0, trivial⟩
  | comp w v ihw ihv =>
      obtain ⟨K, hK⟩ := ihw
      obtain ⟨J, hJ⟩ := ihv
      exact ⟨K + J, w.isMonomialBounded_mono hK (Nat.le_add_right K J),
        v.isMonomialBounded_mono hJ (Nat.le_add_left J K)⟩
  | privateMap => exact ⟨0, trivial⟩
  | nonprivateGate owner hC L hL hG tail => exact ⟨L.length, le_rfl⟩
  | swap => exact ⟨0, trivial⟩
  | frame r w ih => exact ih

/-- The actual physical-first replacement has the original coefficient-sum
bound. A finite monomial bound is obtained from the original gate lists and
is used only to invoke the existing expansion estimate.
Source: polynomial-PEPS, `04-compression.tex`, lines 199–212 and 229. -/
theorem sum_norm_branchCoefficient_physicalFirstReplacement_le
    {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) {a : Layout P}
    (physical priv : Layout P) (w : OriginalCircuit a (physical ++ priv))
    (hb : w.IsExpansionBounded r S)
    (g : (w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)).gateLocations) :
    let R := w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)
    (∑ ξ : R.branchLabels g, ‖R.branchCoefficient g ξ‖) ≤ S := by
  obtain ⟨K, hK⟩ := w.exists_isMonomialBounded
  exact ((SourceCircuit.isExpansionBounded_physicalFirstOutput
    (w.produce.auxiliary (stackLength r S δ)) physical priv _ (K * stackLength r S δ ^ r) S).mpr
      (isExpansionBounded_replacement hδ w hb hK)).at_gate g |>.2

open Classical in
/-- An actual Gaussian sample of the physical-first source replacement
approximates the original circuit's physical density with error at most
`3 * ε / 4`. Each original party is prepared in one normalized whole-memory
vector, and its physical dimension remains the original value `physicalDim p`.
Private register dimensions are finite but have no numerical bound.
Source: polynomial-PEPS, `04-compression.tex`, lines 17–19, 137–151, 199–229 and 342–381. -/
theorem exists_physicalFirst_sourceSample_original_error_le
    [Fintype P] {n : Type} [Fintype n]
    (H : P → HSpace) (x : ∀ p, H p) (hx : ∀ p, ‖x p‖ = 1)
    (physicalDim : P → ℕ) (ps : List P) (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps)
    (priv : Layout P)
    (w : OriginalCircuit (ProductInput.wholePartyLayout H)
      (familyPhysicalLayout physicalDim ps ++ priv))
    {r M lifetime : ℕ} (B D : ℝ≥0) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (hb : w.IsExpansionBounded r (B : ℝ)) (hcount : w.nonprivateCount ≤ M)
    (hlifetime : ∀ p, w.participationCount p ≤ lifetime)
    (hphysical : ∀ p, (physicalDim p : ℝ≥0) ≤ D)
    (hpriv : ∀ t ∈ priv, FiniteDimensional ℂ t.space.carrier)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (bIn : OrthonormalBasis n ℂ (Mem (ProductInput.wholePartyLayout H))) :
    let ψ := ProductInput.ofAllParties H x hx
    let δ := sourceGateBudget ε M
    let m := stackLength r (B : ℝ) δ
    letI := Layout.finiteDimensional_mem_of_registers priv hpriv
    letI := w.produce.finiteDimensional_auxiliary m
    let R := w.produce.physicalFirstReplacement (sourceGateBudget_pos hε M)
      (familyPhysicalLayout physicalDim ps) priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r (B : ℝ)).mpr hb)
    let bPhysical := familyLabelledPhysicalBasis physicalDim ps hps hcover
    let bDiscard := exchangedGarbageBasis (w.produce.auxiliary m) priv
      (stdOrthonormalBasis ℂ (Mem (w.produce.auxiliary m)).carrier)
      (stdOrthonormalBasis ℂ (Mem priv).carrier)
    let Q := (B : ℝ) ^ (4 * lifetime) * (D : ℝ) ^ 4
    let k := sourceSamplingCount (Fintype.card R.sourceLocations) Q ε
    let ρ := Matrix.euclideanOuterProduct (bIn.repr ψ.vector) (bIn.repr ψ.vector)
    ∃ (lam : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Fin (min (R.sourceDims s).1 (R.sourceDims s).2) → ℝ)
      (E : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Matrix (Fin (R.sourceDims s).1) (Fin (min (R.sourceDims s).1 (R.sourceDims s).2)) ℂ)
      (F : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Matrix (Fin (R.sourceDims s).2) (Fin (min (R.sourceDims s).1 (R.sourceDims s).2)) ℂ),
      (∀ s ξ, (∀ j, 0 ≤ lam s ξ j) ∧ ∑ j, lam s ξ j = 1 ∧
        (E s ξ)ᴴ * E s ξ = 1 ∧ (F s ξ)ᴴ * F s ξ = 1 ∧
        ambientSchmidtVector (lam s ξ) (E s ξ) (F s ξ) =
          (SourceCircuit.sourceCoordinates R s ξ).ofLp) ∧
      ∃ ω : SourceCircuit.SourceGaussianSamples R k,
        Matrix.rectangularTraceNorm
          (SourceCircuit.physicalSourceReplacedDensity (familyPhysicalLayout physicalDim ps)
            (w.produce.auxiliary m ++ priv) R
            (fun s ξ ζ ↦ SourceCircuit.sampledSourceMatrix R k lam E F s ξ ζ ω)
            bIn bPhysical bDiscard ρ -
            Matrix.partialTraceRight (Matrix.euclideanOuterProduct
              (familyLabelledPhysicalReadout physicalDim ps hps hcover priv (w.eval ψ.vector))
              (familyLabelledPhysicalReadout physicalDim ps hps hcover priv
                (w.eval ψ.vector)))) ≤ 3 * ε / 4 := by
  intro ψ δ m R bPhysical bDiscard Q k ρ
  have hR : R.IsAllowed :=
    (SourceCircuit.isAllowed_physicalFirstOutput (w.produce.auxiliary m)
      (familyPhysicalLayout physicalDim ps) priv _).mpr
      (w.produce.isAllowed_replacement (sourceGateBudget_pos hε M) w.isAllowed_produce
        ((w.isExpansionBounded_produce_iff r (B : ℝ)).mpr hb))
  have hfinite : ∀ t ∈ w.produce.auxiliary m ++ priv,
      FiniteDimensional ℂ t.space.carrier :=
    w.produce.finiteDimensional_auxiliary_private_registers m priv hpriv
  have hlt : ∀ p, R.participationCount p ≤ lifetime := fun p ↦
    (SourceCircuit.participationCount_physicalFirstOutput (w.produce.auxiliary m)
      (familyPhysicalLayout physicalDim ps) priv _ p).trans_le
      (w.participationCount_replacement_le (sourceGateBudget_pos hε M) hb hlifetime p)
  have hcoeff : ∀ g : R.gateLocations,
      (∑ ξ : R.branchLabels g, ‖R.branchCoefficient g ξ‖) ≤ (B : ℝ) :=
    w.sum_norm_branchCoefficient_physicalFirstReplacement_le (sourceGateBudget_pos hε M)
      (familyPhysicalLayout physicalDim ps) priv hb
  obtain ⟨lam, E, F, hframes, ω, hω⟩ :=
    SourceCircuit.exists_sourceSample_lifetime_error_le physicalDim ps hps hcover R hR hfinite
      lifetime B D hB hD hlt hcoeff hphysical ε hε hεone ψ.prepare
      ψ.isAllowed_prepare ψ.sources_prepare bIn bPhysical bDiscard
  rw [ψ.eval_prepare] at hω
  let : DecidableEq ((p : P) → Fin (physicalDim p)) :=
    fun a b ↦ Classical.propDecidable (a = b)
  have hhalf :=
    (letI := Layout.finiteDimensional_mem_of_registers priv hpriv;
      w.rectangularTraceNorm_physicalFirst_density_sub_le_half hε
        (familyPhysicalLayout physicalDim ps) priv hb hcount bIn bPhysical
        ψ.vector ψ.norm_vector.le)
  simp only [SourceCircuit.physicalSourceReplacedDensity_exact] at hhalf
  refine ⟨lam, E, F, hframes, ω, ?_⟩
  calc
    _ ≤ ε / 4 + ε / 2 := rectangularTraceNorm_sub_le_sum hω hhalf
    _ = 3 * ε / 4 := by ring

end OriginalCircuit
end TNLean.PEPS.PairEffect
