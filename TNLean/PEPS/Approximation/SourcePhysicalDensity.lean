/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCompressedDensity
import QICLean.Channel.PartialTrace

/-!
# Physical density after tracing retained garbage

The polynomial-PEPS manuscript explicitly permits arbitrary finite private and
resource dimensions (`04-compression.tex`, lines 5–6) and states that every Hilbert
space in this section is finite dimensional, without a size bound on unspecified
dimensions (lines 17–19). Discarded registers remain in the memory until the final
partial trace (lines 23–30). Thus finite orthonormal coordinates on the actual
input, physical output, and garbage memories impose no additional restriction.

The joint output basis is obtained from the physical and garbage bases through
the canonical append isometry. The physical operator is the partial trace of
the actual full circuit output. The source-subset identity therefore descends
to this physical operator by linearity, without a garbage-dimension factor.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–383.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-source-corrections-sourcephysicaldensity-01
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.physicalDensity

Provenance-ID: 8769-source-corrections-sourcephysicaldensity-02
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.physicalCorrectedSourceTerm

Provenance-ID: 8769-source-corrections-sourcephysicaldensity-03
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.physicalSourceReplacedDensity

Provenance-ID: 8769-source-corrections-sourcephysicaldensity-04
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.physicalSourceReplacedDensity_exact

Provenance-ID: 8769-source-corrections-sourcephysicaldensity-05
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.physicalSourceReplacedDensity_sub_exact

Provenance-ID: 8769-source-corrections-sourcephysicaldensity-06
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.rectangularTraceNorm_physicalSourceReplacedDensity_sub_le

-/

noncomputable section
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit

/-- The fixed physical and garbage bases give coordinates on the actual final layout. -/
private def physicalOutputBasis {P x d : Type} [Fintype x] [Fintype d]
    (physical garbage : Layout P)
    (bPhysical : OrthonormalBasis x ℂ (Mem physical))
    (bGarbage : OrthonormalBasis d ℂ (Mem garbage)) :
    OrthonormalBasis (x × d) ℂ (Mem (physical ++ garbage)) :=
  (bPhysical.tensorProduct bGarbage).map (appendIso physical garbage).symm

/-- The actual circuit output operator after tracing its retained garbage registers.
The input matrix is arbitrary; for a circuit satisfying the paper's hypotheses,
a normalized pure input gives its physical density.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 4–19 and 23–30. -/
def physicalDensity {P n x d : Type} [Fintype n] [Fintype x] [Fintype d]
    {a : Layout P} (physical garbage : Layout P) (w : SourceCircuit a (physical ++ garbage))
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis x ℂ (Mem physical))
    (bGarbage : OrthonormalBasis d ℂ (Mem garbage)) (ρ : Matrix n n ℂ) :
    Matrix x x ℂ := by
  classical
  let bOut := physicalOutputBasis physical garbage bPhysical bGarbage
  let M := LinearMap.toMatrix bIn.toBasis bOut.toBasis w.eval.toLinearMap
  exact Matrix.partialTraceRight (M * ρ * Mᴴ)

/-- The physical corrected term traces the actual retained garbage, without changing
its original source-occurrence or local-label indices.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–383. -/
def physicalCorrectedSourceTerm {P n x d : Type} [Fintype n] [Fintype x] [Fintype d]
    {a : Layout P} (physical garbage : Layout P) (w : SourceCircuit a (physical ++ garbage))
    (S : Finset (sourceLocations w))
    (E : ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis x ℂ (Mem physical))
    (bGarbage : OrthonormalBasis d ℂ (Mem garbage)) (ρ : Matrix n n ℂ) :
    Matrix x x ℂ :=
  Matrix.partialTraceRight (correctedSourceTerm w S E bIn
    (physicalOutputBasis physical garbage bPhysical bGarbage) ρ)

/-- Source replacement in the actual circuit followed by its physical partial trace.
This definition precedes, and does not assume, the corrected-subset identity.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–383. -/
def physicalSourceReplacedDensity {P n x d : Type} [Fintype n] [Fintype x] [Fintype d]
    {a : Layout P} (physical garbage : Layout P) (w : SourceCircuit a (physical ++ garbage))
    (Y : ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis x ℂ (Mem physical))
    (bGarbage : OrthonormalBasis d ℂ (Mem garbage)) (ρ : Matrix n n ℂ) :
    Matrix x x ℂ :=
  Matrix.partialTraceRight (sourceReplacedDensity w Y bIn
    (physicalOutputBasis physical garbage bPhysical bGarbage) ρ)

/-- Exact local source operators recover the physical output of the actual circuit.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–355. -/
theorem physicalSourceReplacedDensity_exact {P n x d : Type}
    [Fintype n] [Fintype x] [Fintype d]
    {a : Layout P} (physical garbage : Layout P) (w : SourceCircuit a (physical ++ garbage))
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis x ℂ (Mem physical))
    (bGarbage : OrthonormalBasis d ℂ (Mem garbage)) (ρ : Matrix n n ℂ) :
    physicalSourceReplacedDensity physical garbage w (exactSourceMatrix w)
      bIn bPhysical bGarbage ρ = physicalDensity physical garbage w bIn bPhysical bGarbage ρ := by
  classical
  unfold physicalSourceReplacedDensity physicalDensity
  rw [sourceReplacedDensity_exact]

open Classical in
/-- The physical replacement error is exactly the sum of the nonempty corrected
terms after tracing the actual garbage. No dimension factor is introduced.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-subset-expansion`,
`04-compression.tex`, lines 338–383. -/
theorem physicalSourceReplacedDensity_sub_exact {P n x d : Type}
    [Fintype n] [Fintype x] [Fintype d]
    {a : Layout P} (physical garbage : Layout P) (w : SourceCircuit a (physical ++ garbage))
    (E : ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis x ℂ (Mem physical))
    (bGarbage : OrthonormalBasis d ℂ (Mem garbage)) (ρ : Matrix n n ℂ) :
    physicalSourceReplacedDensity physical garbage w (E + exactSourceMatrix w)
        bIn bPhysical bGarbage ρ - physicalDensity physical garbage w bIn bPhysical bGarbage ρ =
      ∑ S ∈ (Finset.univ : Finset (Finset (sourceLocations w))).erase ∅,
        physicalCorrectedSourceTerm physical garbage w S E bIn bPhysical bGarbage ρ := by
  simpa only [map_sub, map_sum, physicalSourceReplacedDensity, physicalDensity,
    physicalCorrectedSourceTerm, Matrix.partialTraceRightLM, LinearMap.coe_mk,
    AddHom.coe_mk] using
    congrArg (Matrix.partialTraceRightLM (α := x) (β := d))
      (sourceReplacedDensity_sub_exact w E bIn
        (physicalOutputBasis physical garbage bPhysical bGarbage) ρ)

open Classical in
/-- The physical trace-norm error is bounded by the sum of the corrected physical
terms, with no dependence on the dimension of the retained garbage.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-total-error`. -/
theorem rectangularTraceNorm_physicalSourceReplacedDensity_sub_le {P n x d : Type}
    [Fintype n] [Fintype x] [Fintype d]
    {a : Layout P} (physical garbage : Layout P) (w : SourceCircuit a (physical ++ garbage))
    (E : ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis x ℂ (Mem physical))
    (bGarbage : OrthonormalBasis d ℂ (Mem garbage)) (ρ : Matrix n n ℂ) :
    Matrix.rectangularTraceNorm
        (physicalSourceReplacedDensity physical garbage w (E + exactSourceMatrix w)
          bIn bPhysical bGarbage ρ - physicalDensity physical garbage w bIn bPhysical bGarbage ρ) ≤
      ∑ S ∈ (Finset.univ : Finset (Finset (sourceLocations w))).erase ∅,
        Matrix.rectangularTraceNorm
          (physicalCorrectedSourceTerm physical garbage w S E bIn bPhysical bGarbage ρ) := by
  rw [physicalSourceReplacedDensity_sub_exact]
  exact Matrix.rectangularTraceNorm_sum_le _ _

end TNLean.PEPS.PairEffect.SourceCircuit
