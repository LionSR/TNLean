/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FiniteInputMemory
import TNLean.PEPS.Approximation.FamilyPhysicalReadout

/-!
# Original data of a distributed construction

The data consist of the original party memories, a normalized product input,
the intended physical outputs, the private registers retained until the final
trace, and the actual chronological circuit. The original party memories and
the discarded output registers are finite-dimensional; no numerical bound on
private dimensions is imposed. Resource bounds and
approximation conclusions are not part of these data.

**Local fix (nonempty parties):** A distributed construction has at least one
party. The scalar-absorption step of the source proof places scalar factors in
an existing local tensor. For zero parties the empty-node network has value one,
whereas an empty-participant gate can change the scalar output. This convention
is recorded in `docs/paper-gaps/polypeps_nonempty_parties.tex`. The general
circuit type and its empty-participant gates remain unrestricted.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 17–30,
137–151 and 565–578; `01-preliminaries.tex`, lines 5–7.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-original-sampling-distributedconstruction-01
TNLean.PEPS.PairEffect.DistributedConstruction
Provenance-ID: 8769-original-sampling-distributedconstruction-02
TNLean.PEPS.PairEffect.DistributedConstruction.input
Provenance-ID: 8769-original-sampling-distributedconstruction-03
TNLean.PEPS.PairEffect.DistributedConstruction.physicalDensity
Provenance-ID: 8769-original-sampling-distributedconstruction-04
TNLean.PEPS.PairEffect.DistributedConstruction.physicalDensity_posSemidef
Provenance-ID: 8769-original-sampling-distributedconstruction-05
TNLean.PEPS.PairEffect.DistributedConstruction.trace_physicalDensity_le_one
-/


noncomputable section
open scoped ComplexOrder
namespace TNLean.PEPS.PairEffect

/-- The original data of a distributed construction on a finite nonempty party
set. The fields describe the source's input, circuit and retained outputs;
they do not assume a compressed representation or an error estimate.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 17–30 and 137–151. -/
structure DistributedConstruction (P : Type) [Fintype P] where
  /-- An existing party at which scalar factors can be absorbed.
  Source: `04-compression.tex`, lines 565–578; see the module convention. -/
  nonemptyParties : Nonempty P
  /-- Each party's whole original private memory.
  Source: `04-compression.tex`, lines 23–30 and 137–139. -/
  initialSpace : P → HSpace
  /-- Private dimensions are finite but need not satisfy a numerical bound.
  Source: `04-compression.tex`, lines 17–19. -/
  finite_initialSpace : ∀ p, FiniteDimensional ℂ (initialSpace p)
  /-- The original vector at each party.
  Source: `04-compression.tex`, lines 137–139. -/
  initialVector : ∀ p, initialSpace p
  /-- The original input is a product of normalized party vectors.
  Source: `04-compression.tex`, lines 137–139. -/
  norm_initialVector : ∀ p, ‖initialVector p‖ = 1
  /-- The intended physical dimension at each party.
  Source: `04-compression.tex`, lines 148–151. -/
  physicalDimension : P → ℕ
  /-- The order of the physical registers in the circuit output.
  Source: `04-compression.tex`, lines 23–30 and 148–151. -/
  physicalOrder : List P
  /-- Each party has exactly one intended physical register.
  Source: `04-compression.tex`, lines 148–151. -/
  physicalOrder_nodup : physicalOrder.Nodup
  /-- The physical output includes every original party.
  Source: `04-compression.tex`, lines 148–151. -/
  mem_physicalOrder : ∀ p, p ∈ physicalOrder
  /-- The actual private registers retained until the final trace.
  Source: `04-compression.tex`, lines 27–30 and 150–151. -/
  privateOutput : Layout P
  /-- Each discarded register is finite-dimensional, without a size bound.
  Source: `04-compression.tex`, lines 17–19 and 150–151. -/
  finite_privateOutput : ∀ r ∈ privateOutput, FiniteDimensional ℂ r.space
  /-- The original contraction circuit, with its actual gate expansions.
  Source: `04-compression.tex`, lines 23–43 and 137–151. -/
  circuit : OriginalCircuit (ProductInput.wholePartyLayout initialSpace)
    (familyPhysicalLayout physicalDimension physicalOrder ++ privateOutput)

namespace DistributedConstruction
variable {P : Type} [Fintype P]

/-- The original normalized product input of the construction.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139. -/
def input (C : DistributedConstruction P) :
    ProductInput (ProductInput.wholePartyLayout C.initialSpace) :=
  ProductInput.ofAllParties C.initialSpace C.initialVector C.norm_initialVector

/-- The actual physical density of the original circuit, obtained by tracing
its retained private registers in finite orthonormal coordinates. No division
by the output norm is made.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 150–153. -/
def physicalDensity (C : DistributedConstruction P) :
    Matrix ((p : P) → Fin (C.physicalDimension p))
      ((p : P) → Fin (C.physicalDimension p)) ℂ := by
  classical
  letI := Layout.finiteDimensional_mem_of_registers C.privateOutput C.finite_privateOutput
  let J := familyLabelledPhysicalReadout C.physicalDimension C.physicalOrder
    C.physicalOrder_nodup C.mem_physicalOrder C.privateOutput
  exact Matrix.partialTraceRight (Matrix.euclideanOuterProduct
    (J (C.circuit.eval C.input.vector)) (J (C.circuit.eval C.input.vector)))

/-- The original physical density is positive semidefinite.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 152–153. -/
theorem physicalDensity_posSemidef (C : DistributedConstruction P) :
    C.physicalDensity.PosSemidef := by
  classical
  exact (Matrix.posSemidef_vecMulVec_self_star _).partialTraceRight

open scoped Classical in
/-- The trace of the original physical density is at most one; the output is
not required to have norm one.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 152–153. -/
theorem trace_physicalDensity_le_one (C : DistributedConstruction P) :
    C.physicalDensity.trace ≤ 1 := by
  classical
  let := Layout.finiteDimensional_mem_of_registers C.privateOutput C.finite_privateOutput
  let J : Mem (familyPhysicalLayout C.physicalDimension C.physicalOrder ++ C.privateOutput)
      ≃ₗᵢ[ℂ] EuclideanSpace ℂ (((p : P) → Fin (C.physicalDimension p)) ×
        Fin (Module.finrank ℂ (Mem C.privateOutput))) :=
    familyLabelledPhysicalReadout C.physicalDimension C.physicalOrder
      C.physicalOrder_nodup C.mem_physicalOrder C.privateOutput
  change (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
    (J (C.circuit.eval C.input.vector)) (J (C.circuit.eval C.input.vector)))).trace ≤ 1
  rw [Matrix.trace_partialTraceRight, Matrix.euclideanOuterProduct,
    Matrix.trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K]
  rw [J.norm_map]
  norm_cast
  apply Complex.real_le_real.mpr
  apply pow_le_one₀ (norm_nonneg _)
  have hC : ‖C.circuit.eval‖ ≤ 1 := by
    simpa only [C.circuit.eval_produce] using
      C.circuit.produce.norm_eval_le_one C.circuit.isAllowed_produce
  exact (C.circuit.eval.le_opNorm_of_le C.input.norm_vector.le).trans
    (by simpa only [mul_one] using hC)

end DistributedConstruction
end TNLean.PEPS.PairEffect
