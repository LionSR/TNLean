# GHZ sector probabilities and selected-vector circuit conversion

## Mathematical scope

This extends the discussion/outlook analysis of arXiv:2307.01696v2 and the
open same-phase scope question in issue #8469. It does not refute every phase
definition. The proved statement concerns closed nearest-neighbor unitary
circuits on the physical ring, with every gate included in the depth.
Measurements, classical feedforward, and added ancillas are not hypotheses or
conclusions of this theorem.

The repeated-block source tensor has diagonal letters `(1,1,0)` and `(0,0,1)`.
Its coefficient two is the trace multiplicity of two identical blocks with
copy weight one, not a scalar weight two raised to the chain length. The
normalized periodic states are exactly `(2|0^N>+|1^N>)/sqrt(5)` and balanced GHZ.
Their entire local boundary-generated spaces and canonical parent Hamiltonians
agree, not merely the dimensions of those spaces.

For `N > 4T+4`, sites `0` and `2T+2` have disjoint radius-T backward cones,
and site `T+1` lies outside both. Off-diagonal product-branch entries vanish at
that site. The weighted covariance is bounded by `16/25`, whereas balanced
GHZ has Pauli-Z covariance one. Phase-aligned vector distance `eta` changes
this covariance by at most `6 eta`; thus `eta >= 3/50` and overlap error
`1-|<U psi,phi>| = eta^2/2 >= 9/5000`. No trace-distance representation is used.

## Library placement and simplification

- Generic support entries, expectations, ring geometry, and weighted GHZ
  correlations live in `Circuit/` and import no MPS modules.
- `QuantumCircuit.ghzState` and `ghzState_apply` retain their names and bodies;
  their lightweight definition is moved from `Circuit/Measurement/GHZ` to
  `Circuit/GHZState`, which the measurement module imports.
- The arithmetic proof of `MPSPreparation.isSeparatedBy_window` is extracted
  to `QuantumCircuit.isSeparatedBy_of_val_bounds`; the existing window theorem
  now invokes it. No parallel ring-distance proof is retained.
- The final overlap-error theorem uses the existing phase-alignment result
  `MPSPreparation.exists_norm_sub_smul_sq_eq`.

## Validation boundary

The circuit support, expectation, weighted-GHZ, ring-separation, explicit-vector
infidelity modules and regression examples have direct strict Lean checks from
the actual production imports, using one thread and the package's Lean options.
Reused artifacts were audited against exact source bodies, the Lean toolchain,
and the reachable QIC source at the manifest pin. No cold Mathlib, Brouwer, or
QIC build was started.

The source-tensor parent module's complete production import closure requires
QIC fixed-point/spectral artifacts absent from the warm local cache. Its theorem
bodies were checked in a separately identified probe using exact extracted
source definitions and exact warmed core/parent imports. That probe is not a
full production-import or root build. Exact-head CI must establish the complete
import closure, downstream measurement/window regressions, and root build before
merge. This distinction applies to the validation report, not to a weakened
mathematical statement.

The typed tenkz diagram is a scalar contraction over disjoint spaces I, J, R,
with R nonempty: nine tensor nodes, six physical wires, no open legs. The
regression audits all connections and the empty boundary signature. The rendered
PDF was visually inspected. The chapter uses the phase-distance proof, consistent
with the formal theorem.
