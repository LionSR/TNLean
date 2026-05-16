/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorIrreducibility.ProjectionOrtho
import TNLean.MPS.CanonicalForm.SectorIrreducibility.OrbitSum
import TNLean.MPS.CanonicalForm.SectorIrreducibility.HLiftCore
import TNLean.MPS.CanonicalForm.SectorIrreducibility.HLift

/-!
# Sector irreducibility helpers

The sector-irreducibility argument for cyclic decompositions starts from a
partition of unity by orthogonal projections. Adjoint fixed projections preserve
their corners, orbit sums transport sector-supported operators around the cycle,
and the fixed-point upgrade turns corner preservation into fixedness. These
facts give irreducibility on each cyclic-sector corner.

## Main statements

The main results give pairwise orthogonality from a projection-valued partition
of unity, fixedness of orbit sums, recovery of sector-supported operators by
compression, fixed-point-algebra rigidity for irreducible cyclic decompositions,
and irreducibility of the corner maps.

## Tags

matrix product states, cyclic sectors, irreducibility
-/
