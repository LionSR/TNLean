# Full periodic kernel of the physical-sector sum

Context: #10386. Combines #10412 actual state decomposition with the actual
local/periodic component projection transport, without introducing a supplied
global kernel decomposition or a dynamics relation.

For arbitrary local spaces S and T, exhaustive physical alphabets of dimensions
a and b, and M ≥ R ≥ 2, the actual complementary-projector Hamiltonian of the
sum of the embedded local spaces has kernel exactly equal to the sum of the
embedded component Hamiltonian kernels.

The forward inclusion derives the actual coefficient restrictions x and y,
uses the proved decomposition ψ=Ex+Fy, then applies the independently proved
actual component kernel equivalence. Submodule map and sum witnesses yield
the inclusion. The reverse inclusion extracts the actual map/sum witnesses
and applies the same component equivalence. Word embedding disjointness is
derived from the two standard finite-alphabet inclusions; it is not supplied.

The theorem is generic in the actual local spaces. It therefore permits the
Weyl boundary range and pure particle line to be inserted directly when their
component classifications are available. It is not itself the full proposed
finite-prefix model, and it makes no source-counterexample claim.

No local Lean, Lake, build, elaboration or checkdecls is run, as requested.
The public statement and its Blueprint proof remain notready. Native checks
and bounded source review do not replace hosted kernel acceptance. No
persistent Lean fixtures are introduced.

Independent bounded source/API review found no concrete mismatch in the
finite-alphabet disjointness, coefficient decomposition, equation transport,
component kernel equivalence, or map/sum witnesses in either inclusion.
Native import, role, full synchronization, TeX, prose, integrity, size, tactic
and whitespace checks pass.
