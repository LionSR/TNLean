# Actual tensor extension along a finite physical embedding

The new Core/PhysicalEmbedding module proves that extending a periodic tensor
by zero along a finite physical embedding extends its actual Euclidean MPS
state by zero along the induced configuration embedding. The statement uses
Function.extend directly and does not introduce another tensor construction.
It holds at every chain length, including zero, and allows empty alphabets.
The bond dimension is unchanged.

Scouting covered Core/PhysicalRotation and ParentHamiltonian/PhysicalEmbedding.
Those existing results describe arbitrary matrix physical rotations and their
local ground spaces. The new state identity reuses the existing
MPSTensor.mpv_reindexPhysical on image configurations. Outside the image, a
missing physical letter splits the word into prefix, zero letter, and suffix;
Kraus.evalWord_append and evalWord_cons give a zero product. There is no new
word-product expansion, tensor-power sum, or ground-space assumption.

The Euclidean isometry is the shared Algebra/EuclideanExtendByZero owner.
No parent-Hamiltonian import is introduced into Core. The single public result
has a separate scope-faithful Blueprint statement, marked notready. This is a
bounded ingredient for the SPWC10 Theorem 5 finite-prefix investigation, not a
full all-volume model or a source counterexample claim.

Native import, Blueprint, formatting, integrity and source checks are recorded
in the PR. No local Lean, Lake, elaboration or build was run. Kernel acceptance
remains pending; source/API review does not establish proof acceptance.
