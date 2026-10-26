# Permutation-matrix unitarity in QICLean

The theorem `Equiv.Perm.permMatrix_mem_unitaryGroup` states that a complex
permutation matrix is unitary. This finite-dimensional matrix fact now belongs
to `QICLean/Algebra/PermutationMatrixUnitary.lean`, where it is also used in the
construction of a unitary having trace pairing zero with a Hermitian matrix.

The declaration, including its proof, is unchanged. The original file
`TNLean/Algebra/PermutationMatrixUnitary.lean` is deleted, and its nineteen
direct consumers import the QICLean module. Retaining both declarations would
define the same fully qualified name twice. No compatibility alias is needed:
the theorem name itself is preserved by the relocation.

The QICLean revision is changed in `lakefile.toml`, `lake-manifest.json` and
`docbuild/lake-manifest.json` together. The QICLean root already imports the
new module through its algebra collection. The regenerated TNLean algebra
collection therefore drops the deleted module without adding an external
import. The existing blueprint anchor keeps the same theorem name; the
promoted-tactic ledger and repository guidance point to its new source.

Source verification checks the unchanged theorem and consumer proof text,
resolves all former import sites, and compares the dependency manifests and
toolchain. It does not substitute for a Lean build against the coordinated
QICLean revision.
