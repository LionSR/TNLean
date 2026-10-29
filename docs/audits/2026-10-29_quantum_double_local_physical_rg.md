# Local elementary quantum-double physical renormalization

Issue: LionSR/TNLean #8947, item 4, bounded to one local four-site block.

## Source and boundary

Compared `Papers/1001.3807/paper_v3.tex` lines 2745–2833 and 2861–2923.
Inspected `figs6/tc-lattice.pdf` and `tc-2x2-renorm.pdf`; the independent
reviewer additionally inspected `tc-tensor-orientation.pdf`.
The checkout lacks `renorm-as-diff-doubles`; no geometric assertion relies on it.
`quantumDoubleElementaryTensor_eq_regular` identifies the elementary coefficient
with the existing right-regular action on `|s⟩ = L_s|1⟩`. The block contracts
four actual elementary tensors across four internal bonds. It is not defined
by the desired blocked K coefficient.

`quantumDoubleElementaryBlock_physicalRG` and its matrix version quantify over
all boundary and physical labels of every finite group, with no commutativity,
compatibility, flatness or image premise. Eight virtual registers remain.
The full physical permutation inverts the original-arrow basis and extracts
the ordered holonomy into the fourth physical register. Three physical spins
remain active and the fourth remains a full G register fixed at identity.
Four independent surplus virtual covectors are fixed at identity.
`quantumDoubleElementaryBlock_toK` reconstructs exactly the existing
`quantumDoubleKTensor` in source order.

The printed pair map D(a,b)=(a,b^-1 a) has inverse (a,d)↦(a,a d^-1), not D
itself in general. The matrix identity uses ket-forward physical P and ket
inverse boundary D correctly under Mathlib's pullback permutation convention.
The block coefficient is exactly one. The reduced tensor satisfies
RR†=|G|I, and the explicitly defined |G|^-1/2 R satisfies NN†=I.
The existing source-illustration paragraph was corrected: a regular-invariant
uniform-vector calculation is conditional and does not describe the identity
covectors obtained in the copied-color coordinates.

No global torus tiling, full-lattice common kernel, parent-space comparison or
topological degeneracy theorem is claimed. This does not close issue #8947.

## Independent review

An independent reviewer read the exact source,
actual proof bodies, new regression, Blueprint and gap note. It found no
remaining mathematical blocker after the surplus-factor prose was corrected.
It verified inverse directions, noncommutative products, absence of stronger
premises, retained dimensions and exact normalization. Its independent Python
S3 oracle checked all 36 pair inputs, 1,296 physical inputs and 1,296 colorings;
the 216 retained physical words each had multiplicity six. That computation
is supporting evidence, not a substitute for the Lean proofs.

## Validation performed

- Preserved the Lean toolchain and all dependency pins. Mathlib checkout
  `c55e6e786f49471c72fbddbec5415808896aec1e` matches the manifest and Lean
  v4.35.0-rc3. The matching prebuilt Mathlib artifacts were verified before builds.
  No Mathlib source build was started.
- `lake build TNLean.PEPS.Examples.QuantumDoubleRenormalization`: passed;
  dependencies were built only after
  the matching prebuilt Mathlib cache was verified.
- Direct strict elaboration of the production file and
  `scripts/quantum_double_renormalization_regression.lean`: passed with
  autoImplicit=false, relaxedAutoImplicit=false, maxSynthPendingDepth=3,
  Mathlib standard linters and warningAsError=true.
- Regression uses S3 noncommuting transpositions, rejects pair involutivity
  and uncorrected original-arrow holonomy, checks full-space inverse maps,
  unrestricted physical/K/matrix boundaries, raw Gram factor six and exact
  normalized Gram. It also checks the binary abelian specialization and CNOT.
- Transitive checks of all nine public theorems reported only `propext`,
  `Classical.choice`, `Quot.sound`. Temporary checks were kept outside the repo.
- All 23 new Blueprint declaration links were separately resolved by Lean.
  Blueprint source synchronization passed, including reverse coverage of every
  new public definition/theorem. Generated import aggregators are current.
  The new module's 19-module TNLean import closure is acyclic and contains
  no lattice-placement module.
- Existing source-construction regression (`--no-render`): passed, including
  25 negative mutations and S3/binary source checks. Existing local-term
  regression (`--no-render`): passed, including seven negative mutations.
  No existing test assertion was changed.
- Import-generator unit tests (11), Blueprint scanner tests, reader-facing
  prose check and diff whitespace check passed. Tactic-pattern scan found
  no new repeated pattern in the new module.

## Not validated

No full repository root build was run. No Blueprint rendering or
`leanblueprint checkdecls` was run: the leanblueprint executable is not
installed. Source synchronization and compiled resolution of all new links
passed instead. No macOS-only cache-seeding test was applicable on Linux.
Hosted CI is required for full-repository validation.
