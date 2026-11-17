# Mixed-path weak-Hopf parent: scope and verification

Work for #10762 starts from main `7e8438a32f1f0435e3acec579a89656de1b3f07b`
on local branch `codex/10762-weak-hopf-mixed-parent`. No push, PR or merge is
part of this work.

## Source and ownership inspection

Read #10762, #10763, the source's symmetrization paragraph and Appendix B,
the existing weak-Hopf completion note, the actual mixed MPO construction,
and the generic weak-Hopf representation and averaging implementation.
Open PR searches for mixed-path and weak-Hopf work found no overlapping
new module. Related open work includes #10686 (relative L-symbol classes),
#10636 (based rings), and #10748 (Kraus name migration). Changed-file lists were checked: the only overlap with #10686 and #10636
is the generated `MPOSymmetry.lean` import collector; there is no overlap
with #10748. No existing implementation file from these PRs is edited. The parallel #10763 session owns endpoint adjoint closure; no
existing parent-commutation or endpoint-adjoint file is edited.

There is no `.agents/skills` directory in this checkout. Read root AGENTS.md,
project conventions, blueprint style, the tactic ledger, and the shared
texra Lean conventions, proof-assistant and paper-gap-note skills.

## Mathematical results and limits

1. A faithful convolution-dual representation with a unital physical
   representation has no zero diagonal physical letter. The enlarged
   mixed MPO has such letters on both unused physical summands. Thus it
   cannot equal any existing `WeakHopfRepresentation.tensor` when either
   original physical dimension is positive. No action, injectivity,
   fusion, adjoint, or integral hypothesis is needed for this obstruction.
2. For a supplied normalized weak-Hopf realization of the **active** common
   MPO, exact endpoint action decompositions with common multiplicity and
   injective endpoints give `E(hγ) = Q - 1 + hγ` on the open interval.
   Positive bond dimensions give continuous extension to both endpoints.
3. Adding `1 - Q` recovers the existing active interaction exactly.
   Including it isometrically with the unused-space penalty recovers the
   existing arbitrary-alphabet mixed interaction on `[0,1]`. Positivity,
   continuity and the existing uniform periodic gap transfer by equality.
4. The realization supplies adjoint boundaries, which physical inclusion
   preserves. Compatibility and endpoint continuity give commutation of
   the completed periodic Hamiltonian with the actual common MPO for
   every ring length at least two.

The realization is supplied, **not constructed from fusion and F-symbols**.
The recorded representation contains only the coproduct, star, faithful
representation and integral laws used by the proof, not all C*-weak-Hopf
axioms. The theorem does not claim a spectral gap or the same kernel for
the literal uncompleted average. The source's general reconstruction and
phase-classification scope remains open. The enlarged unital realization
as literally requested is impossible, rather than a missing proof.

## Validation

All three new modules pass the package build and strict direct elaboration
with automatic implicits disabled, synthesis depth 3, standard Mathlib
linters, and warnings as errors. All 26 new blueprint declarations were
checked against the compiled modules. The five audited capstones depend
only on `propext`, `Classical.choice`, and `Quot.sound`.

The targeted modules and `TNLean.MPS.Symmetry.MPOSymmetry` aggregate build
pass (20,433 jobs). `scripts/ci_lean_checks.py strict --base origin/main`
passes on all four changed Lean files, including the import collector;
no regression script is selected. Full-library and full-site rendering are
not claimed. Blueprint validation includes all 26 new compiled references,
repository-wide role/source synchronization, and the standalone note PDF.
Final verification also passes:

- `lake exe lint_style` (no text-style errors).
- `scripts/blueprint_roles.py --check` and
  `scripts/blueprint_lean_sync.py --report-duplicate-tags --ci`.
- Pinned LaTeX formatting of the new blueprint section; standalone note PDF.
- Generated-import freshness, import layers, no new declaration forwarders,
  module size, added reader-facing prose, and whitespace checks.
- The scoped tactic-pattern scan and new-source proof-integrity scan.

The final aggregate rebuild also passes after the docstring correction.
Existing dependencies emit module-system advisory warnings; the four
changed sources pass the stricter warning-as-error check. No placeholders,
new axioms or kernel bypasses are introduced. Temporary diagnostic Lean
files were removed. The working tree is intended to remain clean, and no
remote publication or review action has been performed.
Prebuilt Mathlib was fetched with the pinned Lean 4.36.0-rc1 toolchain;
no Mathlib source build was attempted. The standalone paper-gap note
compiles to a three-page PDF using the local CTAN doublestroke package.
The repeated endpoint-extension pattern is recorded in
`docs/tactic_patterns/mixed_weak_hopf.md`.
