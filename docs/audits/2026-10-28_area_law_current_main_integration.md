# Area-law integration on current main

This integration starts from main revision
`c457d2be30e12c770fb7807e822f0ca72739f498`. It preserves the removal of the
permanent Lean test directory and the new rule that foundation inspection is a
manual local operation. No permanent test or per-theorem foundation fixture is
introduced. The earlier audit
`2026-10-28_lvv_integrated_verification.md` describes a historical snapshot under
the earlier policy; its fixture descriptions do not prescribe the current workflow.

The worktree was created at that exact revision and seeded by the canonical script
from a clean, fully built hot-main at the same revision, before mathematical
changes were applied. The Lean, Mathlib and QICLean pins are unchanged. All ordinary
builds run through `scripts/lake_build_locked.sh`. The prebuilt Mathlib cache is
used throughout; no Mathlib source is rebuilt.

The mathematical contributions comprise independent bond trimming with its
corrected quadratic radius, deterministic error reduction, physical local
propagation and finite Gaussian quadrature, a finite energy family chosen before
every ground pair, left-factor decompositions retaining simultaneous rank bounds,
and extraction of an MPS from the actual final viable span. They also include the
finite uniform sharp matrix Bernstein inequality, with the rectangular case proved
through Hermitian dilation. The general probability version remains separate work.

Ordinary targeted verification has passed for the physical Gaussian, cut
decomposition and final-span results (4159 jobs); for the scaled deterministic
error reduction and scalar polynomial bounds (3942 jobs); and for finite matrix
Bernstein (3248 jobs). Strict final-source and manual foundation checks of the new
physical finite-filter construction are described in
`2026-10-28_physical_viable_filter.md`. Full-library and compiled blueprint
verification are still required for the complete integration snapshot.

The precise quantitative qualifications remain part of the mathematical statements:
the size-trimming theorem uses the library constant-cut bound and corrected net
exponent; bond trimming uses a quadratic radius; the unknown-energy filter uses
Huang's Gaussian construction with conservative polynomial parameters. Neither the
printed sharper quantitative rates nor a running-time theorem follow from these
results. The original power sampler has a ground-energy-dependent exponent,
as documented in `docs/paper-gaps/lvv13_sampling_ground_energy.tex`.

At this snapshot, the physical finite filter supplies a complete error-reduction
step. The successive cut induction must still combine it with extension and the
actual size and bond trimmings. The independent ground-state approximation theorem
is used to control trimming loss, rather than to replace that construction.

The ALVV degenerate-ground-space development is checked in a separate worktree with
its required companion-library revision. Its interval, gap-capping and nontrivial
spectrum restrictions must be retained when integrating or comparing its results.
The low-energy and binary-tree constructions, the unrestricted quantitative source
claims, and the remaining Hastings and AKLV arguments are not certified by this
integration report.


## Verification of the first integration snapshot

Revision `bacd5b7d73b144f7d828b8e0473bdfac89af3063` passed the full library build
(15004 jobs), strict compilation of all 52 changed production sources, manual
ordinary-object inspection of 251 public declarations, and compiled blueprint
declaration checking. The inspected declarations use only `propext`,
`Classical.choice` and `Quot.sound`. No permanent foundation fixture is present.
The full and targeted build logs contain no Mathlib source-compilation jobs, and
no reported new job in the full build reached the 25-second diagnostic threshold.

The subsequent contribution supplies the actual successive induction and final-span
approximation, described in `2026-10-28_lvv_successive_construction.md`. Its independent
strict and foundation checks precede its ordinary integration verification. It is a
new contribution beyond the verified snapshot above; that snapshot is not evidence
for source files added afterwards. The same distinction applies to the subsequent
general-probability integral trace-exponential estimates.


The next integration also includes the completed general iid complex matrix Bernstein
inequality, described in `2026-10-28_lvv_matrix_concentration_plan.md`. Its statement
uses the actual centered Gram variance norms and the dimension factor `2d`.
This concentration theorem is distinct from the source-specific word sampler; the
successive construction instead uses the independently proved physical Gaussian
family. The generic probability and matrix-analysis modules are staged here pending
reconciliation with the companion library's existing results and active development.
