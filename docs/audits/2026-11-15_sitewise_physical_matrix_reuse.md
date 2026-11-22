# Sitewise physical-matrix proof reuse

Base: `eb588dc15332a3798431015e6c27ecbaf329b2d1`.
Original module blob: `46f91f8cf65d48aca820a7953fcdad274157478b`.

This implements rank 11 of the comprehensive simplification audit in #10637.
In `MPS/Operator/PhysicalSector/SitewisePhysicalMatrix.lean`:

- Move `sitewisePhysicalMatrix_one`, with its proof and simp attribute unchanged, before the isometry theorem.
- Derive `sitewisePhysicalMatrix_isometry` from the adjoint, multiplication and identity laws and the supplied Gram equation.
- Derive `sitewisePhysicalMatrix_mul_conjTranspose` from the adjoint and multiplication laws.

All 15 public declaration headers, imports and Blueprint anchors are unchanged.
No definition, hypothesis, rectangular dimension or zero-length case changes.
The module shrinks from 310 to 285 lines: **net −25 Lean lines**.
All 27 open PR file lists and relevant branch-name searches were checked; no edited-file overlap was found.

Passed: public-header equality, exact identity-block relocation, unchanged-import, prose, line-length, whitespace and forbidden-token checks.
The focused Lake command exits 127 because Lake and dependency caches are unavailable; compiler acceptance remains pending.
Required hosted checks include the changed module, `SitewisePhysicalRecovery`, `PhysicalSectorProductTransport`, the root build and strict changed-file checks.
#10637 and #10639 still have queued `changes` jobs, without diagnostics or completed CI conclusions.
Remaining broad API and hypothesis migrations stay open; no merge is performed.
