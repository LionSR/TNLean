# MPU blocking and ownership audit — 2026-11-16

## Baseline and mathematical scope

Baseline main: `73007e10337424b3556fb198507b2157f99f19a3`.
The original checkout was `eb588dc1`; the campaign branch starts from the
fresh remote main, with no pre-existing local changes.

Source: `Papers/1703.09188/paper_v2.tex:1657–1687`, equations
`eq:defeq-sigma1` and `eq:unwind-dagger-trick`, in the proof of
`prop:sigma1-and-sigma2-equal`.

The selected result is the local four-spin unwinding equation. It is
derived from the actual eight-spin two-block network, rather than assumed
after comparing its tensor factors. If `A ⊗ B = ζ X ⊗ X†`, contracting
entries `(i,k),(k,j)` over `k` gives `AB = ζ I`; the isometry of `A` then
gives `B = ζ A†`. This removes the unexplained factor comparison in the
source proof. The printed two-block supplier already exists and is reused.

The final canonical corollary derives its local equations from actual
even-ring adjoint symmetry. Its canonical ambient restriction is explicit;
the existing full-support paper-gap note applies. No source-proposition
completion is asserted. The arbitrary-k printed supplier and the full
sequence `Y_s = Y_(s+1)` remain to be proved. Intrinsic numerical parity
was already merged and is not reimplemented.

## Dependency and ownership map

| Lane | Current boundary and owner | Campaign action |
| --- | --- | --- |
| #6024/#6140 | `codex/mpu-continuous-support-6024-6140`; task `6af9f45c-edd0-8191-b3e2-51c9c8ba90dc` | Reserved. Continuous support/frame candidates are not orbit lifting, endpoint compatibility, or reduced-source support. |
| #7032 → #7016 | Requires #6024/#6140 and the source comparisons | Preserve this dependency order; no assumed continuous gauge. |
| #9880 | `feat/mpu-intrinsic-deformation`; task `6af9f920-4cd4-8191-9fe1-1642159240d7` | Reserved. #10311/#10360 and intrinsic parity on main are reused. |
| #7574 | #10640, head `a64097005a1112afdcf9ce3300961e1e496373b5`; task `6af9f452-d118-8191-8e3d-de85819c00c3` | Reserved. Current-head CI/review is separate from earlier audited heads; general equivalence integration remains open. |
| #7111 | Literal arbitrary-blocking gates and sequential unwinding remain open | This branch owns the local eight-spin calculation and local unwinding, in new files. |
| Claude product refactor | `claude/mpu-sitewise-kronecker-power`, `0ed96ebf5afa91e4aa69c0e6c38ee2683186ab3b` | Reserve `FinKronecker`, `TwoSiteStandardFormCircuit`, `FundamentalTheoremGates`, `ShiftStrictEquivalence`, and the central tactic ledger. |
| Broad refactoring | #10676/#10677/#10678; task `6af9f3c7-5f6c-8191-955c-d9b6b14dd0ee` | No edits to their proof files or audit records. |
| MPO campaign | Task `6afa4931-98d0-8191-9777-f0e0779620c1`; #10626/#10636/#10641 and listed prerequisites | No cochain, anomaly, or MPO-symmetry implementation here. |
| MPU-to-QCA and gauging | Handover recorded by merged #10604 | QCALean owns this work; no competing QCA implementation. |

All 59 then-open PR file lists were inspected. The only shared edit is the
generated MPU import aggregator, where separate import additions must be
regenerated when integrating other branches. The new proof module, new
blueprint fragment and its chapter input do not overlap an open PR.
The source-labelled parity entries remain untouched and unfinished.

## Coordination

No supported tool exposes a direct Claude session. The live branch and its
Claude session attribution identify an active shared-file owner; the GitHub
author login alone was not used as the ownership test.

The boundary is posted on
[#7111](https://github.com/LionSR/TNLean/issues/7111#issuecomment-6903754725)
and the campaign checkpoint on
[#5704](https://github.com/LionSR/TNLean/issues/5704#issuecomment-6903874234).
No direct contact, response, agreement or transfer of another owner's files
is claimed. Existing owner labels and assignments were not changed.

## Verification record

- Lean: `leanprover/lean4:v4.36.0-rc1`.
- Mathlib: `625d8914199bc567cca9b91f90e8e5afafa5ae51`.
- QICLean: `603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac`.
- Stale dependency checkouts were aligned by Lake to the committed manifest;
  no dependency pins were changed.
- All 9,047 pinned Mathlib cache files were downloaded and decompressed
  under `/workspace/.cache/mathlib`. Mathlib was not rebuilt from source.
- `lake build TNLean.MPS.MPU.BlockingUnwinding` completed successfully
  (19,357 prerequisite/build jobs); the new module took 8.4 seconds.
  This is a targeted build, not a full TNLean build. Existing dependency
  modules emit legacy module-system warnings; the new module has no warning.
- The complete new module passed the production strict Lean flags, including
  the Mathlib standard linter set and warnings as errors.
- All four public declarations were audited with temporary `#print axioms`
  commands outside the repository. Only `propext`, `Classical.choice` and
  `Quot.sound` occur. No audit fixture is committed.
- Generated imports, blueprint roles, source/tag synchronization, reader
  prose, integrity-token and whitespace checks pass. All four new public
  declarations have separate scope-matching blueprint entries. No source
  parity-completion marker was changed.
- The blueprint fragment compiles in a standalone two-page LaTeX document.
  Full blueprint compilation and compiled declaration checking are separate
  hosted-CI obligations; no local full-blueprint pass is claimed.
- The tactic scanner found no repeated pattern in the new module. Its MPU
  subtree scan identifies the pre-existing product-copy repetitions owned
  by Claude's live refactor; those are not edited here.
- Hosted exact-head CI, independent mathematical/prose review and normal
  merge gates remain required. No merge or source-issue closure is claimed.

OpenAI Codex (GPT-6) performed the source/ownership audit and wrote the
candidate proof and documentation. Maintainer mathematical review remains
required.
