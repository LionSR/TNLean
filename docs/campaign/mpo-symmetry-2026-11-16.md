# MPO symmetry campaign — 2026-11-16

## Claimed scope and baseline

Owner: the separate campaign delegated from thread `6af54194-8060-8191-9800-f45dd86d90e6`.
Branch: `feat/10521-controlled-z-combined-symmetry`. Issue: #10521, partial construction only.
Claim comment: https://github.com/LionSR/TNLean/issues/10521#issuecomment-6903716068.

Provisioned TNLean was clean at `eb588dc15332a3798431015e6c27ecbaf329b2d1`.
Fetched upstream main is `73007e10337424b3556fb198507b2157f99f19a3`; this branch starts there.
The provisioned dependency directories were stale too: QICLean `acda92aa` and Mathlib
`c55e6e78`. The manifest requires QICLean `603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac`,
Mathlib `625d8914199bc567cca9b91f90e8e5afafa5ae51`, and Lean `v4.36.0-rc1`.
Restore those exact pins and fetch prebuilt Mathlib artifacts before any build.
Do not use the provisioned v4.35 artifacts or rebuild Mathlib from source.

## Refreshed ownership and dependency map

The live issue bodies, comments, open-PR inventory (59 PRs), and every open-PR file list
were read before implementation. Thread interiors are unavailable in this environment;
thread ownership below combines the delegation with current GitHub evidence.

| Scope | Current evidence | Campaign boundary |
| --- | --- | --- |
| #8321 | #10626 draft, `b554532d`, stacked on `761f6a56`; #10615 `d6b3712c`, #10616 `3ba155b6` remain drafts | Preserve existing owner and prerequisite order. ControlledZGauging and cochain sources are occupied; add separate consumers only. |
| #8322 | #10636 draft `2475f50b`; universal/bridge local branches reported in delegation | No based-ring implementation or consumer migration here. Preserve local unverified bridges. |
| #8053 item 2 | Existing Fibonacci owner; issue says actual two-block L=F remains | No takeover or duplicate symbolic calculation. |
| #8048/#8054/#8948 | tnlean-35; #8948 comments claim `feat/mixed-path-mpo-batch` | Preserve time reversal, arbitrary-boundary adapter, Hamiltonian commutation and degenerate interpolation. |
| #8040 | tnlean-43 | No CZX PEPS changes. |
| #10519 | Abstract pre-bialgebra family construction remains; #10517/#10526 merged | Faithful unital representation alone does not imply cosemisimplicity. Supplied-family counit does not solve this. |
| #10521 | Open, unassigned, zero comments before campaign claim; no open SIMPS PR found | Claim exact combined normal MPO family, actual split-leg/ring comparison, and two invariant states. Full phase identification remains open. |
| #8050 | Updated status confirms algebraic foundations on main; physical invariance/interpolation remain | No claim of the full L-class/physical-phase biconditional. |
| #6024/#6140 → #7032 → #7016 | Active continuous-standard-form owner from delegation | No MPU path-source-data changes. |
| #9880 | Active intrinsic-deformation owner from delegation | No sign-deformation changes. |
| #8060 | #10641 draft `dac8ae0a` | Preserve conditional detector/physical-anomaly distinction. |
| #7574 | #10640 ready `3c4ede7d`, updated since handoff | Existing owner; final-head CI/review still required. |
| Refactoring stack | #10676 `7c16e494` → #10677 `c5ddd838` → #10678 `064e2daa`, all drafts | No occupied source edits or cherry-picking. Independent new modules only. |

No labels, assignees, PR bases, workflow approvals, or issue states were changed by this audit.
#10616's reported workflow approval gate must be handled by its authorized owner/maintainer.
Live workflow read confirms PR CI run `43744473685` remains `action_required`.
Skipped auto-fix workflows do not clear that gate.

## Mathematical dependency order

1. Reuse existing diagonal dressing and letter-rescaling normality; prove a commuting
   diagonal twist of an exact normal group family is again exact and normal.
2. Instantiate the construction for the combined controlled-Z/on-site Z symmetry on the
   actual qubit chain, using the existing controlled-Z family and character on the other bit.
3. Identify its operator with the product of the existing split-leg phases on the ring;
   derive invariance of the controlled-Z state and reference product state at every positive
   length, including length one. Obtain actual action/fusion data through existing results.
4. Remaining: compute and compare the two actual L-symbol classes; prove physical path
   invariance or a source-faithful SIMPS classification before identifying the phase.

## Results and validation

Both new proof modules pass the package build and direct strict Lean elaboration, including
`autoImplicit=false`, `relaxedAutoImplicit=false`, the package's synthesis-depth bound,
standard Mathlib linters, and warnings as errors. All 22 new public declarations have
transitive foundational dependency sets contained in `{propext, Classical.choice, Quot.sound}`.
The temporary audit command file was deleted. No full-library or compiled Blueprint acceptance is
claimed.
The new shared construction belongs in `MPOSymmetry/DiagonalTwist.lean`; the controlled-Z
consumer belongs in a separate example module, avoiding the #8321 source overlap.

Verified mathematical results:

- A commuting diagonal on-site twist preserves the exact normal group multiplication
  law and the original bond dimensions. Every common invariant state remains invariant.
- The combined controlled-Z/on-site Z family has bond dimension one or two, is normal,
  and has the literal identity operator. Its operators form a native Mathlib representation.
- Its actual operator equals the diagonal product of the existing split-leg phases on
  every positive ring length, including one. Those operators are unitary.
- The existing bond-three controlled-Z state and bond-one zero product state are both
  fixed. Actual action reductions exist for each under the same family. The anomaly
  class is zero. This last statement is in degree three, not the missing relative
  degree-two class comparison.

Exact local verification commands and evidence (2026-11-16):

```
lake build TNLean.MPS.Symmetry.MPOSymmetry.DiagonalTwist \
  TNLean.MPS.Examples.ControlledZCombinedSymmetry
```

Passed, 18,895 jobs in the focused dependency closure. This is **not** the full library
build. Dependency modules emit their existing legacy-module/style warnings; both new
sources pass independently with all warnings treated as errors:

```
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dpp.unicode.fun=true -DmaxSynthPendingDepth=3 \
  -Dlinter.mathlibStandardSet=true -DwarningAsError=true <new-proof-source>
```

Also passed: generated-import check (98 aggregators, 5,420 production modules),
Blueprint source synchronization with reverse coverage of both new modules, Blueprint
roles, the complete repository text-style linter, reader-facing prose, forbidden-token
scan, 100-character line bounds, and
`git diff --check`. The focused tactic-pattern scan found no promoted/new repeated
pattern in these modules; unrelated pre-existing candidates remain with their owners.
All 22 public names occur in the new Blueprint entries. Source synchronization is
distinct from compiled full-library declaration checking and web/PDF generation.

The initial cache command stopped because its default `/home/agent/.cache` is read-only;
retry uses `XDG_CACHE_HOME=/workspace/.cache`. Only the cache executable was compiled.
The exact prebuilt artifact fetch completed (9047 artifacts); no Mathlib Lean source module
was rebuilt. The style executable compiled its required C objects from the cached artifacts.
Dependency pins and tracked configuration are unchanged. The new modules use the
same legacy import convention as their existing dependencies: this Lean version rejects
importing those non-`module` dependencies from a `module` file.

## Candidates and blockers

- Relative L-symbol extraction needs actual reduction matrices; a split-index bond
  projective representation alone does not compute the MPO action L-symbol.
- The full SIMPS physical phase theorem is absent, and the paper-gap note stays open.
- Final-head focused strict elaboration, full library/Blueprint CI, required proof and
  Blueprint review, and dependency-order integration are required before any normal merge.
- Preserve the shared tactic ledger owned by #10677. Record any abstraction decision here.
  The diagonal construction reuses existing mathematical lemmas rather than adding a tactic.
