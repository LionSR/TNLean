# MPU printed blocking and ownership audit — 2026-11-16

## Baseline and mathematical scope

The campaign began from fresh main
`73007e10337424b3556fb198507b2157f99f19a3`, after finding a stale original
checkout. It integrated `2e0e6387c156ff7449a4f1df51775a5a5d2144cf` in the
sequential-unwinding checkpoint and now integrates fresh main
`eb889b02d660645c4001e2271a880ebe339e593a`. Dependency pins are unchanged.

Source: `Papers/1703.09188/paper_v2.tex:1657–1733`, especially
`eq:defeq-sigma1`, `eq:unwind-dagger-trick`, and the proof of
`prop:sigma1-and-sigma2-equal`.

The branch proves the following connected results.

1. **Local unwinding.** The actual eight-spin network factors into the
   source's two four-spin factors. From `A ⊗ B = ζ X ⊗ X†`, summing entries
   `(i,k),(k,j)` gives `AB = ζ I`; isometry of `A` gives `B = ζ A†`.
   The actual printed two-block supplier is reused. The canonical local
   corollary derives its certificates from actual even-ring adjoint
   symmetry, with its canonical ambient restriction explicitly retained.
2. **The full finite-spin sequence.** The literal circuits and every
   actual `Y_s` act on `Fin (2*k) → Fin d`. Support commutations, the
   successor identity, both endpoints and the phase `σ ζ^(k-1)` are proved.
   No successor equality or full blocked parity is a premise.
3. **Actual arbitrary positive blocking.** For supplied square standard-form
   data, `TwoSiteStandardFormData.printedBlock` constructs the standard form
   of the actual `blockTensor W k`, after the explicit physical half-word
   relabelling. It retains the original virtual bond space and constructs
   both identity-spectator half factors. The open input contraction and
   the centered output contraction are proved. This is not merely a pair
   of unitary circuits or a newly manufactured tensor with those gates.
4. **The trace of those actual gates.** Their normalized trace equals the
   intrinsic trace of the actual blocked tensor. Under adjoint symmetry on
   every even ring of length greater than one, the existing intrinsic parity
   theorem gives the source odd/even trace identities for these particular
   representatives. Neither result in this step assumes a canonical
   ambient presentation. Intrinsic parity is reused, not reimplemented.

The square supplied-gate hypothesis is explicit: a general supplied
standard form can have distinct intermediate dimensions and rectangular
unitaries between its coordinate spaces. Choosing square gates from the
unrestricted source hypotheses, the general local-symmetry criterion and
full source integration remain separate owner work. The new scope note is
`docs/paper-gaps/mpu_printed_blocking_square_scope.tex`. The original
source-labelled parity entries remain `notready`, and #7111 remains open.
The older canonical local-unitary corollaries retain the existing
full-support paper-gap note; that premise does not occur in the new
supplier or its trace parity theorem.

## Proof structure of the actual supplier

`PrintedBlockingContraction` obtains layer entries from the existing
`QuantumCircuit.noncommProd_embedOp_apply`, with disjointness and exact
exterior supports proved. The open network is a finite sum over the
intermediate ordered pair at every cell. Induction contracts the old right
half factor with the next left half factor through `S.v_apply`. The base
case is `S.W_apply`. Decoding the existing blocked physical alphabet gives
the actual blocked tensor, with both virtual endpoints free.

The input-circuit entry has only two exterior deltas. Summing its exterior
output values against the original half factors selects exactly the open
network. The original-spin equivalence is the existing
`twoSiteChainConfigEquiv`, composed only with the length-commutation cast.
No competing definition of the chain circuit is introduced.

`PrintedBlockingHalfFactors` concatenates two decoded half words. Its
physical equivalence encodes the same ordered original pairs into the
actual block alphabet. The left half factor retains the first spin and
fixes its following spectators; the right half factor retains the last
spin and fixes its preceding spectators. Decomposing words with the
existing `Fin.consEquiv` and `Fin.snocEquiv` makes the two spectator sums
collapse. The centered output gate is the original `v` with exactly the
same spectator deltas. These two contractions and gate unitarity supply
all fields of the standard-form witness.

`PrintedBlockingTrace` uses that actual witness for the gate/intrinsic trace
identity. Common physical relabelling preserves the two-ring exchange
trace by reindexing its two finite sums; the normalization is preserved by
the equality of the finite alphabet cardinalities. Its parity theorem
consumes merged `IsMPU.intrinsic_blocking_trace_parity`. The existing actual
printed two-block witness identifies the even reference trace. No orbit
lifting, continuous source factors, local gauge supplier, or stabilization
premise is added to these results.

## Dependency and ownership map

| Lane | Current boundary and owner | Campaign action |
| --- | --- | --- |
| #6024/#6140 | `codex/mpu-continuous-support-6024-6140`; task `6af9f45c-edd0-8191-b3e2-51c9c8ba90dc`; candidate `86767f70f62aaf977040c026d53673054f5499c6` | Reserved. No takeover or retry of another owner's denied draft operation. Candidate validation, orbit lifting, endpoint compatibility and reduced-source support are separate. |
| #7032 → #7016 | Requires #6024/#6140 and source comparisons | Preserve dependency order; no continuous gauge assumption. |
| #9880 | `feat/mpu-intrinsic-deformation`; task `6af9f920-4cd4-8191-9fe1-1642159240d7`; candidate `ff958a09976d472ebeef5054b8a566fb570b0744` | Reserved. Reuse merged intrinsic results and do not edit owner files or retry denied operations. |
| #7574 | #10640, reported head `a64097005a1112afdcf9ce3300961e1e496373b5`; task `6af9f452-d118-8191-8e3d-de85819c00c3` | Reserved. Earlier validation does not replace final-head CI/review or general-equivalence integration. |
| #7111 | This campaign's printed blocking lane, draft #10690 | Local unwinding, literal finite circuits, all sequential steps, actual square supplied blocking and its trace. General source integration remains open. |
| Claude product refactor | `claude/mpu-sitewise-kronecker-power`, originally `0ed96ebf5afa91e4aa69c0e6c38ee2683186ab3b` | Reserve `FinKronecker`, `TwoSiteStandardFormCircuit`, `FundamentalTheoremGates`, `ShiftStrictEquivalence`, and the central tactic ledger. |
| Other live Claude MPU branches | Campaign board, canonical/ancilla blocking, conjugation, equivalence index, local-symmetry criteria, standard-form path, virtual-gauge path | Consume main APIs only; no edits to those branch files, the main symmetry blueprint, or campaign metadata. |
| Broad refactoring | #10676/#10677/#10678; task `6af9f3c7-5f6c-8191-955c-d9b6b14dd0ee` | No edits to their proof files or audit records. |
| MPO campaign | Task `6afa4931-98d0-8191-9777-f0e0779620c1`; #10626/#10636/#10641 and prerequisites | No cochain, anomaly, or MPO implementation here. |
| MPU-to-QCA and gauging | Handover in merged #10604 | QCALean owns this work. |

The initial audit inspected all 59 then-open PR file lists. Fresh branch and
main reads establish the subsequent boundaries. The new proof modules,
own blueprint fragment, square-scope note and audit are isolated. The
MPU import aggregator is generated and is the shared integration surface.
Upstream campaign-board and tactic-ledger updates enter only through the
normal main integration; their contents are not edited by this campaign.

## Actual coordination and review status

No supported tool exposes a direct Claude session. Active ownership was
identified from live branch contents and real Claude session attribution,
including the campaign-board head
`24e0bb6863fd40b140a7010049ec6836d57d2163`, rather than the GitHub author
login alone.

Ownership notices are posted on
[#7111](https://github.com/LionSR/TNLean/issues/7111#issuecomment-6903754725),
with the contraction continuation at
[6904905021](https://github.com/LionSR/TNLean/issues/7111#issuecomment-6904905021).
The campaign checkpoint and fresh ownership evidence are on
[#5704](https://github.com/LionSR/TNLean/issues/5704#issuecomment-6904191637).

Real coordination has occurred through the supported GitHub review channel.
Claude's review-only responses at
[6904590185](https://github.com/LionSR/TNLean/pull/10690#issuecomment-6904590185)
and
[6905032825](https://github.com/LionSR/TNLean/pull/10690#issuecomment-6905032825)
review `74c4ba0` and `9252ca1`, respectively. Both report no substantive
mathematical/prose issue or ownership conflict, and no edits or metadata
changes. They do not cover this larger supplier continuation. A new final
head needs fresh review and hosted checks; no stale approval is reused.

## Verification record

- Exact Lean `v4.36.0-rc1`, Mathlib
  `625d8914199bc567cca9b91f90e8e5afafa5ae51`, QICLean
  `603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac`. No pin changes.
- All 9,047 pinned Mathlib cache files were restored under the writable
  cache directory. Mathlib was not rebuilt from source.
- Targeted package build of `PrintedBlockingTrace` and
  `SequentialBlockingUnwinding` succeeds (19,393 jobs). The three supplier
  modules took 5.9s, 5.9s and 4.4s; the sequential module took 5.8s.
  This is not a full TNLean build. Legacy dependency module-system warnings
  are separate from strict checks of the changed proof modules.
- The three supplier modules pass production strict flags, Mathlib standard
  linters and warnings as errors without diagnostics. All six
  changed proof modules pass this check without diagnostics.
- A temporary transitive audit of all 61 public declarations reports only
  `propext`, `Classical.choice`, `Quot.sound`. No audit fixture is committed.
- Every public declaration has a scope-matching blueprint tag. Blueprint
  roles, reader prose and generated imports are checked; source/tag
  synchronization and reverse changed-declaration coverage are recorded
  against the final published head in the PR.
- The complete blueprint fragment compiles as a standalone five-page LaTeX
  document. Full blueprint and compiled declaration checking remain separate
  hosted-CI obligations.
- The tactic scanner identified a repeated pair-product congruence across
  four sites in two owned files. It is promoted to the source-specific
  `printedPairGate_prod_congr` lemma and all four sites consume it.
  Nested sum congruence reuses existing `Finset.sum_congr₂`. The repeated
  pattern no longer appears in the new files; the central ledger remains
  reserved to its owner, so this audit records the promotion.
- Hosted CI run `43786201840` for `9252ca1` passed the full Lean build,
  compiled declaration checks, timings and PDF compilation, but failed
  the LaTeX formatting step. The owned fragment is corrected with the
  repository-pinned latexindent 3.24.7. The full repository formatting
  gate now passes locally. That run cannot validate the new supplier commit. The final head needs all
  required checks and reviews, actionable findings resolved, and normal
  branch-protection gates before any merge. No merge or source-issue closure
  is asserted.

OpenAI Codex (GPT-6) performed the source/ownership audit and wrote the
proofs and documentation. Maintainer mathematical review remains required.
