# Complete verification of the entropy and collar estimates

The complete TNLean root build passed with 12,480 jobs. The native blueprint
checker then verified all 19,876 declaration names against that compiled root.
The complete PDF and refreshed web builds passed. These checks establish the
library and blueprint verification of the auxiliary results; they do not prove
the full area law or the amplified information estimate.

The verification inputs are frozen at
`e623594d6c23f647bbdce797bcdf1a4cd48610b7`. All production Lean files and root
dependency inputs remain unchanged from
`548f23f7b274af443eb3644d8153f15148565c31`. The only configuration change is the
four-line string-pool setting in `blueprint/src/latexmkrc`, copied exactly from
`53f0bd48eed8771e331309ffb929794f9869b611`, merged into main by
`806099b4dddcce591b3a62ee1921926a6af5ad55`. It preserves explicit caller
overrides and changes no system-wide TeX configuration.

`verification.json` records the commands, exit codes and SHA256 hashes. The
guarded full build used this worktree's preserved blocking lock helper and its
own build wrapper. Mathlib's pinned prebuilt cache was verified before building.
The root build has inherited linter warnings, preserved in `root-build.log`.
The new modules retain their earlier clean target builds and seven strict
kernel reports.

The declaration audit used the already compiled native checker from the
QICLean integration worktree under this TNLean worktree's `lake env`. Its
pinned package revision is `3d425859e73fcfbef85b9638c2a91708ef4a22d4`; its source,
configuration and toolchain match the local checker byte for byte. The two
root toolchains also match. The checker loads this workspace's compiled root
and tests every name in `blueprint/lean_decls`, exactly as the usual blueprint
command does. No cache artifacts were copied and no repository lock was taken
for this audit. The successful checker emits no text, so `checkdecls.log` is
empty; its exit code and declaration-list hash are recorded separately.

An earlier interpreted execution of the checker failed with a Lean
IR-interpreter assertion. Its failed log is preserved, and that execution is
not counted as a successful audit. The subsequently queued local executable
build was cancelled while still waiting for the lock, before any build began.
The completed native audit allowed other agents' queued builds to proceed.

The PDF was forced once to replace the previously failed rendering; four
XeLaTeX passes converged to 2085 pages. The final log reports 6,242,741 string
characters against a capacity of 11,673,555, and no undefined references or
citations. `pdf.log.gz` and `print.log.gz` preserve the complete command log
and final TeX log. Both compressed and uncompressed hashes are recorded.
The generated PDF remains at `blueprint/print/print.pdf`; its hash and size
are recorded without committing the entire book.

Physical PDF pages 1697–1698, printed as 1696–1697, contain the regional
dimension bound, conditional boundary implication, exponent gap and uniform
collar threshold. Their rendered images are preserved here. Visual inspection
found readable formulas, resolved citations and references, and no clipping
or overlap in those entries. The refreshed web build uses the complete print
bibliography and reports no warnings.

Assisted by OpenAI Codex. Human mathematical review remains separate from
these formal and rendering checks.
