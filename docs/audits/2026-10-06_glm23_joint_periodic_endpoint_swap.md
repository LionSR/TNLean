# GLM23: sector exchange and both actual periodic endpoints

## Source and scope

This extends the checked first-endpoint package for GLM23 v3,
`Papers/2203.12563/REsubmission.tex`, lines 1695–1777. The actual mixed
family, joint support, and periodic Hamiltonian are the existing objects.
The new result covers the second periodic endpoint and supplies one
positive constant valid at both endpoints for every ring length at least
two. It does not assert a gap over the interior of the path or settle
the open-boundary comparison or phase classification.

## Exact permutation and transport

The physical equivalence sends `00(i)` to reversed `11(i)`, `11(j)` to
reversed `00(j)`, `01(x,a,b)` to reversed `10(x,a,b)`, and `10(x,a,b)` to
reversed `01(x,a,b)`. Both rectangular coordinates retain their order.
The virtual change is the actual summand permutation in each block,
not transport along an equality of dimension numerals.

Writing this virtual algebra equivalence as `Φₓ`, the actual letters obey

```
C_rev,x(e μ) = Φₓ(C_x(μ))
W_rev,x(1−γ) = Φₓ(W_x(γ))
A_rev,x(1−γ,e μ) = Φₓ(A_x(γ,μ))
```

These statements hold for every real parameter without injectivity or
dimension assumptions. The physical isometry `U_N` maps reversed-chain
vectors to original-chain vectors by precomposition with the alphabet
equivalence. The joint two-site boundary identity is
`U₂ Γ_rev,1−γ((ΦₓXₓ)ₓ) = Γ_γ(X)`.
Trace invariance is applied to every complete block product before the
joint sum is taken, preserving all physical overlap between block labels.

Surjectivity on each virtual block gives exact support equality. Orthogonal
projection onto an isometric image then gives local parent conjugacy.
The existing generic cyclic-placement conjugacy supplies the full periodic
Hamiltonian conjugacy, preserving both directed terms at length two.
The same matrix permutation transports actual component MPS vectors and
their common coefficient map, even at length zero.

## Endpoint kernels and gaps

Apply the first-endpoint theorem to the reversed pair. The second-endpoint
kernel is exactly the span of the actual parameter-one component vectors.
Its uniform gap has exactly the reversed first-endpoint constant.
The source hypotheses are the two simultaneous one-site spans and
positive second-block dimensions. No positivity of the original first
dimensions, nonempty-label assumption, or nonzero physical alphabet is
introduced.

The generic isometric-conjugacy helper explicitly transports kernel
membership, the whole kernel, and its orthogonal complement. It preserves
any real norm-gap bound in both directions without positivity or finite
dimensionality assumptions. The kernel-orthogonality transport is therefore
part of the proof, rather than an additional premise.

When both endpoint block dimensions are positive, the minimum of the two
common-parent endpoint constants works at both parameter values. Each
endpoint bound comes from its full joint canonical parent. The result
does not take minima of separate block gaps.

## Implementation and ownership

- `JointMixedEndpointSwap` proves the exact physical and virtual family,
  joint-support, and local-parent identities.
- `JointMixedEndpointRightPeriodicGap` proves actual periodic transport,
  the parameter-one kernel and uniform gap, and both-endpoint statements.
- `IsometricConjugationGap` provides five generic isometry lemmas. Their
  unique blueprint owner is the shared ch13 martingale entry
  `thm:martingale_isometric_conjugation_gap`; the core-identification
  development uses the same file and owner.

The eight first-endpoint proof modules are reused unchanged. Integration
adds three generated imports, one strict regression entry, and one chapter
include. The swap blueprint leaf gives direct mathematical statements and
proofs; it adds no tensor diagram.

## Checked implementation and documentation

The initial three-module source checkpoint is preserved publicly at
`18fe4919ac69bfbf670245dcf6c9d0fe02808b47`, tree
`27d03b2780228bb42c94b9af4b4f8a0c547e49f0`.
That checkpoint did not compile the actual swap or right-periodic modules;
its new blueprint entries were intentionally unchecked. The generic helper
had passed an isolated strict native compile in 8.9 seconds before the
executor filesystem interruption, with no source repair.

Native [CI run 37472300569](https://github.com/LionSR/TNLean/actions/runs/37472300569)
subsequently passed for public head
`e8e89126bf85e16d1fa0df36d1f0d2e17164cecf`. GitHub tested merge commit
`33adb3d33e84222d1010da026e1cc8a0f4ec0982`; its tree, the public-head tree,
and the authored checkpoint `ee50ef44ca75f22a4885ccb2430f4b2c985dcd8c` tree
are all `ef908946b606e9b3e19c92dea873a979f920c85d`.

The [native build job](https://github.com/LionSR/TNLean/actions/runs/37472300569/job/112298681251)
completed all 12,405 build jobs. The actual swap took 10.0 seconds, the
right-periodic module 8.9 seconds, and the shared isometric-conjugacy
module 2.0 seconds. Strict endpoint regressions, the text style linter,
compiled blueprint declarations, and compiled paper-gap declarations
passed. The changed-module timing gate also passed; it reported one
35-second warning for the existing periodic-sector module, below the
50-second failure threshold.

The regression covers physically overlapping block columns on endpoint
alphabets of sizes two and three, unequal virtual dimensions one and two,
the ordered rectangular tuple `(0,1)`, arbitrary-parameter conjugacy,
two-site kernels, the derived uniform gaps, an original endpoint with
zero physical and bond dimensions, and empty labels with both empty and
nonempty physical alphabets. Fourteen strict guards expect only
`propext`, `Classical.choice`, and `Quot.sound`.

All fourteen new guards passed together with the eleven first-endpoint
guards. The successful strict test step also ran the six other existing
mixed-endpoint regressions. Every checked blueprint statement was matched
to the compiled declarations, including the absence of span or dimension
hypotheses for sector exchange, all chain lengths for conjugacy, the two
one-site spans and positive second dimensions for the second endpoint,
and positivity of both dimension families for the common bound.

The four new entries and their three proofs now carry checked markers.
The shared ch13 isometric-conjugacy statement and proof remain byte-identical
to the core-identification development in PR #8725. This documentation
batch changes no Lean source, regression, workflow, import, or mathematical
statement.

The focused PDF and web builds pass. Both new mathematical pages, PDF
pages 3–4, were visually inspected; the equations fit and references
resolve. The full focus has no overfull boxes. All 21 declaration links
are present in the HTML and have unique source owners. The native Tenkz
event audit passes for the one inherited context panel, with no hard
errors or advisories. Raw HTML reader checks, pinned latexindent 3.24.7,
reader-facing prose, generated imports, and source reverse coverage pass.
All local cross-references resolve. The prior local browser launch was
denied permission to create its singleton socket and was not repeated.
The [native blueprint job](https://github.com/LionSR/TNLean/actions/runs/37472300569/job/112298681274)
passed the full web render, Tenkz sweep, equation-layout and search checks,
and browser reader checks over 91 pages with 192,621 typeset expressions.
Its source synchronization and reverse declaration coverage also passed.
The current focused PDF and HTML were regenerated after adding the seven
markers; the native run predates this documentation-only batch.

The focused prose check passes. A broader local prose scan additionally
reported ten pre-existing PEPS prose findings outside this change. A local
whole-repository source synchronization attempt could not validate 523
references because QICLean is not checked out in this documentation
worktree; the complete native source and compiled checks above passed.
Local checks confirm unique ownership and reverse coverage for all 21
added declarations. The adjacent JSON records these scopes and the current
source and render hashes.

## First native CI diagnostics

Run 37469197230 reached the actual swap module and found two rectangular
sector goals requiring disjointness of the two finite-sum embeddings, plus
one forward support-image goal needing explicit isometry/linear-map
coercion normalization. The repair reduces finite equalities to their
natural coordinates and discharges the impossible cross-sector equalities
with the existing arithmetic tactic; the support statement is unchanged.
The repaired module, capstone and fourteen guards passed in run 37472300569
above. These initial diagnostics are retained as history, not current
blockers.
