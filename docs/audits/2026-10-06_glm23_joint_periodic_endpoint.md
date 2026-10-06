# GLM23: the actual degenerate periodic endpoint

## Source and scope

The source is GLM23 v3, `Papers/2203.12563/REsubmission.tex`, lines
1695–1777. The actual mixed family and insertions are those already defined
in `JointMixedEndpointFamily` and `JointMixedEndpointSupport`.
This work studies the first endpoint, parameter zero, on periodic chains
of every length at least two. It does not address the open-boundary
comparison, the gap uniformly near an endpoint, MPO commutation, or the
complete phase classification.

The isolated branch starts at `476769cd544b256dcd30d1df465f90896ac60db6`,
whose tree is `08eae47dac442d89a13640c9b3473386f39d0add`.
The implementation is cloud-only. The generated import frontier, one strict
regression entry, and one chapter include integrate this package.

## Sibling integration reconciliation

This branch remains stacked on the checked actual-family checkpoint
above, corresponding to public pull request #8720 head
`8f48b5cc8b133f7df4c3368ef725b13963681932`. The additive work in sibling
#8721 is not imported or edited. A later combined branch must retain both
sets of additions in these four shared integration files:

- `TNLean/MPS/ParentHamiltonian/Martingale.lean`: this branch adds
  `ReducingProjectionGap`; #8721 adds `DependentSpectatorGapEquivalence`.
- `TNLean/MPS/Symmetry/MPOSymmetry.lean`: this branch adds the seven
  periodic-support modules; #8721 adds `JointMixedEndpointBoundaryColumns`
  and `JointMixedEndpointSpectatorGap`. Regenerate rather than hand-edit
  the aggregator after combining them.
- `.github/workflows/pr-ci.yml`: this branch adds only
  `JointMixedEndpointPeriodicGap` to the existing strict mixed-endpoint
  loop. #8721 separately adds `JointMixedEndpointBoundaryColumns` and
  `DependentSpectatorGapEquivalence`. Preserve all three entries and all
  strict options.
- `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex`: this branch adds
  `ch30_mpo_joint_periodic_endpoint`; #8721 separately adds
  `ch30_mpo_joint_boundary_columns` and `ch30_dependent_spectator_gap`.

The new production proof files and regression files do not overlap.

## Joint physical and virtual support

Write `P_x = I_(D0 x) ⊕ 0`, and let `R_i`, `C_i` select row and column
phase zero at physical site `i`. The virtual identities are derived from
the actual four-summand letters:

- `P_x C_x^μ = r(μ) C_x^μ` and `C_x^μ P_x = c(μ) C_x^μ`
- `R_0 Γ′_(2,W)(X) = Γ′_(2,W)(X P)`
- `C_1 Γ′_(2,W)(X) = Γ′_(2,W)(P X)`
- At `W=P`, `C_0 Γ′_2(X) = R_1 Γ′_2(X) = Γ′_2(X)`

The four virtual corners `P_b X_x P_a` therefore occupy the four distinct
physical phase pairs `(00,00)`, `(00,01)`, `(10,00)`, and `(10,01)`.
The actual extended support is the orthogonal sum of these four phase
supports. Labels inside the common `00` physical alphabet are retained
jointly; no exact physical orthogonality of different block labels is
assumed or inferred.

The `00 × 00` compression is precisely the full joint canonical support
of `jointMixedEndpointLeftTensor A₀ d₁ D₁`. Explicit boundary compression
gives the equality, and reducing orthogonal projections give
`Π_G = R_0 C_1 Π_S`. In particular, with `h′=I−Π_S` and `k=I−Π_G`,

```
0 ≤ h′ ≤ k ≤ h′ + (I−R_0) + (I−C_1)
I−C_0 ≤ h′
I−R_1 ≤ h′
```

## Cyclic constraint counting

The phase penalty is
`E_N = Σ_(i : Fin N) ((I−R_i)+(I−C_i))`.
It acts diagonally by the nonnegative integer count of failed row and
column phase conditions. Its kernel consists exactly of all-`00`
configurations, with orthogonal projection `Q_N`.

Each site occurs once as a first column and once as a second row in the
oriented periodic interaction sum. Therefore the actual local constraints
give `I−Q_N ≤ E_N ≤ 2H′_N`. This yields the fixed inactive-sector energy
bound `1/2`; the constant is derived, not assumed. At `N=2` there are two
directed interaction summands. The proof never assumes that predecessor
and successor are different sites.

Local phase reduction extends to every cyclic placement and spectator
site. Thus `E_N` and `Q_N` commute with the actual Hamiltonian. Summing the
local canonical comparison gives
`H′_N ≤ K_N ≤ H′_N + E_N`.
Since `E_N Q_N=0`, positivity of `K_N−H′_N` implies the exact equality
`H′_N Q_N = K_N Q_N`.

The penalty forces every actual zero-energy vector into `Q_N`, so the
actual and common canonical kernels agree. The canonical input is the
joint block-parent theorem at simultaneous span length one and interaction
range two, applied directly to the embedded first family on the common
enlarged physical alphabet.

## Gap and degeneracy

The terminal hypotheses are the original two simultaneous one-site spans
and positive first endpoint block dimensions. Positivity of the second
endpoint dimensions is unnecessary for this first-endpoint result; no
extra source assumption is added.

The periodic kernel is the range of the actual path's component-vector
map. Right-absorbing virtual compression identifies each actual
zero-parameter component vector with the embedded original endpoint vector
at every positive length. For a single common
canonical gap `δ>0`, splitting `v=Q_Nv+(I−Q_N)v` gives the actual gap
`min(δ,1/2)`. The proof transports orthogonality to the common kernel
explicitly and uses the two vanishing cross terms. It never takes a
minimum of separate block gaps.

The enlarged physical dimension is split into zero and nonzero cases.
If it is zero, every positive-length chain vector is zero, so the kernel
and gap statements are direct. Empty block families are permitted both
with empty and nonempty physical alphabets. No `NeZero d₀` or nonempty
label assumption is introduced.

## Regression and validation

`TNLeanTest/JointMixedEndpointPeriodicGap.lean` uses two scalar blocks with
physical columns `(1,0)` and `(1,1)`. Their inner product is one, while
they span the product algebra simultaneously. The regression specializes
the actual ground-space, common-gap, active-operator and phase-count
statements to this overlapping family. It checks the two-site count,
empty labels, zero physical alphabet, and eleven strict standard-axiom
outputs, each exactly `propext`, `Classical.choice`, and `Quot.sound`.
The hash-command style linter is disabled only inside the axiom-check
section; all other strict regression options are retained.

The complete proof source was validated at public commit
`7526a088de379402132b015c8186ec879e07fa42`, corresponding to local commit
`32824148466899720e3c56177137efede41dca81` and tree
`ac5687ca14e45044681900f2f9a99268d7e476a6`.
The tested merge `1e95f7a547c63f7195e768676fde437d0af1bd00` has this same
exact tree. All eight checks passed in
[CI run 37446115075](https://github.com/LionSR/TNLean/actions/runs/37446115075).
The Lean build job, `112211268126`, passed the production build, strict
regression, compiled blueprint declaration check, style, and timing gates.
The new production modules took 6.5, 9.3, 10, 12, 11, 12, 33, and 9 seconds
respectively for the generic helper, selectors, canonical corner, reducing
sectors, orthogonal corners, projector comparison, periodic sectors, and
periodic kernel/gap. Each lies below the 50-second changed-module ceiling.

All 88 public declaration owners are compiled and indexed. The focused
blueprint leaf,
`blueprint/src/chapter/ch30_mpo_joint_periodic_endpoint.tex`, now marks
its eleven entries and eight proofs checked. This documentation-only
checkpoint preserves the validated production and regression source;
CI for the final documentation head remains pending until publication.

Local bottom-up checks also passed the seven lower production modules.
The capstone warmup lost its execution handle before elaborating the final
module; no terminal result is claimed for that interrupted local session.
The exact-tree CI above supplies the complete proof and guard evidence.

Documentation checks are:

- The changed-declaration source scan reports complete reverse blueprint
  coverage. Full source synchronization and compiled declaration checking
  pass in the exact-tree CI environment.
- The focused PDF and web builds pass with the checked markers. All 88
  declaration-owner links occur in the generated HTML, with eleven
  checked entries and eight checked proofs.
- The three mathematical pages, PDF pages 3–5, were rendered and visually
  inspected. Their displayed formulas fit the page, references resolve,
  and the corner boundary is explicitly `P_b X P_a`. The copied context
  has one overfull box in the existing canonical-gap theorem's long
  title; the new leaf has none.
- The native Tenkz event audit passes with no hard errors or advisories.
  The focused context contains one inherited tensor panel; this leaf adds
  no diagram. The supported PDF-to-SVG fallback renders the web panel.
- Generated HTML passes the repository's raw-source reader checks. The
  full blueprint job, including browser reader checks, passes in CI.
  The local Chromium run remains blocked by the executor's denial of
  singleton socket creation, including an approved escalated launch;
  no local browser success is claimed.
- Formatting uses the pinned latexindent 3.24.7 and repository settings.
  Reader-facing prose, generated import consistency, and whitespace checks
  pass.

The adjacent validation JSON records the exact Lean and blueprint source
hashes, CI source and tested-tree identities, focused render hashes,
declaration owners, and local browser limitation.
