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
The implementation is cloud-only. MPU-gauging source and the import
generator logic are unchanged. The generated import frontier,
one strict regression entry, and one chapter include are integrated after
the parent task's explicit review authorization.

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

## Regression and validation status

`TNLeanTest/JointMixedEndpointPeriodicGap.lean` uses two scalar blocks with
physical columns `(1,0)` and `(1,1)`. Their inner product is one, while
they span the product algebra simultaneously. The regression specializes
the actual ground-space, common-gap, active-operator and phase-count
statements to this overlapping family. It checks the two-site count,
empty labels, zero physical alphabet, and strict standard-axiom guards.

The focused blueprint leaf is
`blueprint/src/chapter/ch30_mpo_joint_periodic_endpoint.tex`. It states
the mathematical restrictions explicitly and contains no checked markers
until native compilation succeeds.

At this source checkpoint, Lean/Lake and cache activity are reserved for
the parent's serialized build slot. Native checks, strict regression,
and the affected CI integration remain pending. Documentation checks so
far are:

- The changed-declaration source scan reports complete reverse blueprint
  coverage. The unseeded worktree's all-repository scan reports missing
  dependency-source references; none belongs to the new leaf.
- The focused PDF and web builds succeed. All 88 new declaration-owner
  links occur in the generated HTML. There are no checked markers before
  native validation.
- The three new mathematical pages, PDF pages 3–5, were rendered and
  visually inspected. Their displayed formulas fit the page, references
  resolve, and the corner boundary is explicitly `P_b X P_a`. The copied
  context has one overfull box in the existing canonical-gap theorem's
  long title; the new leaf has none.
- The native Tenkz event audit passes with no hard errors or advisories.
  The focused context contains one inherited tensor panel; this leaf adds
  no diagram. The supported PDF-to-SVG fallback renders the web panel.
- Generated HTML passes the repository's raw-source reader checks.
  Chromium's phone/desktop reader checks are blocked by the executor's
  denial of singleton socket creation, including an approved escalated
  launch. No browser success is claimed.
- Formatting uses the pinned latexindent 3.24.7 and repository settings.

The local documentation evidence is
`/workspace/shared/glm23-blueprint-validation/joint-periodic-focused/verification.json`.
It records the exact rendered source and output hashes; it will be refreshed
after the native checks and final checked-marker update.
