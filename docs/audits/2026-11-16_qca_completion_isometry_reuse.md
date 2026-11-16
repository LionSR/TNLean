# Canonical-map and completion reuse in QCA

Audited base: `18ef7315513d2d1f235af1ade0664605f33ef716`.
Submission base: `73007e10337424b3556fb198507b2157f99f19a3`; the selected
source files and dependency pins are unchanged between these revisions.
Selected batch: **13 proofs across nine QCA modules, net −58 Lean lines**.
This is independent of the consolidation stack #10676 → #10677 → #10678.

## Mathematical contracts

An additive map preserving every norm is an isometry, without a completeness
assumption. Two continuous maps out of a completion agree everywhere when
they agree on the original dense algebra. A closed property holding on that
dense algebra holds on the completion. These existing mathematical results
replace repeated distance expansions, completion inductions and manual
closure-minimality arguments.

The algebraic-local algebras remain incomplete. In particular,
`ForwardNormPreserving` is still an explicit, used hypothesis; automatic
C-star isometry is used only for completed C-star algebra equivalences.
Every existing public header, hypothesis, conclusion, definition, import and
attribute is retained. The positive local-dimension and block-length
assumptions stay unchanged, and finite-region statements still quantify over
empty regions. Norm-closed support generation is not strengthened to an
algebraic generation claim.

## Selected occurrences

All declaration names below have the `SpinChain.` prefix.

| Module | Reused proof sites | Before → after |
| --- | --- | ---: |
| LocalNorm | `localObservable_isometry` | 192 → 185 |
| QuasiLocal | `quasiLocalObservable_isometry` | 124 → 123 |
| AlgebraicTranslation | `algebraicLocalTranslation_isometry` | 318 → 315 |
| AlgebraicBlocking | `algebraicLocalBlocking_isometry` | 385 → 383 |
| QuasiLocalTranslation | `quasiLocalTranslation_zero`, `quasiLocalTranslation_add` | 205 → 192 |
| BlockingTranslation | `quasiLocalBlocking_translation` | 269 → 264 |
| CompatibleLocalAutomorphism | `algebraicEquiv_isometry`, `translationCovariant_quasiLocalEquiv` | 300 → 292 |
| CompatibleLocalState | `quasiLocalFunctional_unique` | 181 → 180 |
| SupportAlgebraGeneration | `quasiLocalStarAlgHom_ext_evenPair`, `commute_of_forall_commute_image_evenPair`, `PropagatesWithin.supportAlgebraJoin_topologicalClosure_eq_top` | 496 → 478 |

For example, local inclusion formerly expanded the distance of two images,
rewrote subtraction through several homomorphism projections, and invoked norm
preservation at their difference. It now applies the existing additive
norm-to-isometry theorem to the same norm equality. Translation composition
still proves the same equality on algebraic-local observables; completion
extensionality supplies the continuous extension. The support proofs still
use the closed preimage under the automorphism and evaluate at its inverse.

## Existing owners and scope checks

Pinned Mathlib: `625d8914199bc567cca9b91f90e8e5afafa5ae51`.

- `AddMonoidHomClass.isometry_of_norm`: Analysis/Normed/Group/Uniform,
  additive form of lines 114–123.
- `UniformSpace.Completion.ext` and `ext'`:
  Topology/UniformSpace/Completion, lines 414–422.
- `DenseRange.induction_on`: Topology/DenseEmbedding, line 358.
- `ContinuousLinearMap.fromCompletion_unique`:
  Topology/Algebra/LinearMapCompletion, line 90.

No new mathematical declaration, tactic or simp attribute is introduced.
This dated pattern inventory leaves the central tactic ledger with its
current #10677/#10629 owners. The families meet the rule of three and use
existing Mathlib lemmas rather than adding parallel abstractions.

The audit inspected all 58 open PR file lists before selection, with no
overlapping QCA file. It also checked the existing QCA support-factor and
shared-coordinate audits and open/closed completion-related cleanup records.
The historical QCA support-generation scope remains in force. Existing
Blueprint statements, labels, tags and density-based proof sketches remain
appropriate; no Blueprint file is changed.

## Deferred and rejected candidates

- Normalized-column isometries and unitary preparation repeat across
  UnequalMERA, BinaryMERA, StaircasePreparation, SequentialNoAncilla and
  ShortChainPreparation. Estimated saving: 30–50 lines. The pinned upstream
  library lacks the convenience theorem, and the existing extension owner
  is occupied by #10676; defer the ownership decision.
- Circuit operator placement repeats in PortChannelRouting,
  PhysicalPortLocalDilation, EncodedChannelLayer, PairProduct and
  SiteEmbedding. A shared star-algebra homomorphism could save 25–45 lines,
  but adds a new object and its positivity entry touches excluded area-law
  scope; defer a separate placement batch.
- Six embedded fixed-point-pair orthogonality calculations have only 10–20
  estimated net lines after a shared statement. Keep positive-semidefinite
  and empty-index cases; do not open a small isolated PR.
- Scalar-Gram normalization in UnitaryKronecker has an upstream theorem but
  is currently a single-file candidate; retain it for a larger related batch.
- QCA blocking aliases and bipartite range composition need header migration
  or additional coercion validation. They are outside this proof-only batch.
- Positivity and contractivity completion inductions prove inequalities;
  equality-extension theorems do not replace them.

## Validation and consolidation status

Static validation compares exact-main source blobs, all public declaration
headers and all imports, scans new proof text for prohibited terms and line
length, checks whitespace and added prose, and runs the tactic-pattern scan.
The changed Blueprint-cited statements and their original density arguments
are retained. This is static evidence, not compiler acceptance.

Local Lean/Lake and the prebuilt cache are absent. Toolchain download checks,
including a network-enabled execution request, returned an HTTP 403 proxy
response. No Mathlib source build was attempted. Required hosted acceptance
is strict checking of the nine changed modules, the full root build,
compilation-time checks and compiled declaration/Blueprint validation at the
final head with the unchanged pinned dependencies.

At selection, #10677 had passed strict directly changed-source checks and
changed-module builds and was running its full build. #10676 and #10678 were
still in setup/build. No fresh proof or Blueprint approval had posted; all
three heads and all 13 source drafts were untouched. Their exact-head CI
and review gates remain separate from this independent batch. No merge or
source-PR closure is authorized by static coverage alone.

The QCA tactic scan leaves two existing three-line prefixes: configuration
split-coordinate extensionality and centralizer membership expansion. Neither
prefix is a complete proof or a new duplicated result. The centralizer sites
already use Mathlib's membership characterization; the coordinate arguments
have different remaining boundary conditions. They are deferred rather than
introducing a tactic for a shared prefix.

The first integrated #10678 strict check later found unfixed interval
endpoint goals in all three Gaussian split rewrites. Commit
`064e2daa74705ba3d455de0cf685942bee9b0acf` specifies the same original
interval explicitly and retains every statement and the net line count.
Focused source builds had succeeded; fresh strict/full final-head acceptance
is pending. The independent QCA changes are not included in that repair.
