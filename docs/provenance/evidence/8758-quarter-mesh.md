# Affine-mesh clearance and local layer exclusion

These six original declarations establish the numerical mesh and layer
estimates used in the initial-star argument. All distances below are measured
in the sup norm on the plane.

For an origin \(o\in\mathbb R^2\) and a real spacing \(q\), the translated
mesh is

\[
\mathcal M(o,q)=\{o+qz:z\in\mathbb Z^2\}.
\]

The actual nine marks of any finite collection of dyadic cells of side
\(2^j\) lie in \(\mathcal M(o,2^\ell/4)\) whenever \(\ell\le j+1\).
For \(q>0\), distinct mesh points have distance at least \(q\). If
\(u,v,x\) belong to the mesh, either \(u=v\) or their affine span \(L\) has horizontal,
vertical or diagonal slope, and \(x\) lies outside \(L\), then

\[
\|x-y\|_\infty\ge q/2\qquad(y\in L).
\]

The case \(u=v\), in which the affine span is a single point, is included.
For the quarter mesh \(q=t/4\), these estimates give separation \(t/4\)
and clearance \(t/8\).

Write \(t_k=2^{\lfloor\zetak\rfloor}\). For \(C\ge2\) and
\(k\ge50{,}000{,}000\), let \(x\in\overline{D_k}\) and
\(y\in\overline{D_h}\), where the closed dyadic layers have the same
origin, finite endpoint set and parameter \(C\). If \(k+2\le h\) or
\(h+2\le k\), then

\[
\|x-y\|_\infty\ge16t_k.
\]

Consequently, \(\|x-y\|_\infty<10t_k\) implies
\(h\le k+1\) and \(k\le h+1\). The index threshold is uniform in
\(h\), the origin, the endpoint set and the points. No nonemptiness
hypothesis is imposed on the endpoint set.

## Source, attribution and scope

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.

The mesh estimates are the numerical step in the proof of
`geometry:initial-stars`, lines 352–359, within the proof of
`prop:two-families`. Local layer exclusion uses lines 352–356, the earlier
`geometry:nonadjacent` estimate in lines 193–204, and the scale definitions
and comparison in lines 200–207. The explicit threshold and constants are
stated in separate blueprint entries for these numerical consequences.

The proofs are independently written; no upstream Lean source or proof text
is reused. OpenAI Codex (GPT-6) assists LionSR under the existing
[TNLean #8758 mesh claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6044056435)
and its
[local-layer extension](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6044139454).

The remaining geometric construction includes active interfaces, fan coloring,
minimum incident-scale assignment to marks, isolated stars, contact completeness,
repairs, descendant counts and the complete two-family partition. The present
numerical consequences do not establish the isolated-star lemma or either
manuscript headline theorem.

## Exact source and canonical evidence

Exact verified source: `5db13f626cbba4ce128e25ddcdb60a00532f0f3a`.
The six audited declarations are:

- `TNLean.PEPS.AreaLaw.Geometry.affineMesh`;
- `TNLean.PEPS.AreaLaw.Geometry.beltMarks_subset_affineMesh`;
- `TNLean.PEPS.AreaLaw.Geometry.affineMesh_dist_ge`;
- `TNLean.PEPS.AreaLaw.Geometry.affineMesh_line_dist_ge`;
- `TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_dist_nonadjacent_fineScale`;
- `TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_nearby_indices`.

| Check | Actual command | Exit code | Elapsed seconds |
|---|---|---|---|
| Combined Geometry target | `lake build TNLean.PEPS.AreaLaw.Geometry` | 0 | 13.186 |
| Imported six-name audit | `lake env lean docs/provenance/evidence/8758-quarter-mesh-axioms.lean` | 0 | 4.067 |

`LocalLayers` compiled in 7.3 seconds, `MeshGeometry` in 7.6 seconds and the
Geometry aggregator in 2.6 seconds, without warnings. All six exact imported
names report only `propext`, `Classical.choice` and `Quot.sound`. The build
and imported audit both completed successfully. The signatures and proofs
of all six declarations also passed independent mathematical review.

The canonical commands ran from the warmed TNLean worktree under the shared
repository lock through `scripts/lake_build_locked.sh --`, reusing the
pinned prebuilt Mathlib artifacts. The driver completed and released the
lock. The source-only preparation worktree was clean at the frozen source,
had no `.lake` directory and performed no cache or build operation. Its
source passed non-mutating elaboration with all package options from the
warmed environment; the MeshGeometry direct check took 4.39 seconds without
warnings.

Evidence log paths and SHA256 hashes:

- `8758-quarter-mesh-build.log`: `6ad0b19d4c0fba077c3def34ce484e8f1b1d41d4b380f985b3441ef894554499`;
- `8758-quarter-mesh-axioms.log`: `5261ea8137ac50ac96fdd396d3e10baef28c76aeb1b4436ae820c10a985145ce`.

Each log records the actual command, frozen source revision, elapsed time
and exit code. Captured output has trailing whitespace removed; build
diagnostics and the actual quoted axiom results are preserved.

## Provenance and integration

The complete 221-entry current-policy provenance/source/license/notice
validation passes, including exact source and audit bytes at the frozen
revision, command headers, evidence hashes and all six quoted imported
names. Promotion changes precisely the six new entries in
`docs/provenance/openai-math.d/8758-quarter-mesh.json` to
ported/declared/passed. All prior 215 entries remain byte-identical to the
baseline at `98d26cdad5e212a7e241951618dd3645f3ae6b21`. This prior inventory
includes the previously existing planned root-ledger entry; the completed
parent proof entries retain their actual verified source and evidence.

Complete blueprint source synchronization and reverse coverage passed with
20,175 distinct public references and 20,169 theorem-like entries. No missing
or duplicate references were reported. The six new blueprint declaration
tags are distinct and match the independently reviewed statements and their
explicit hypotheses.

Three short slope-normalization blocks in one file are recorded as a tactic
pattern candidate. The criterion for promotion across at least two files is
not met.

The earlier primary-region work recorded a local whole-library
`leanblueprint checkdecls` failure caused by a missing pre-existing
`Fibonacci.olean` artifact. That historical failure log remains intact;
the unrelated check was not repeated locally for this contribution.
Full-library CI, compiled blueprint declaration checking and rendering
remain pending. Publication accompanies this completed evidence record.
