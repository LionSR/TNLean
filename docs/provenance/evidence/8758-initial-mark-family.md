# A finite family of separated initial marks

The four original declarations select actual sparse-belt shifts throughout
the dyadic layers, bound their initial marks, assign smallest incident sides
and prove separation of distinct marks. The marked points are the actual
center, corners and side midpoints of the selected cells.

For every origin, finite lattice domain, cut and natural parameter $C$, the
first result chooses actual residue functions $a,b$. At layer $k$, their
values belong to the finite residue set modulo $q_k=2^{p_k-\ell_k}$, where
$p_k$ and $\ell_k$ are the prescribed pitch and fine-cell exponents. Let
$F_k$ denote the actual selected belt-cell indices. Then, for every natural
$k$,

$$
|F_k|\le64(2C+1)^2\,|\partial_\Lambda A|\,2^{-\delta_0 k/2},
$$

and $\{k:F_k\ne\varnothing\}$ is finite. This support may be empty;
no nonemptiness of the domain, boundary or selected family is assumed.

The second result chooses a constant $B>0$ before the origin, finite domain,
cut, natural parameter $C$ and lower index $k_0$. For these arbitrary data,
it supplies actual residue functions retaining both the estimate in every
layer and finite support. Write $\mathcal M_k$ for the union of the nine
actual marks of each cell indexed by $F_k$. It provides a finite set $M$
satisfying

$$
x\in M\quad\Longleftrightarrow\quad
\exists k\ge k_0,\quad x\in\mathcal M_k,
$$

and

$$
|M|\le B(2C+1)^2\,|\partial_\Lambda A|.
$$

Thus $M$ is exactly the deduplicated union of the actual initial marks of
all selected belt cells at layers $k\ge k_0$. The positive constant is
chosen as 576 times the numerical finite-sum bound for polynomial exponent
zero. The coefficient 576 is 9 × 64. Only this initial-mark contribution is
counted.

## Smallest incident sides and separation

The third declaration in `InitialMarkFamily.lean` again chooses a positive
constant $B$ before all geometric data. Under $C\ge2$ and
$k_0\ge50{,}000{,}000$, it retains the chosen residues, estimates in every
layer, finite support, exact finite mark set and cardinality bound. It also
supplies $S:M\to\mathbb R$, defined on the actual marks, with the following
properties:

- $S(v)>0$ for every $v\in M$.
- For each $v\in M$, an actual selected cell at some $k\ge k_0$ marks
  $v$ and has side exactly $S(v)=2^{\ell_k}$.
- Every selected cell at any $h\ge k_0$ that marks $v$ has side at least
  $S(v)$.
- If $v,w\in M$ are distinct, then
  $\|v-w\|_\infty\ge\max(S(v),S(w))/4$.

The witness and comparison properties make $S(v)$ the actual smallest
incident side. The layer attaining that side need not be unique. A least
incident index is used only inside the proof.

The separate `FineMarkSeparation.lean` theorem applies to every actual
fine-layer cell. For arbitrary origin and finite endpoint set, assume
$C\ge2$ and $k,h\ge50{,}000{,}000$. Let $z$ and $w$ be actual fine-layer
cell indices at layers $k$ and $h$, respectively. If $x$ and $y$ are distinct
members of their nine-point cell-mark sets, then

$$
\|x-y\|_\infty\ge\frac{\max(2^{\ell_k},2^{\ell_h})}{4}.
$$

The selected belt cells are included in these fine-layer index sets, so this
estimate applies to their actual marks. No endpoint-set nonemptiness is
assumed. Smallest incident sides and separation in the global theorem are
proved for the chosen finite family.

## Source, attribution and scope

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.

The per-layer shift choice and geometric decay are in `geometry:belt-count`,
lines 220–233. The actual nine belt-cell marks and deduplication are in
lines 325–330. The smallest incident side is assigned in lines 327–329;
the separation assertion is `geometry:initial-stars`, lines 332–339, with
its numerical proof in lines 352–363. The summation
in the counting argument is in lines 668–692, including
`geometry:total-repairs`, within the proof of `prop:two-families`.

The present contribution treats the initial belt-cell families, their
initial marks, smallest incident sides and mark separation. Active rays
and sectors, fan coloring, recursive replacements, descendant counts and
the full total-repairs estimate remain separate mathematical obligations.
Neither the complete two-family partition nor either manuscript headline
theorem is established by these statements.

The proofs are independently written; no upstream Lean source or proof text
is reused. OpenAI Codex (GPT-6) assists LionSR under the existing
[TNLean #8758 claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6044473740)
and its [separation extension](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6044749108).

## Exact source and canonical evidence

Exact verified source: `5d2246bb32045fafea826200dd09b3518629ae97`.
The four audited declarations are:

- `TNLean.PEPS.AreaLaw.Geometry.exists_finitely_supported_sparse_belt_shifts`;
- `TNLean.PEPS.AreaLaw.Geometry.exists_uniform_initial_mark_bound`;
- `TNLean.PEPS.AreaLaw.Geometry.exists_uniform_separated_initial_marks`;
- `TNLean.PEPS.AreaLaw.Geometry.fineLayer_marks_dist_ge`.

The first three belong to `InitialMarkFamily.lean`; the last belongs to
`FineMarkSeparation.lean`. The two earlier initial-family proof texts are
unchanged by the separation extension. Independent mathematical review
approved the four signatures, proof arguments and empty cases.

| Check | Actual command | Exit code | Elapsed seconds |
|---|---|---|---|
| Combined Geometry target | `lake build TNLean.PEPS.AreaLaw.Geometry` | 0 | 29.380 |
| Imported four-name audit | `lake env lean docs/provenance/evidence/8758-initial-mark-family-axioms.lean` | 0 | 4.380 |

`FineMarkSeparation` compiled in 18 seconds, `InitialMarkFamily` in 3.5
seconds and the Geometry aggregator in 2.8 seconds, without warnings.
All four exact imported names report only `propext`, `Classical.choice`
and `Quot.sound`.

The canonical commands ran from the existing warmed TNLean worktree under
the shared repository lock, through `scripts/lake_build_locked.sh --`,
reusing the pinned prebuilt Mathlib artifacts. The source-only preparation
worktree had no `.lake` directory and performed no cache or build operation.
Its source also passed non-mutating elaboration with the package options
from the warmed environment, without warnings.

Evidence log paths and SHA256 hashes:

- `8758-initial-mark-family-build.log`: `4b5495b1af70004935fbd373e220e6587990929d3fcf3a405506c05da1fde4dd`;
- `8758-initial-mark-family-axioms.log`: `76a58109b7ea15c6b9ac6981a5850915beb65b64aad8a8197d8e347b2f6a94d9`.

The actual logs record the command, frozen revision, elapsed time and exit
code. Only trailing whitespace was normalized; build diagnostics and the
quoted axiom reports are preserved.

## Provenance and integration

Strict static promotion passed for precisely the four new entries in
`docs/provenance/openai-math.d/8758-initial-mark-family.json`. The complete
225-entry current-policy provenance/source/license/notice audit passes,
including exact module and committed audit bytes at the verified source,
actual command headers, log hashes and all four imported names.

The prior 221 entries are byte-identical to the completed parent baseline
at `436ea587677e61b2e971555cdf612ba1be6006cd`. Their proof sources and evidence
remain unchanged. This prior inventory contains the previously existing
planned root-ledger entry; it is not a claim that all 221 entries have been
compiled. The six mesh/locality parent entries retain their actual verified
source revision and logs.

Complete blueprint source synchronization passed with 20,179 distinct
public references and 20,173 theorem-like entries; the full JSON report has
`sync_ok: true`, and no missing, stale or duplicate references. Reverse
coverage reports no changed declarations missing blueprint entries. The
four new entries have distinct declaration tags and checked proof tags.
Formatter idempotence and generated-import checks passed.

The earlier primary-region work recorded a local whole-library
`leanblueprint checkdecls` failure caused by a missing pre-existing
`Fibonacci.olean` artifact. That historical failure log remains intact; the
unrelated check was not repeated locally for this contribution. Full-library
CI, compiled blueprint declaration checking and rendering remain pending.
Publication is on `feat/area-law-initial-mark-family`, stacked on
[#8859](https://github.com/LionSR/TNLean/pull/8859). The pull request records
the published evidence revision; the verified proof revision remains the
exact frozen source above.
