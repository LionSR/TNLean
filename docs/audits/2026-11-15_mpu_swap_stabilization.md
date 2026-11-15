# Swap comparison with a common identity ancilla

Status: all 32 declarations compiled at `67bdbc2e`. The three transport and
obstruction modules also passed focused strict checks at that head. The
five-declaration physical-matrix module has one unused-simp warning, repaired
without changing statements; its clean strict check and full CI remain pending.
The original source entry is unfinished. Initial source checkout:
`cbf482955f46f36c71c95ab1547b3cc86b6d58c2`.


Hosted checks and the transitive axiom audit at `99005136` used the tested
merge with main, whose QICLean pin is `603fc408`. The older feature snapshot
retains `c4576824`; this PR does not change dependency inputs. The local-pin
statements below record the initial workspace, not the effective merged CI inputs.

## Ownership and existing work

On 2026-11-15, [#7574](https://github.com/LionSR/TNLean/issues/7574) was open
and had no assignee. Searches for open PRs mentioning `7574`, an open PR with
`swap` in its title, and an open PR mentioning `stabilization` returned no
matches. These searches do not establish that there is no unpublished work.

[Merged #8572](https://github.com/LionSR/TNLean/pull/8572) already proves all
three strict comparisons and their common-positive-blocking versions. Despite
an older issue comment describing a fixed virtual dimension, its final body and
the current signatures allow arbitrary `Da` and `Db`: `padBond` embeds both
endpoints into a common virtual dimension. Unequal virtual dimensions therefore
are not a new obligation. The issue's last two comments identify identity-ancilla
stabilization as remaining work.

[#6017](https://github.com/LionSR/TNLean/issues/6017) remains open with no
assignee and owns the general equivalence definitions and standard-form path
criterion. [#7528](https://github.com/LionSR/TNLean/issues/7528) is closed. This
reduction introduces no competing general path-equivalence predicate and proves
no phase classification.

Source: `Papers/1703.09188/paper_v2.tex`, `SSymmetries`, lines 1301--1322;
`def:equivalent-symmetry`, lines 1356--1366; and `lemma:sym-trafo-swap`,
lines 2065--2085. The one-sided transformation below uses `threeMPU2`,
lines 2053--2063, with the correction already recorded in
`docs/paper-gaps/mpu_swap_symmetry_one_sided.tex`.

## Full actions after adjoining an ancilla

Fix positive integers $d,x,k$. Put $H=\mathbb C^d\otimes\mathbb C^d$,
$A_x=\mathbb C^x$, and let $S$ exchange the two factors of $H$.
On one enlarged site define

$$Q_x=S\otimes I_{A_x}.$$

Use exactly the product basis underlying `tensorPhysicalId`: a site is indexed
by $(i,a)$ with $0\leq i<d^2$ and $0\leq a<x$, flattened to $ix+a$.
If $i=rd+s$, then $Q_x$ is the permutation
$(r,s,a)\mapsto(s,r,a)$. Consequently
$Q_x^2=I$, $Q_x^\dagger=Q_x^{\mathsf T}=Q_x$, and
$\overline{Q_x}=Q_x$. The ancilla is unchanged by this permutation.

For $N>0$, write $C_{x,N}=Q_x^{\otimes N}$. Define the following actions on
**every** operator $X$ on $(H\otimes A_x)^{\otimes N}$:

$$
\mathcal D_{x,N}(X)=C_{x,N}X^\dagger C_{x,N},\qquad
\mathcal T_{x,N}(X)=C_{x,N}X^{\mathsf T}C_{x,N},\qquad
\mathcal K_{x,N}(X)=\overline X.
$$

The target actions are ordinary adjunction, transposition, and conjugation,
respectively. These formulas specify the actions outside the identity-ancilla
image, which is essential because the comparison path can leave that image.
They are a concrete choice preserving the distinguished two physical species;
the source does not determine this choice from a symmetry at dimension $d^2$
alone.

Let $R_N:H^{\otimes N}\otimes A_x^{\otimes N}\to
(H\otimes A_x)^{\otimes N}$ be the product-basis permutation, and let
$\iota_x(X)=R_N(X\otimes I)R_N^{-1}$. Then
$C_{x,N}=R_N(S^{\otimes N}\otimes I)R_N^{-1}$. Since $R_N$ is a real
permutation, adjunction, transposition, and conjugation commute with its
reindexing. Kronecker multiplication therefore gives

$$
\mathcal D_{x,N}(\iota_x(X))
 =\iota_x(S^{\otimes N}X^\dagger S^{\otimes N}),\qquad
\mathcal T_{x,N}(\iota_x(X))
 =\iota_x(S^{\otimes N}X^{\mathsf T}S^{\otimes N}),\qquad
\mathcal K_{x,N}(\iota_x(X))=\iota_x(\overline X).
$$

Thus all three extensions respect the actual ancilla embeddings. This does not
assert a dimension-only family independent of the chosen factorization.

## Comparison on arbitrary enlarged operators

Write $C=C_{x,N}$. For every enlarged operator $X$, including operators outside
the image of $\iota_x$, the map $L(X)=CX$ satisfies

$$
L(\mathcal D_{x,N}(X))=X^\dagger C=(CX)^\dagger,\qquad
L(\mathcal T_{x,N}(X))=X^{\mathsf T}C=(CX)^{\mathsf T},\qquad
L(\mathcal K_{x,N}(X))=C\overline X=\overline{CX}.
$$

Here $C^2=I$ gives the first equality in the adjunction and transposition
calculations; $C^\dagger=C^{\mathsf T}=C$ and $\overline C=C$ give their
second equalities and the conjugation calculation. Since $L^2=\mathrm{id}$,
these intertwining identities prove all three fixed-equation equivalences:

$$
CX^\dagger C=X\iff(CX)^\dagger=CX,\qquad
CX^{\mathsf T}C=X\iff(CX)^{\mathsf T}=CX,\qquad
\overline X=X\iff\overline{CX}=CX.
$$

No unitarity assumption on $X$, ancilla-image assumption, or supplied
symmetry-transport certificate is used in these identities.

## Tensor endpoints, blocking, and virtual padding

Let $F_x$ be left multiplication by $Q_x$ on the physical output leg of an
arbitrary local tensor. Its entries are finite linear combinations of tensor
entries, so $F_x$ is continuous. It is an involution, and its periodic operator
is $C_{x,N}W^{(N)}$. Therefore it preserves the MPU locus in both directions.

Let $U$ have physical dimension $d^2$ and any virtual dimension. Identity
ancilla attachment has coefficients
$U^{(x)}_{(i,a),(j,b)}=U_{i,j}\delta_{a,b}$. For each output $(i,a)$ and
input $(j,b)$,

$$
(F_x(U^{(x)}))_{(i,a),(j,b)}
 =\sum_{h,c}S_{i,h}\delta_{a,c}U_{h,j}\delta_{c,b}
 =\left(\sum_h S_{i,h}U_{h,j}\right)\delta_{a,b}
 =((F_1U)^{(x)})_{(i,a),(j,b)}.
$$

The symbol $F_1$ uses the canonical identification $H\otimes\mathbb C=H$;
at the original dimension it is exactly `ketLeftMul (shiftPhysicalSwap d)`.
This coefficient identity proves that the transformed stabilized endpoint is
the identity-ancilla attachment of the transformed original endpoint.

After blocking $k$ sites, the output action is $Q_x^{\otimes k}$. Indeed, for
output word $\mathbf i$ and input word $\mathbf j$ of length $k$,

$$
(F_xW)^{[k]}_{\mathbf i,\mathbf j}
 =\sum_{\mathbf h}\left(\prod_{t=0}^{k-1}(Q_x)_{i_t,h_t}\right)
   W_{h_0,j_0}\cdots W_{h_{k-1},j_{k-1}}
 =(Q_x^{\otimes k}W^{[k]})_{\mathbf i,\mathbf j}.
$$

The scalar coefficients commute with the virtual matrices, while their order
in the final product is unchanged. The blocked action on length $N$ is the
reindexing of the unblocked length-$Nk$ action along the real configuration
permutation. It has all three fixed-equation equivalences just proved, with
$C$ replaced by $(Q_x^{\otimes k})^{\otimes N}$.

For virtual inclusion $J:\mathbb C^D\to\mathbb C^{D'}$, every physical slice
of the padded tensor is $JW_{i,j}J^\dagger$. A physical output action commutes
with this operation since
$\sum_h Q_{i,h}JW_{h,j}J^\dagger
=J(\sum_hQ_{i,h}W_{h,j})J^\dagger$.
It preserves canonical endpoints by the existing physical-unitary canonical
form theorem; it does not require the padded endpoints to be canonical.

## Result for paths and common stabilization

For every fixed $x,k>0$, apply $F_x$ after blocking as above to a continuous
path in any common virtual dimension $D'$. The resulting path is continuous,
has the transformed stabilized endpoints, consists of MPUs, and satisfies the
corresponding target symmetry at every positive chain length. The three
operator identities prove its symmetry on all intermediate tensors, without
requiring them to factor through an ancilla embedding. Applying the same
involution recovers the original path. Canonical form at both endpoints is
preserved in both directions.

Consequently, for arbitrary endpoint virtual dimensions $D_a,D_b$, each strict
comparison between $(U^{(x)})^{[k]}$ and $(V^{(x)})^{[k]}$ under the explicitly
defined enlarged and blocked swap-combined symmetry is equivalent to the
strict comparison between $((F_1U)^{(x)})^{[k]}$ and
$((F_1V)^{(x)})^{[k]}$ under the corresponding ordinary blocked symmetry.
The same $x$, $k$, $D'$, and two virtual inclusions work in both directions.
Existential quantification over $x,k>0$ therefore gives all three comparisons
with an arbitrary common identity ancilla and common positive blocking.
If MPU conditions on the original endpoints are also included, they are
preserved by the unitary involution $F_1$.

This proves the comparison for the natural labelled-spin full actions. It does
not identify the result with the current general equivalence predicate or
select an arbitrary abstract enlarged action from its restriction alone. For equal positive starting physical dimensions,
balanced positive ancilla sizes are necessarily equal, so a common ancilla
covers that balancing condition for the shift examples.

## Lean implementation boundary

The additive `TNLean/MPS/MPU/PhysicalAncillaLeftMul.lean` defines the full
reindexed Kronecker matrix $Q\otimes I_x$, its matrix properties, and the
tensor-level ancilla commutation identity. The additive
`TNLean/MPS/MPU/Examples/SwapSymmetryStabilization.lean` defines $Q_x$ using
that matrix and the two explicit swap-combined enlarged blocked actions.
Its fixed-$x,k$ and existential common-positive-$x,k$ comparisons reuse:

- `mpo_ketLeftMul` and `mpo_tensorPhysicalId` for the actual periodic operators;
- `isInvariantUnderSymmetry_iff_of_pointwise` for the three invariance statements;
- `strictlyEquivalentUnderSymmetry_iff_ketLeftMul` for canonical endpoints,
  paths, and unequal virtual dimensions;
- `blockTensor_ketLeftMul` to identify the blocked transformed endpoints.

The candidate defines ancillary actions on all enlarged blocked operators before
invoking these results. Its three internal invariance lemmas prove the required
correspondences rather than passing them through as hypotheses. Blocking is
specified directly by the matrix $(S\otimes I_x)^{\otimes k}$; no equality to
an unspecified dimension-only symmetry-family component is asserted. Endpoint
MPU guards on the original tensors are not included in these explicit strict
comparison signatures; the unitary involution preserves such guards if needed.

The two transport modules have 18 public declarations, covered by auxiliary Blueprint entries
in `ch28_mpu_swap_stabilization.tex`. Their entries are marked checked following
the exact-head strict result at `82f750c8` below; obstruction entries remain
`notready`. The source-labelled `lemma:sym-trafo-swap` is unchanged. The two generated import
aggregators are updated with the repository's generator.

The existing `EquivalentUnderSymmetry` cannot express this conclusion directly:
it requires a dimension-only coherent family and coprime balanced ancillas.
For equal positive physical dimensions, balance gives $p_a=p_b$, and
$\gcd(p_a,p_b)=p_a$ then forces both to be one. Changing that general definition
belongs to #6017; it is unnecessary to write the specialized comparison as an
explicit existential over common $x,k>0$. No second generic path predicate is
needed. The source-labelled `lemma:sym-trafo-swap` must remain unfinished until
the intended stabilization convention is settled and the result is checked.

## Initial local validation and limits

The proof was checked against the current signatures and the source equations.
The live `main` version of `Equivalence.lean` was also read through the GitHub
connector: its strict-equivalence signature still permits independent `Da,Db`.
Its reported blob hash was `5a8998b4ed052a2350af75d543e02b6ea5b48bb3`.

The temporary script `/tmp/check_7574_stabilization.py` uses independent symbolic
complex matrix entries, with conjugation represented exactly. It passed 25
cases with $1\leq d,x\leq3$, chain lengths zero through two, and operator
dimension at most 144. The checks covered 33,128 full-operator entries,
including 22,372 entries outside the identity-ancilla block support. All three
intertwining identities, involution, ancilla semiconjugacy, one-sided endpoint
commutation, and block regrouping passed. No random samples or floating-point
arithmetic were used. Script SHA256:
`082163773a597fdd3911c4ab68a029c9204ed7a5c7f9f2eb2733c3833f24168b`.
These finite checks detect coordinate mistakes; they do not replace the
universal proof or Lean elaboration. Audit whitespace and mathematical-display
delimiter checks, script syntax compilation, generated-import checks, 100-column
and proof-integrity scans of both new modules, and `git diff --check` passed.
The tactic-pattern scan ran on the MPU tree; the new proofs use the promoted
pointwise comparison and the existing generic path transport. Full source-based
Blueprint synchronization reports 563 missing dependency references because the
pinned dependency checkouts are absent. No reported missing declaration belongs
to either new module. New-declaration coverage is 18/18, with no duplicate tags.

The selected environment has no `lean`, `lake`, or `elan` executable and no
`.lake` directory. The toolchain and Mathlib pins remain `v4.36.0-rc1`; the QICLean
pin remains `c457682404aa548b4acd16ac27be5d3835e68892`. A toolchain endpoint probe
returned HTTP 403 under the environment's disabled network policy. No package
installation, cache mutation, Lean build, axiom audit, or compiled-declaration
check ran. Hosted validation is being sought through a draft candidate PR;
its eventual status must be recorded separately from these local checks.
The first hosted run at `3d82a4bd` reached the new helper module and failed on a
reindex-multiplication rewrite and a residual endpoint expansion, with three
unused-simp diagnostics. The repair uses Mathlib's reindex multiplication result
as an explicit calculation, unfolds the final ket action, and removes the unused
arguments. The mathematical signatures are unchanged; the repair still needs
hosted validation. Source-interpretation obstructions are documented separately
in `2026-11-15_mpu_swap_ancilla_obstruction.md`, with nine additional unverified
public declarations in `Examples/SwapAncillaCompatibility.lean`.

No source completion tag, general equivalence-definition change, assignment,
or merge was made.

## Exact-head check at b08bb624

Hosted run `43749029318`, build job `132918788035`, built
`PhysicalAncillaLeftMul.lean` in 4.5 seconds and reported its focused strict
check as `ok`. These nine helper declarations are checked at that exact head.
The two example modules failed: the pointwise comparison needed explicit source
and target actions, the configuration permutation matrix needed a scalar type,
and several operator-coordinate proofs needed a separate Kronecker evaluation
or an explicitly typed semiconjugacy equality. The source repair addresses those
diagnostics without changing theorem signatures.

The same run passed module policies, inline diagram semantics, and Blueprint
PDF compilation. The web job failed on three latexindent alignment differences;
the repair applies the exact reported formatting. The example-module repairs and
the complete new head remain unverified until the next hosted check. No passing
root build or new-declaration axiom audit is inferred from the helper's success.

## Exact-head check at 82f750c8

Run `43752814750`, build job `132930528266`, built
`SwapSymmetryStabilization.lean` in 3.5 seconds and reported focused strict checks
for both transport modules as `ok`. Thus all 18 transport declarations have
passed package-option build and warnings-as-errors checking at this exact head.
The five scoped transport Blueprint entries now reflect that result; the
unrestricted source entry does not change.

The obstruction module still failed on the scalar type of a permutation product,
nonterminal simplification warnings, and the literal four-to-sixteen witness.
The next repair uses Mathlib's permutation multiplication directly, keeps the
final scalar contradictions inside terminal simplifications, and evaluates the
finite literal witness. Those changes remain candidates until checked. The full
root build, compiled-reference checks, and axiom audit are still outstanding.

## Distinguished-matrix API candidate

The additive `PhysicalMatrixSymmetry.lean` retains the local matrix as physical
data. Its two full actions are $X\mapsto Q_NX^\dagger Q_N$ and
$X\mapsto Q_NX^{\mathsf T}Q_N$, where $Q_N=Q^{\otimes N}$. The construction
uses no dimension-only choice of a new swap. Adjoining an identity ancilla
replaces $Q$ by $Q\otimes I_x$; compatibility with the actual sitewise operator
embedding is derived for every operator, ancilla size, and chain length.
Ordinary conjugation has the corresponding direct compatibility theorem.
The algebraic identities hold for every complex square $Q$; the source's real
symmetric unitary involutions are a subclass. No involution property for
arbitrary $Q$ is asserted.

This is a five-declaration extension of the existing finite-chain action type,
not a replacement for the general equivalence predicates. The swap constructors
use it at the same explicitly blocked physical matrix as before, so their full
actions and all theorem statements remain definitionally unchanged. It avoids
the requirement that the original swap descend along every smaller physical
factorization. The source-labelled comparison, the arbitrary balanced-ancilla
convention, and any general equivalence revision remain open.

The five new declarations and their two Blueprint entries remain candidates
until hosted Lean checks pass. Generated import and reader-facing prose checks,
100-column and forbidden-token source scans, and whitespace checks pass locally.
The chapter tags all 32 public declarations exactly once. Those static checks
are separate from the 18 transport declarations checked at `82f750c8`.

Supplemental exact rational-complex checks of arbitrary local matrices passed
27 physical-size, ancilla-size, and chain-length cases, including zero sizes and
length zero (323 enlarged operator entries). They verify the sitewise regrouping
and all three embedding identities independently of the special swap. The script
`/tmp/check_7574_physical_matrix.py` is temporary and is not a formal proof.

## Exact-head check at b59d8045

Run `43754146822`, build job `132934861605`, again passed the focused strict
checks for both transport modules. Their package builds took 6.6 and 4.1 seconds.
The obstruction module now has only one diagnostic: after permutation matrix
multiplication, the pointwise configuration permutation must be unfolded. The
scalar contradictions and literal four-to-sixteen witness no longer produce
errors or warnings. The repair finishes that equality by definitional reduction
from `Equiv.piCongrRight` and the explicit involutive swap equivalence. Until the
whole module passes, its nine declarations remain unverified candidates.
Module policies and inline diagram semantics passed at that head.


## Exact-head check at fa979bdb

Run `43755230423`, build job `132938012552`, built
`SwapAncillaCompatibility.lean` in 5.4 seconds and reported its focused strict
check as `ok`. All nine obstruction declarations are therefore checked at this
exact head. Their four auxiliary Blueprint entries now reflect this result.
These are statements about the present global-family and coprime-ancilla
conventions, not counterexamples to the intended labelled-spin source lemma.

The five-declaration distinguished-matrix module had two errors: a conjugation
conditional did not distribute automatically, and a product of ancillary
Kronecker deltas reduced to equal conditionals with different decidability
expressions. The repair splits the common ancillary-coordinate condition
explicitly in each proof. No definitions, hypotheses, or statements change.
The remaining three private matrix identities and both full sandwich
semiconjugacy proofs produced no diagnostics, but the whole module remains a
candidate until its complete build and strict check pass.

Module policies and inline diagram semantics passed. The complete root build,
compiled-reference checks, axiom audit, and final-head checks remain outstanding.


## Exact-head check at 67bdbc2e

Run `43756212698`, build job `132941709416`, compiled all four new modules and
both generated aggregators. Package build times were 4.3 seconds for the physical
ancilla helper, 4.5 seconds for the physical-matrix module, 5.4 seconds for the
obstruction module, and 3.6 seconds for swap stabilization. Both aggregators and
the three helper, transport, and obstruction sources passed focused strict
checks. The physical-matrix module failed warnings-as-errors only on an unused
`Matrix.one_apply` argument at line 66. No unsolved goal or other diagnostic
remains in the four new modules.

Thus all 32 public declarations have compiled proofs, including full generic
ancilla compatibility and its reuse in the swap constructors. Their auxiliary
Blueprint entries reflect compilation. The final cleanup removes only that
unused argument and still requires a clean exact-head run. The original source
entry remains unfinished; the general equivalence definitions and pins are
unchanged. The complete root build, compiled-reference checks, and axiom audit
are still outstanding.

## Checked labelled-spin source continuation

All required CI jobs at `99005136` passed in run `43757303978`, including the
full Blueprint web job. A separate temporary audit checked the transitive
axioms of all 32 declarations on that tested merge and found only `propext`,
`Classical.choice`, and `Quot.sound`.

The labelled-spin continuation now has 18 further checked declarations in
`PhysicalMatrixBlocking.lean` and `Examples/LabelledSwapEquivalence.lean`.
At isolated source commit `d241aa5c`, run `43765894182`, both modules compiled
and passed strict checks; all 50 public declarations passed the same transitive
standard-axiom audit. They give a named fixed-labelled-space stabilization
convention using the actual canonical blocking operation, all three general
comparisons, and all ordered pairs of the actual three source examples.
The added Blueprint sources passed the pinned formatter in run `43766912022`.
See `2026-11-15_mpu_labelled_swap_equivalence.md` for the definition audit and
precise separation from the unchanged general equivalence convention.
