# GLM23 multiplicity L symbols: construction and coherence boundary

Source: `Papers/2203.12563/REsubmission.tex`, v3, `rawrels`,
`eq:F_symbol2`, `1Fsymbol`, `coupledpent`, and lines 595–602.

## Frozen construction and verification status

The additive dependency cone consists of seven modules, in dependency order:

1. `BoundaryDecompositionComparison`: equality of reconstructed target-algebra
   maps and support idempotents; inverse full coordinate comparisons on a
   common, possibly proper and non-self-adjoint, support.
2. `BoundaryDecompositionOperations`: composition, rectangular sandwich
   transport, and exact decomposition transport through both action factors.
3. `BoundaryDecompositionCoordinates`: collected synthesis/analysis matrices,
   their inverse/support identities, and full comparison.
4. `BoundaryActionTrees`: the actual fusion-then-action and sequential-action
   maps, their exact biorthogonal reconstructions, and equal supports.
5. `BoundaryDecompositionIntertwining`: analysis/synthesis letter equations,
   cross intertwiners, and finite reindexing.
6. `BoundaryActionComparison`: inverse full action-coordinate comparisons and
   their defining analysis equation.
7. `BoundaryActionLMatrix`: final-block separation, normalized-trace extraction
   of actual multiplicity matrices, both inverse identities, and the printed
   analysis-tree equation.

The initial targeted checkpoint checked the six precursor modules
(17, 80, 48, 10, 233, and 258 seconds, respectively) and the strict
support-comparison regression. At commit
`26dc420aa85fa47afc94708729b8f92502c93b7e`, the complete Lean build and
both strict regression files passed in
[run 37317689145, job 111788687059](https://github.com/LionSR/TNLean/actions/runs/37317689145/job/111788687059).
All seven production modules are checked, including the actual L-matrix
capstone. All eight guarded reports enforce exactly `propext`,
`Classical.choice`, and `Quot.sound`. This is an immutable, commit-specific
production/regression checkpoint; later documentation or integration trees
must pass their own full CI and review gates. The live PR records those
results rather than attributing this success to a later tree.

Regression files are `TNLeanTest/BoundaryDecompositionComparison.lean` and
`TNLeanTest/BoundaryActionLMatrix.lean`. The latter directly guards both the
source-state inverse theorem and the actual printed-direction analysis
relation. The separate blueprint leaf is
`blueprint/src/chapter/ch30_mpo_boundary_comparison.tex`; all public
construction declarations have owners there. All compiled statements and
proofs carry `\leanok`. All 46 public declarations have exactly matching
fully qualified owners. Statement dependency edges refer to the objects and
premises used to state each result; reconstruction, support comparison,
intertwiner separation, and common-span theorems occur on the proof edges.
The generated import router and existing boundary-regression CI list expose
and test this construction without a separate bespoke build job.

The source-oriented analysis-tree diagram is now embedded natively in this
leaf. It is the separately rendered fragment
`action-l-analysis.tex` (SHA-256
`18a4ba89c5c3632c3026ae04b3a2159688c421a072b66071a5aea82f2656a766`),
using pinned Tenkz commit `08a6493f3605dcf2ca5b512823ccb2698dfc027b`.
Its standalone XeLaTeX preview was visually inspected at 150 dpi; the log
had no warnings or overfull/underfull boxes. Tenkz checked identical boundary
signatures with three east input legs and one west output leg, two nonvoid
tensors per side, and one internal contraction per side. The source order
is outer action i / inner action j on the sequential tree and action k /
fusion mu on the other tree. The integrated leaf was subsequently rendered in an isolated focused
XeLaTeX preview using the actual blueprint preamble and pinned Tenkz source.
All three mathematical pages and the bibliography were visually inspected;
there are no overfull/underfull boxes and the diagram signature check still
passes. Only omitted external dependency-label references warn in this
focused build; those labels were independently checked to resolve uniquely
in the complete blueprint. Full exact-head web validation remains pending.

The typed-index correction note was also rendered and both pages visually
inspected. Its formulas fit without overflow. An orphan footnote marker was
repaired by preventing a break before the source-traceability footnote.
The gauge paragraph explicitly resets its input labels a,b,c, final label d,
and intermediate labels e,f; all displayed formulas and corrected index
orders are unchanged. The cloud TeX environment lacks the unused
`dsfont` package and default font-map registration, so the isolated note
preview omitted only the unused font load and explicitly loaded the already
installed Computer Modern/symbol font maps. Its mathematical body, article
layout, and Computer Modern fonts were unchanged. No package installation
or repository preamble change was made.

## What the construction proves

The two exact action decompositions are built from the actual pairwise fusion
and action maps, rather than assumed as independent comparison data. Their
incoming tensor is `(T_a T_b)·A_x`. Their fixed-final multiplicity spaces have
source orders `(c,k,mu)` and `(z,i,j)`, where
`mu : Fin N_ab^c`, `k : Fin M_cx^y`, `i : Fin M_az^y`, and
`j : Fin M_bx^z`. Dependent finite index types avoid a preselected equality of
cardinalities. Bond reassociation places the sequential tree on the same
incoming space as the fusion tree.

For two decompositions over repetitions of a common target family, positive
simultaneous word span gives equality of their target-algebra reconstruction
maps by linearity. Evaluating at the identity tuple derives equality of their
support idempotents; ambient completeness is never assumed. The full cross
comparisons `C = H_seq S_fus` and `D = H_fus S_seq` are then two-sided inverses.

Each cross contraction intertwines its final blocks. Simultaneous word span
kills distinct-final contractions; normality makes each same-final contraction
a scalar identity. Its scalar is the trace divided by the positive final
bond dimension. Thus `C = directSum_y (L_y tensor I_Dy)` and the reverse
comparison has factors `K_y`. Extracting each diagonal block of `CD = DC = I`
proves `L_y K_y = K_y L_y = I`. The full support equation gives the actual
analysis identity `H_seq = (directSum_y L_y tensor I_Dy) H_fus`.

`actionLMatrix_inverse_of_isInjective` derives the common positive word span
internally from individual state-block injectivity, positive dimensions, and
absence of nonzero scalar-gauge duplicates. Pairwise exact fusion/action data
are inputs; the already verified boundary source-existence results construct
these data from closedness/compatibility and the corresponding source block
assumptions. A single packaged closedness-to-L wrapper has not been added.
The action-equation regression likewise derives its common span internally.
No L matrix, scalar compatibility law, or mixed pentagon is an input.

Zero multiplicity spaces and zero matrix entries are permitted. The paper's
phrase “non-zero constants” cannot mean that every multiplicity-matrix entry
is nonzero: the conclusion is an invertible change of basis. No unitary gauge,
ambient completeness, or unrestricted unblocked gauge-exhaustiveness theorem
is asserted.

## Source orientation and gauges

Main-text action V is analysis: its type at line 459 maps the incoming
operator/state bond to the final state bond. The `V2` picture has final y on
the left and incoming a,z on the right; hat V is synthesis. Thus
`eq:F_symbol2` reads `H_seq = L_printed H_fus`, and `1Fsymbol` contracts
`H_seq S_fus`. There is no transpose or inverse in the L extraction.
Appendix A's temporary generic factor names do not change this convention.

Main-text fusion W is analysis and hat W synthesis. GLM23 `Fsymbolsdef`
reads `H_left = F_GLM H_right`. In the reused complete-zipper API,
`printedFMatrix` P instead satisfies `S_right P = S_left`; therefore
`F_GLM = inversePrintedFMatrix`. That API cites arXiv:1511.08090, whose
synthesis convention must not silently be identified with GLM23's analysis
convention. The exact indexed pentagon renaming is recorded in
`2026-10-05_glm23_boundary_reconstruction.md`.

A source analysis gauge Y corresponds to the library's synthesis gauge
`Z = Y^(-transpose)`. Consequently the source-direction laws are
`F_GLM' = Y_left F_GLM Y_right^(-1)` and
`L' = X_seq L X_fus^(-1)`. These identify conventions; this new L cone does
not yet prove a multiplicity L gauge theorem.

## Typed local correction

The source's `coupledpent` F factor at line 557 reverses both multiplicity
pairs. The surrounding L factors require eta in N_ab^d, chi in N_dc^e,
mu in N_bc^f, and nu in N_af^e. The well-typed F factor therefore has upper
`(d, eta, chi)` and lower `(f, mu, nu)`, rather than the printed upper
`(d, chi, eta)` and lower `(f, nu, mu)`.

`docs/paper-gaps/glm23_multiplicity_l_indices.tex` records the typed corrected
formula, the distinct F/L orientations, and the source gauge display's
missing primes and dual inverse-index placement. The L module carries a
Local fix marker identifying this downstream correction. The mixed pentagon
itself is not a theorem of this frozen cone.

## Audited mixed-pentagon continuation, not yet implemented

The existing scalar `GroupFamily.BlockActionData.isCompatible_lSymbol` is a
one-channel group-action result from periodic/dressed reductions. General
`TNLean.Algebra.LSymbol.IsCompatible` is the scalar coupled-pentagon equation
itself, and its consumers assume that property. Neither supplies the actual
multiplicity-matrix coherence theorem. The complete-zipper F pentagon, proved
by basis comparison, is the intended reusable coherence result.

A triangular physical embedding can combine operators and states into one
auxiliary fusion family. Embed each operator in the upper-left d-by-d physical
corner of size d+1 and each state in the upper-right d-by-1 column. The product
rules are operator/operator = fusion, operator/state = action, and every
state-left product has an empty channel space. There is no extra zero-tensor
label. Use a `Fin (r+s)` label family to reuse the Fin-indexed constructor.
Physical supports preserve injectivity and distinguish the two label kinds;
within each kind the original scalar-gauge separation applies.

After one common blocking, the physical size is `(d+1)^L`, not `d^L+1`.
The virtual W/V maps remain unchanged, so the larger physical alphabet does
not alter the actual coefficients. Constructing the auxiliary complete
zipper family must derive its block inverse and exact empty-channel rules;
these are obligations, not new categorical or support assumptions.

With typed coordinate reindexing, auxiliary forward F on `(a,b,x;y)` has
entry `P[<z,j,i>,<d,eta,n>] = L[row <z,i,j>, column <d,n,eta>]`, while
auxiliary inverse F on operator triples has
`Q[<d,eta,chi>,<f,mu,nu>] = F_GLM[<d,eta,chi>,<f,mu,nu>]`.
The ordinary path identity `C B A = E D`, multiplied by `A^(-1)`, becomes
`E D A^(-1) = C B`, the typed corrected mixed pentagon. This route needs the
lifted `P Q = I` identity as well as the existing opposite-direction inverse
helper. The embedding, coefficient identifications, and lifted cancellation
are the minimal remaining proof obligations. No coherence code is frozen yet.

A later independent specialization can treat exact one-channel closed group
actions. Its composite map must use fusion synthesis:
`odot = actV * kronId(fd.W)`. The present scalar reduction structure does not
provide that exact closed-action bridge. For the source's stabilizer formulas,
require `H = stabilizer(x)` or specialize to `x = x0`; individual inverse-action
V/W maps carry reciprocal L factors that cancel only in their paired sandwich.

## Independent source review checkpoint

On 5 October 2026 an independent review found no mathematical blocker in
the seven-module construction: both trees reconstruct the same unblocked
tensor, common support is derived without ambient completeness, fixed-final
normality gives scalar factors, and both inverse identities allow empty
multiplicity spaces. It confirmed the printed analysis direction and the
state-block injectivity, dimension, and scalar-gauge separation hypotheses.
The review caught a missing word-length qualification in one intermediate
blueprint statement; it now explicitly requires a positive simultaneous
spanning length, as the Lean theorem already did. Compiler and exact-head
CI results are separate from this mathematical checkpoint.
