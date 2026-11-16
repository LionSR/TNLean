# Exact Fibonacci action-tree calculation for #8053, item 2

Status: **all-sector L identification kernel checked; cross-final extension pending**, with separately verified exact arithmetic evidence.
The continuation adds `FibonacciActionDecomposition.lean` and
`FibonacciActionLMatrix.lean`, with proofs rather than proof placeholders.
The blueprint records the precise constructed family but carries no completion
marks while hosted compilation is pending. The earlier exact calculation is
preserved below. Source presence is not kernel-check evidence.

## 2026-11-16 continuation: reuse the now-merged construction

During the interrupted upload, PR #10689 merged at
`ab8f74efe8de668d891465b2962af060b1b4359d`. It adds the exact fusion/action
maps and the tau-tau L comparison in `FibonacciActionTrees.lean` and
`FibonacciLSymbol.lean`. That work is reused rather than duplicated.
Draft #10756 now extends it to **all** operator-label sectors, reverse
comparisons, both inverse identities, and equality with the actual
`fusionFMatrix` in one common standard gauge. No general independence of
the choice of normal-block reductions is claimed.

The refreshed remote branch is based on main
`439502f015916a15cae5a8dfdce0a6a26fc0d543`. It inherits that main's
unchanged dependency pins, including QICLean
`603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac` and the same Mathlib pin.
The historical local baseline and calculation below are retained as evidence,
not presented as the new branch's base or map normalization.

Relative to the maps merged by #10689, use **the same analysis scale for
fusion and action**: sigma at (tau,tau,one), minus sigma inverse at
(tau,tau,tau), and one elsewhere. Synthesis receives the reciprocal.
This differs from the historical action gauge below because #10689 chose
different raw normalizations for its tau-on-chain maps. The exact verifier
now reads #10689's maps and independently checks this refreshed gauge too.
Run `python3 scripts/fibonacci_action_l_check.py` on the refreshed branch;
on the older local checkout pass
`--tree-maps /path/to/FibonacciActionTrees.lean`.

Hosted pinned CI has checked `FibonacciActionDecomposition.lean` strictly at
commit `8e322be197bdfc869bf26ea4c3d8bcb92ab50887` in
[run 43953366828](https://github.com/LionSR/TNLean/actions/runs/43953366828).
Its log records that module as `ok`: the displayed gauge units, all eight
exact complex decompositions, normality, and both actual action trees are
kernel checked. The source blob is
`c1c5aa8cf44867afa60e5e1a874045bcf9e47cef`.

The subsequent run at `080ea322075e41abb201ef7635891ffc691b723d`
accepted the complex multiplication transport but failed the next rewrite
because the GoldenInt certificate retained an unreduced path equivalence.
Commit `c1d793c355835da25acf770657373a2b51bf4b99` states those certificates
in explicit path coordinates. Its pinned
[run 43956358566](https://github.com/LionSR/TNLean/actions/runs/43956358566)
passed both the strict changed-source check and the early module build.
Thus the actual all-sector L/F equality, reverse comparisons, both inverse
identities, and all supporting proofs in that source are kernel checked.
The full project and blueprint checks were still running when this status
was recorded.

A subsequent extension promotes the exact verifier's ten cross-final zero
products to a Lean theorem: `actionTrees_cross_final` covers both rectangular
cross contractions between different final blocks. That extension and its
blueprint statement remain pending kernel checking. No completion marker is
placed on the combined blueprint entry until that check succeeds. These
modules extend the merged construction; they do not replace its map tables.

## Ownership and baseline

Checked GitHub on 2026-11-15: [#8053](https://github.com/LionSR/TNLean/issues/8053)
is open, assigned to LionSR. Its
[then-latest comment](https://github.com/LionSR/TNLean/issues/8053#issuecomment-6517369490)
says tnlean-35 delivered neither a construction nor an L calculation in
[#10446](https://github.com/LionSR/TNLean/pull/10446), leaving item 2 for a
dedicated PR. That PR is now merged. No issue assignment or external comment
was changed in this work.

Local baseline: `cbf482955f46f36c71c95ab1547b3cc86b6d58c2`.
The toolchain and manifest remain unchanged: Lean `v4.36.0-rc1`, Mathlib
`625d8914199bc567cca9b91f90e8e5afafa5ae51`, QICLean
`c457682404aa548b4acd16ac27be5d3835e68892`.

The first commit added this audit and `scripts/fibonacci_action_l_check.py`.
The continuation adds the two candidate Lean modules, generated imports,
blueprint statements and a tactic-pattern note. Shared
NIM-rep definitions and the files from tnlean-35's work are unchanged.

## The two states and the missing unit action

Use the existing physical-dimension-two states in `FibonacciAction.lean`:

- `fibAllTau`: bond dimension 1, with letters `A⁰ = 0`, `A¹ = 1`;
- `fibChain`: bond dimension 2, with letters
  `C⁰ = [[0, σ], [0, 0]]`, `C¹ = [[0, 0], [1, −σ²]]`.

Here σ is the positive real root of `σ⁴ + σ² = 1`, hence `σ = φ⁻¹ᐟ²`.
Their normality theorems already exist. Their joint length-three word span
has dimension `1² + 2² = 5`, as checked by exact elimination in the script.
There is no enlargement of the physical alphabet or replacement of the MPO.

For the three already recorded action compressions, take the target rows of
the recorded `GaugeGolden` as analysis and target columns of `GaugeInvGolden`
as synthesis. Target offsets are 0 for `1·A → A` and `τ·A → C`, and 0, 1
for `τ·C → A, C`, respectively.

The fourth action, `1·C → C`, has the following analysis and synthesis in
product bond order `(operator bond, state bond)`:

```text
VA = [[1, −σ², 1, 0],       WA = [[1, 0],
      [0,    0, 0, 1]]             [0, 0],
                                    [0, 0],
                                    [0, 1]].
```

The script derives these by exact intertwiner elimination and checks their
retraction and single-letter reconstruction. All four actions have the
regular multiplicities `M = fibNim`.

For fusion, use the analogous target rows/columns of the three unit-pair
gauges in `FibonacciUnit.lean` and the ττ gauge in `Fibonacci.lean`. In the
latter, target offsets are 0 and 2. The script checks all four exact fusion
decompositions, including retractions, cross-channel zeros and reconstruction.

## Exact tree orientation and the gauge

Notation follows `BoundaryActionTreeEntries.lean`. Write `VF, WF` for fusion
analysis/synthesis, `VA, WA` for action analysis/synthesis. In common incoming
coordinates `((xa, xb), xx)`, the fusion synthesis and sequential analysis are

```text
SF(c) = (WF(a,b,c) ⊗ I_Dx) WA(c,x,y),
AS(z)[u, ((xa,xb),xx)] = Σv VA(a,z,y)[u,(xa,v)] VA(b,x,z)[v,(xb,xx)].
```

The computed scalar is exactly the definition in `BoundaryActionLMatrix.lean`:
`L[z,c] = trace(AS(z) SF(c)) / D_y`. The script additionally checks that the
whole cross product is `L[z,c] I_Dy`, rather than only comparing its trace.
The inverse comparison uses fusion analysis and sequential synthesis.

In the existing gauges, sectors with at least one unit among `a,b` have
scalar L equal to 1. The remaining sectors are

| `(a,b,x,y)` | Rows z | Columns c | L |
|---|---|---|---|
| `(τ,τ,1,1)` | τ | 1 | σ |
| `(τ,τ,1,τ)` | τ | τ | −σ⁻² |
| `(τ,τ,τ,1)` | τ | τ | −σ⁻² |
| `(τ,τ,τ,τ)` | 1, τ | 1, τ | `[[σ³, −σ], [1, 1]]` |

Rescale analysis maps by the following nonzero factors, and each corresponding
synthesis map by the reciprocal:

```text
α(a,x,y) = σ    for (a,x,y) = (τ,τ,τ), and 1 otherwise;
β(a,b,c) = σ    for (a,b,c) = (τ,τ,1),
           −σ⁻¹ for (a,b,c) = (τ,τ,τ), and 1 otherwise.
```

Thus `VA' = α VA`, `WA' = α⁻¹ WA`, `VF' = β VF`, `WF' = β⁻¹ WF`.
The source gauge formula becomes

```text
L'[z,c] = α(a,z,y) α(b,x,z) / (α(c,x,y) β(a,b,c)) · L[z,c].
```

Every nonempty scalar sector then equals 1 and the only two-dimensional
sector is

```text
L'_(τ,τ,τ)^τ = [[σ², σ], [σ, −σ²]].
```

The script checks **the same fusion gauge** against `fusionFMatrix`'s
left-analysis/right-synthesis contraction. It produces the standard Fibonacci
F in every admissible sector. This prevents confusing F with its inverse or
allowing independent row/column changes in each L sector. The fixed-final
index correspondence is `(z,0,0) ↔ (z,0,0)` for the sequential/right-fusion
space and `(c,0,0) ↔ (c,0,0)` for the fusion-action/left-fusion space. Thus L
has transposed index types relative to the declared F matrix. In this gauge,
the nontrivial F is symmetric and involutive; all other nonempty sectors
are the scalar 1.

## Reproduction and evidence

With SymPy 1.14.0, run from the repository root:

```sh
python3 scripts/fibonacci_action_l_check.py
```

All arithmetic uses the exact algebraic number field; no floating point
comparison or approximate tolerance is used. The script reads the existing
Lean gauge matrices rather than copying their numeric entries. It checks:

- all four fusion and all four action decompositions;
- all 12 nonempty fixed-final L sectors, comprising 15 entries, plus empty sectors;
- both inverse laws and 10 mixed products between distinct final blocks;
- the standard F contractions using the same fusion gauge;
- the five-dimensional simultaneous length-three word span;
- reconstruction of every double-action letter by both actual action trees.

The script passes, as does Python byte compilation. These calculations are
supporting evidence and do not replace a Lean kernel check.

Source SHA-256 values at the recorded baseline:

```text
Fibonacci.lean        053ae1b6f15beebcf4b1e09c61e9c4487b169ac4c48c711e09dd610c982be9f4
FibonacciUnit.lean    d632af077ad20bb8542e3765d52ecc37b166f81700cb5d1ff76f0666d171edaf
FibonacciAction.lean  563c1eda3e66a68b2ae7ee9cfeb1e588c5e0bdcdc115e30fcf666ef55e44e1b6
FibonacciFSymbol.lean be53c7fb4b675bd12c0da6219e7c930bac955cb63fdec62171c0641bf9aaad9e
```

## Formal obligations recorded before the Lean candidate

The following list preserves the obligations recorded before the candidate.
Items 1–4 are now kernel checked at `c1d793c`. The additional cross-final
extension and the full validation in item 5 remain pending as described above.

1. Define the typed fusion and action maps over the existing GoldenInt ring,
   including `1·C → C`, and map them to ℂ with `goldenToComplex`. Use
   `Fin (fibNim a b c)` and `Fin (fibNim a x y)` so inadmissible channels
   remain empty, rather than silently assuming all channels have dimension 1.
2. Prove all eight `IsBiorthogonalDecomposition` instances at the unblocked
   letter level. Existing compression theorems alone are not this certificate.
3. Instantiate `fusionThenActionAnalysis`, `fusionThenActionSynthesis`,
   `sequentialActionAnalysis`, `sequentialActionSynthesis`, and `actionLMatrix`.
   Reuse the coordinate formulas in `BoundaryActionTreeEntries.lean`.
4. Prove the cross contractions after the displayed α,β gauges over GoldenInt,
   transport them to ℂ, and identify the normalized trace with the exact L
   definition. Identify the corresponding `fusionFMatrix` with the printed
   `fibFSymbolGolden`, with the explicit index reversal described above.
   This is an existence/construction result for the displayed two-block family;
   do not claim a classification of arbitrary L-solutions without another proof.
5. Add the source-faithful blueprint entry, regenerate the import aggregator,
   build changed modules with the package linter options, check the resulting
   theorem axioms, run the required full build and blueprint checks, and leave
   #8053 open until those formal obligations are actually discharged.

Local Lean validation is unavailable: neither `lake` nor a Lean
installation nor `.lake` artifacts are present. The managed environment reports
network policy `disabled/enforced`; a normal HTTPS request to GitHub receives
HTTP 403 (`CONNECT tunnel failed`). No cold Mathlib source build, pin change,
network-policy bypass, unproved declaration or weakened completion theorem
was introduced. Hosted CI supplies the pinned compilation evidence above.
A full successful build, final strict checks, blueprint web/PDF and declaration
checks, and a separate resulting-theorem axiom inspection remain required.
No committed diagnostic fixture or workflow exception is added to obtain the
axiom printout. The branch stays draft and #8053 stays open. The user explicitly
instructed that this work must not be merged.

Source references: GLM23, `Papers/2203.12563/REsubmission.tex`, `rawrels`,
`eq:F_symbol2`, `1Fsymbol`, gauge transformations at lines 595–605, and the
Fibonacci example at lines 1991–1993. The local MPO-entry provenance caveat in
`docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex` still applies.
