# Independent physical cutoffs and the shared coupled proof

The source base is TNLean `5fc343a57d70eefd2902780107851ab9b0753a82`, with
QICLean `ba01733099b5a18bed5c9bfb62f95f175b4c9b57`. The contribution constructs
five-region hard clipping with a real threshold t independent of the window
length. Its regional minima, common ground vectors and original centered
ground energy are derived from the nearest-neighbour terms.

For t>=0 the final norm budget is 3t+4ell. Every current low window of
bandwidth eta>=0 satisfying 19+eta<=t has discrepancy at most
288 exp(11/8) exp(-(t-eta)/8). No gap is assumed for that residual.
The scaled low-cluster result then adds the explicit original spectral gap
and scalar tail budget. It retains the full original ground space, its actual
multiplicity and both directed closeness bounds. The word-family theorem
uses that physical cluster and the actual common polynomial family, chosen
before every power and input subspace.

The existing private coupled residual proof is now the specialization t=ell.
Its duplicate scalar estimate and full regional proof are removed. Both
existing public coupled signatures are byte-identical to the source base.
The merged physical viability and entropy source files are unchanged;
they were re-elaborated as current importers, not replaced by older source.

## Verification

Every actual module was checked separately against the clean, fully warmed
5fc343a57d/ba017 provider. All selected source, object, input and prebuilt
Mathlib hashes remained fixed. Changed importers were re-elaborated explicitly.
No cache or provider was modified, and Mathlib was not rebuilt.

| Module | Strict private seconds |
| --- | ---: |
| IndependentFiveRegionResidual | 10.366 |
| IndependentFiveRegionCluster | 25.199 |
| IndependentPhysicalDGPower | 43.094 |
| FiveRegionTruncationResidual | 8.171 |
| PhysicalDGViability | 47.67 |
| PhysicalDGEntropy | 38.3 |

An imported inspection covered the three new public results, both coupled
public results, the three current physical viability results and the current
physical DG entropy theorem. All nine used only `propext`, `Classical.choice`
and `Quot.sound`. The inspection passed in 43.367 seconds over 569 selected
TN/QIC source-object pairs. Its temporary source was deleted afterwards.

The new word-family consumer additionally uses the separately frozen QIC
word-power source from `65f4513e896253dccba07cbb720f9a95122a993b`, supplied as
explicit checked private objects. The source worktree's dependency records
remain unchanged for coordinated integration. The combined companion pin,
ordinary full build, affected regressions and compiled blueprint checks
remain required. This contribution does not establish the recursive tree,
final filter-and-trim iteration, Ritz extraction or an efficient GEN theorem.
