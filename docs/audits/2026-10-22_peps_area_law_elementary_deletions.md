# Elementary declarations removed from the PEPS area-law development

[PR #9888](https://github.com/LionSR/TNLean/pull/9888) removes nine unused
auxiliary declarations from five modules. The source examined here is
`58f49cd0a260509d8cb27945265fbbcbaf9558df`, including its immediate predecessor
for the deleted statements and proofs. The geometric definitions, the angular
and contact-separation results, and the energy estimates remain in place.

## Removed declarations and their replacements

No replacement declaration is needed by a surviving proof. The following
arguments recover each elementary assertion if a later proof needs it.

| Removed declaration | Module under `TNLean/PEPS/AreaLaw/` | Retained definition or mathematical argument |
|---|---|---|
| `TNLean.PEPS.AreaLaw.Geometry.mem_unitBox_self` | `Geometry/BirthSeparationAngular.lean` | Apply `Int.floor_le` and `Int.le_ceil` to each coordinate in the definition of `unitBox`. Thus each point lies between its coordinatewise floor and ceiling. |
| `TNLean.PEPS.AreaLaw.Geometry.isQuarterSectorial_univ` | `Geometry/BirthSeparationAngular.lean` | The two conditions defining `IsQuarterSectorial` hold for the whole plane because every point belongs to it. |
| `TNLean.PEPS.AreaLaw.Geometry.isQuarterSectorial_empty` | `Geometry/BirthSeparationAngular.lean` | The radial equivalence in `IsQuarterSectorial` has both sides false for the empty set, and the box implication has an empty antecedent. |
| `TNLean.PEPS.AreaLaw.Geometry.mem_beltAtom_add_iff` | `Geometry/BirthSeparationAtoms.lean` | Unfold `beltAtom` and `beltAtomCenter`. Translating the integer square index from $c$ to $c+e$ translates its center by $2e$, so membership of $p$ in the new atom is membership of $p-2e$ in the old atom, with the integer vectors embedded in the plane. |
| private `scaleHomeomorph_apply` in `TNLean.PEPS.AreaLaw.Geometry` | `Geometry/BirthSeparationStar.lean` | Unfold the retained `scaleHomeomorph`: for $r\ne0$, its value at $x$ is $v+r x$ by definition. |
| `TNLean.PEPS.AreaLaw.Geometry.smul_mem_repairFanCone_iff` | `Geometry/RepairFanCones.lean` | For $t>0$, apply the retained `smul_mem_repairFanCone` first to $t$ and then to $t^{-1}$, using $t^{-1}(ty)=y$. This gives both directions of positive-scale invariance. |
| `TNLean.PEPS.AreaLaw.Scan.ScanData.integral_etaOld_rpow_nonneg` | `Scan/EnergyBalance.lean` | Apply `Real.rpow_nonneg` to `histories.etaOld_nonneg`, then `integral_nonneg`. The integrand is the one-eighth power of a nonnegative old-leaf quantity. |
| `TNLean.PEPS.AreaLaw.Scan.ScanData.integral_etaNew_rpow_nonneg` | `Scan/EnergyBalance.lean` | Apply `Real.rpow_nonneg` to `histories.etaNew_nonneg`, then `integral_nonneg`, for each child leaf. |
| `TNLean.PEPS.AreaLaw.Scan.ScanData.termEnergy_nonneg` | `Scan/EnergyBalance.lean` | Unfold the retained `ScanRound.termEnergy`. For $0<p<1$, its coefficients $p$ and $1-p$, the history weights and the child weights are nonnegative. The old- and new-leaf integrals are nonnegative by the preceding two arguments. Finite sums and products preserve nonnegativity; an omitted summand is zero. |

## Consumer and blueprint checks

Every final name component listed above was searched, as a whole identifier,
in all tracked files outside `Archive/` at the stated revision. There are no
remaining occurrences in Lean sources, tests, scripts or blueprint sources.
The only remaining occurrences are the descriptions of these deletions in
`docs/proof_debt_ledger.md`. In particular, no blueprint `\lean{...}` tag,
axiom-check test or named automation registration refers to a removed name.
The deleted declarations carried no registered attributes.

The same search in the immediate predecessor finds only the nine declarations
and two calls within the removed group: `termEnergy_nonneg` calls the old- and
new-leaf integral lemmas. Neither the last lemma nor any of the other six
removed declarations has a consumer outside that group. Removing the three
energy lemmas together therefore leaves no unresolved use.

This records the names, elementary replacements and absence of surviving uses
required by `docs/project_conventions.md`. The added audit note changes no Lean
source, test, blueprint tag or dependency input. Its checks are source searches
and comparison with the deleted proofs; no additional compilation is asserted.
