# Nonzero bond-dimension convention for injective PEPS on general graphs

This audit records the convention adopted for issue #9223 and the public
signatures it changed. It follows the pattern of
`docs/audits/2026-08-23_nonzero_coefficient_convention.md` and is the audit note
required for the one renamed declaration. No compatibility alias is provided.

## The convention

Section 3 of arXiv:1804.04964 calls a PEPS injective when every vertex tensor
is injective as a map from its virtual space to the physical space
(`Papers/1804.04964/paper_normal.tex:979--981`). The section also assumes,
without stating it, that every virtual bond space is nonzero: it picks
reference virtual configurations and full matrix algebras on the bonds. The
generic `TNLean.PEPS.Tensor` admits zero-dimensional bonds. On such a bond the
state vanishes and vertex injectivity can hold vacuously at its endpoints, so
the source's conclusions fail.

The source-facing theorems previously carried this convention as explicit
hypotheses `hposA`, `hposB` or `hpos : ∀ e, 0 < A.bondDim e`, next to
`IsVertexInjective A`. The convention now lives once in the Prop structure

```lean
structure Tensor.IsInjective (A : Tensor G d) : Prop where
  isVertexInjective : IsVertexInjective A
  bondDim_pos : ∀ e : Edge G, 0 < A.bondDim e
```

in `TNLean/PEPS/Defs.lean`, with one `**Local fix (nonzero virtual spaces):**`
marker citing `docs/paper-gaps/peps_injective_ft_section3_route.tex`. Its
positivity field quantifies over every edge, which is the whole index of
`bondDim`.

The convention is not put into `Tensor` itself. The generic layer keeps zero
bonds, as decided in #4100 and kept in #9214: the proofs build blocked, coarse,
reindexed and transported tensors whose positivity is derived, and
`stateCoeff_ne_zero_iff_bondDim_pos_of_isVertexInjective` is only meaningful
when zero bonds are admitted. `IsVertexInjective` therefore stays the
vertex-level linear-independence condition on all of those internal tensors.

The structure is not a parallel predicate family: its projections are its
fields, the anonymous constructor builds it, and the only added lemma is
`Tensor.IsInjective.transport` along graph isomorphisms.

## Migrated signatures

Each theorem below now takes `A.IsInjective` (and `B.IsInjective` where it
compares two tensors) in place of `IsVertexInjective` together with explicit
positivity.

| Declaration | File |
|---|---|
| `exists_stateCoeff_ne_zero` | `TNLean/PEPS/FundamentalTheorem.lean` |
| `fundamentalTheorem_PEPS_of_bondDim` | `TNLean/PEPS/FundamentalTheorem.lean` |
| `bondDim_eq_of_isInjective_sameState` (renamed) | `TNLean/PEPS/FundamentalTheorem.lean` |
| `fundamentalTheorem_PEPS` | `TNLean/PEPS/FundamentalTheorem.lean` |
| `gauge_unique_mod_edge_scalars` | `TNLean/PEPS/FundamentalTheorem/Uniqueness.lean` |
| `fundamentalTheorem_normalPEPS_of_vertexInjective` | `TNLean/PEPS/NormalFundamentalTheorem.lean` |
| `gaugeEquiv_cycleShift_of_isCycleShiftInvariantState`, `bondDim_cycleSuccEdge_add_one_eq_of_isCycleShiftInvariantState`, `bondDim_eq_of_isCycleShiftInvariantState` | `TNLean/PEPS/CycleShiftBondUniformity.lean` |
| `exists_constant_injectiveMPS_of_cyclicShiftInvariantState_per_bond` | `TNLean/PEPS/CycleMPSConstantDescription.lean` |
| `bondDim_translateEdge_of_isTorusTranslationInvariantState`, `bondDim_torusRightEdge_const_of_isTorusTranslationInvariantState`, `bondDim_torusUpEdge_const_of_isTorusTranslationInvariantState`, `torusUniformBondDim_of_isTorusTranslationInvariantState` | `TNLean/PEPS/TorusStateTranslationInvariant.lean` |
| `GaugeConsistencyConnectivityCounterexample.FundamentalTheoremPEPSStatement` | `TNLean/PEPS/GaugeConsistencyConnectivityCounterexample.lean` |

The `**Scope restriction (positive bond dimensions):**` marker on
`gauge_unique_mod_edge_scalars`, the `**Local fix (positive virtual spaces):**`
module marker of `TorusStateTranslationInvariant.lean`, and the positive-bond
part of the scope restriction in `CycleMPSConstantDescription.lean` were
removed; the structure's marker covers them. The `3 ≤ n` scope restriction of
the cycle results stays.

Internal steps keep explicit positivity because they also run on derived
tensors: `prod_perVertexScalar_eq_one`, `gaugeConsistency`, and the local
gauge extraction, kernel-descent, region-block and coherent-frame lemmas.

## Rename

| Old name | New name | Reason |
|---|---|---|
| `TNLean.PEPS.bondDim_eq_of_isVertexInjective_sameState` | `TNLean.PEPS.bondDim_eq_of_isInjective_sameState` | The hypothesis is now `Tensor.IsInjective`; the old name named a hypothesis the theorem no longer takes. |

`fundamentalTheorem_normalPEPS_of_vertexInjective` keeps its name: "vertex
injective" names its scope restriction against the general normal theorem,
which is unchanged.

## Counterexample modules kept

Both counterexample modules stay in this pass, by the second limit of the
degenerate-readings rule: the convention must be in the definition that every
remaining source-facing theorem uses before the witness is deleted.

- `TNLean/PEPS/PositivityCounterexamples.lean` refutes the injective
  Fundamental Theorem stated with `IsVertexInjective` alone. No library theorem
  has that hypothesis set any more. The general normal theorem
  `fundamentalTheorem_normalPEPS` and `bondDim_eq_of_normalBlocking` still keep
  explicit positivity over region-blocking data, and cite the
  counterexample-backed positivity fix. A hand check (not in Lean) indicates
  that the triangle witness meets their other hypotheses: every proper nonempty
  region has a zero-dimensional boundary edge, so region injectivity holds
  vacuously, and both states are zero while the bond dimensions differ.
  Deletion follows once that theorem takes its own interface carrying the
  convention.
- `TNLean/PEPS/PhysicalToVirtualCounterexample.lean` refutes
  `physical_to_virtual_insertion` without positivity. That theorem's injectivity
  hypothesis is `EdgeBlockedThreeSiteInjective A e`, chain data that the witness
  satisfies with one zero bond at an endpoint. Deletion follows once the
  three-site chain carries the convention.
