# Crossing supports through the crossing-terms set

Date: 2026-10-21. Issue: #9798.

The range-R swapped doubled Hamiltonian had its own set of crossing supports,
`crossingSupports Λ R A`. This set equals `Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A`,
which the area-law development already uses. The duplicate set and its membership lemma are
deleted, and their uses now read the crossing-terms set. No deprecated aliases are kept.
`crossingSites` and `exists_walks_of_mem_crossingSites` keep their names and namespace. They move
from `PEPS/Approximation/SwappedLocalHamiltonian.lean` to `Lattice/CrossingSupports.lean`.

## Removed declarations and replacements

| Removed | Replacement |
|---|---|
| `TNLean.Lattice.crossingSupports` | `Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A` |
| `TNLean.Lattice.mem_crossingSupports` | unfolding `Entropy.crossingTerms` with `Finset.mem_filter` |
