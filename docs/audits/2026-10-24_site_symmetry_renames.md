# Site-symmetry renames (2026-10-24)

The site-symmetry module `TNLean/Lattice/SiteSymmetry.lean` introduces the predicate
`Matrix.IsSiteInvariant G q H`, meaning that `H` commutes with every site permutation `P_g`. Two
public declarations were removed in its favour:

| Removed | Replacement |
| --- | --- |
| `Matrix.commute_sitePermMatrix_sum` | `Matrix.isSiteInvariant_sum_conj` |
| `MPSPreparation.supportedOperators_submatrix_siteEquiv` | `QuantumCircuit.supportedOperators_submatrix_siteEquiv` |

- `commute_sitePermMatrix_sum q H₀ h` stated that `P_h` commutes with
  `∑_g P_g H₀ P_g†` for one `h`. `isSiteInvariant_sum_conj q H₀` states the same for every `h`,
  through `IsSiteInvariant`, and is the case `κ = G` of `isSiteInvariant_sum_of_covariant`. The
  old declaration lived in `TNLean/Lattice/VariationalLowerBound.lean`; the replacement is in
  `TNLean/Lattice/SiteSymmetry.lean`.
- The support lemma, that permuting the sites by `p` carries an operator on `S` to one on `p '' S`,
  is unchanged except that the sites range over any finite type instead of `Fin N`. It moves from
  `TNLean/MPS/Preparation/CyclicOperatorSupport.lean` to
  `TNLean/Circuit/SitePermutationSupport.lean`.

All uses outside `Archive` have been migrated: `VariationalLowerBound.lean`, `SiteSymmetry.lean`
and `CyclicOperatorSupport.lean`. The blueprint `\lean` tags cite the new names. No alias is kept.
