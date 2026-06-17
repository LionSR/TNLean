# Ch05 audit issues

## `blueprint/src/chapter/ch05_schwarz.tex`

- Lines 392-438: the tags resolve, but the blueprint environment/statement does not match the Lean declaration kind.
  `\lean{KadisonSchwarz.rightMultiplicativeDomainSubalgebra}` and `\lean{KadisonSchwarz.leftMultiplicativeDomainSubalgebra}` point to `def`s constructing `Subalgebra` structures, not theorem declarations; same for `\lean{KadisonSchwarz.multiplicativeDomainStarSubalgebra}` and `\lean{KadisonSchwarz.krausMapStarAlgHom}`.
  Lean refs: `TNLean/Channel/Schwarz/MultiplicativeDomainFull.lean:268`, `:280`, `:293`, `:330`.

- Lines 517-579: three theorem statements are weaker than the tagged Lean declarations.
  `\lean{KadisonSchwarz.schwarz_inequality_subnormal_operator}` proves both
  `T(Aᴴ) * T A ≤ T(Aᴴ * A)` and `T A * T(Aᴴ) ≤ T(Aᴴ * A)`, not just the first one.
  `\lean{KadisonSchwarz.schwarz_inequality_commuting_dominant_operator}` and
  `\lean{KadisonSchwarz.kadison_schwarz_commuting_dominant_cp}` likewise return both left and right bounds.
  Lean refs: `TNLean/Channel/Schwarz/SchwarzSubnormal.lean:341-347`, `:458-466`, `:638-646`.

## `blueprint/src/chapter/ch05_qpf.tex`

- Lines 584-613: the first spectral-radius theorem does not match the tagged Lean statement.
  `\lean{spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp}` proves
  `spectralRadius ... = ENNReal.ofReal r`, not a direct real-valued equality `spectral radius = r`.
  The real-valued statement belongs to the next tag,
  `\lean{spectralRadius_toReal_eq_of_posDef_eigenvector_of_irreducible_cp}`.
  Lean refs: `TNLean/Channel/Irreducible/SpectralRadius.lean:208-217`, `:472-480`.

- Lines 3-4, 257-258, 279-280: prose uses blueprint-internal language banned by the style guide.
  Instances:
  `used throughout the blueprint`,
  `used later in the blueprint` (twice).
