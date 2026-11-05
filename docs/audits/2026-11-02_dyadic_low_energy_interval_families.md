# Decreasing original-to-clipped comparison loss on every interval

For each fixed bandwidth eta > 0, one constant C is chosen before the chain,
local dimension, numerical count base, interval, narrower width and accuracy
index. At index i, the numerical base is m_i = m 2^i, while the physical
local dimension q and every Hamiltonian term remain unchanged. With

    g = min(w,1), u_i = 1 + log m_i + log(1/g),
    ell_i = ceil(C u_i^2/g), D_i = (m_i ell_i^2)^(22 ell_i),

the constructed improving family has exactly D_i^2 operators on any prescribed
interval. Both spectral comparisons have loss 1/(200 2^(4i)), and the same
chosen degree gives D_i^12 Delta_i <= 10^(-5). The image is the actual sum of
the images of the retained source space under these operators.

The numerical residual budget is proved before introducing the physical
matrices. The exact ceiling estimate gives ell_i >= ell_0 + 64i, so the
actual residual decreases by at least 2^(-4i). Long intervals use the actual
clipped polynomial and its exact regional factors after inward cuts. Short
intervals use configuration matrix units. Canonical original spectral targets
are those of the same raw Hamiltonian at every index. Empty intervals and
intervals meeting either boundary are included.

This is a quantitative auxiliary to ALVV, arXiv:1602.08828v2, the improving-family
construction at lines 1027–1041. Assumption (LD), lines 281–284, declares the
bandwidth fixed. The statement retains q >= 2 and the explicit buffer
6w <= eta_1 <= eta. It has no spectral-gap, supplied-family, supplied-residual,
rank or sampling premise. The scope note is
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
An entropy estimate and the sharper source MPS rate remain separate arguments.
In particular, clipped-space invariance is not claimed to be raw-space invariance.

The existing three index-zero public statements have byte-identical signatures.
Their proofs specialize the three accurate statements at i=0. No parallel
viability predicate or duplicated physical construction is introduced.

## Verification

Private checks read only the fully built provider TN f7bae89a06741bb61820b50cd4b421a2d42951e7
and its own QIC 00ca963e4a79afd68d9d6f875dd468a21f1dccdd. The checker used actual
module names, the strict package options, warning-as-error, source/object/input
hash guards and transitive changed-importer checks. All output was written
under `/tmp/tnlean-dyadic-regional-f7bae8-20261102`.

| Module | Strict seconds | Guarded TN/QIC source-object pairs |
|---|---:|---:|
| `DyadicRegionalLowDensityFamily` | 23.175 | 543 |
| `RegionalLowDensityFamily` | 13.865 | 544 |
| `DyadicLongIntervalLowDensityFamily` | 23.095 | 546 |
| `LongIntervalLowDensityFamily` | 12.823 | 547 |
| `DyadicIntervalLowDensityFamily` | 16.058 | 557 |
| `IntervalLowDensityFamily` | 9.606 | 558 |

The combined imported inspection of all six public declarations passed in
7.689 seconds and reported only `propext`, `Classical.choice` and `Quot.sound`.
Temporary Lean audit commands were removed after inspection. The earlier
regional two-name inspection also passed. No ordinary build, full-library
check or compiled blueprint declaration check is claimed for this checkpoint;
those remain for integration. No Mathlib source or shared cache was changed.

Three new production modules must be included when regenerating the AreaLaw
and root import aggregators. The source-only patch omits generated aggregators.
The reader blueprint includes the new regional, long-interval and all-interval
results and records the old statements as index-zero consequences.

Source-level blueprint declaration resolution, added-prose review, the tactic
pattern scan and whitespace checks passed. The role check reports one inherited
reference mismatch in `ch35_physical_dg_reference_space.tex`; this checkpoint
adds only supporting lemmas and introduces no role mismatch.

Reverse declaration coverage resolves all six mathematical declarations. Its
text parser additionally misreads the docstring line “lemma retains” in
`DyadicLongIntervalLowDensityFamily.lean` as a declaration named `retains`.
This is a parser false positive, not an unrecorded mathematical statement.
