# Entropy in an original low-energy band

For each fixed bandwidth eta > 0, one positive K_eta is chosen before the
chain length, local dimension q >= 2, physical interactions, prescribed
interval, positive deficit v and unit vector. Write G(c) for the original
Hamiltonian's spectral subspace below its canonical minimum plus c. Every
unit vector psi in G(eta-v) satisfies

    S(psi_J) <= log(dim G(eta))
      + (K_eta/v) * (1 + log q + log(1+1/v))^3.

The coefficient of the full-band logarithmic dimension is exactly one.
All prescribed intervals, including empty intervals and both boundary cases,
are included. The Hamiltonian is the actual sum of supported nearest-neighbour
positive contractions. There is no spectral-gap, supplied-filter, residual,
sampling or entropy hypothesis. For v > eta the target is proved zero, so no
upper restriction on v is left in the public statement.

## Construction and source comparison

One actual constant-viable space W0 is chosen for G(eta-b/2), where
b = min(v,eta/2). At the fixed width w=b/6, the accurate interval families
send this same W0 to actual image spaces viable for G(eta-b), with error
2^(-i-1) and dimension at most dim(W0) D_i^2. Spectral cutoff inclusion
transfers this to G(eta-v). The clipped upper and lower comparisons are both
used explicitly; no original band is treated as invariant under a clipped
polynomial, and no equality of its eigenvalues is assumed.

For one fixed physical vector, the images bound tails of one actual regional
state. The existing finite entropy estimate is applied at initial rank
dim(W0) and the enlarged ranks dim(W0) D_0^24 D_i^2. The logarithmic dimension
bound on that same W0 supplies one copy of log(dim G(eta)). Bootstrap and
filter constants are chosen independently and need not agree. The companion
scalar entropy estimate absorbs the two costs into one K_eta.

The source is ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105,
with Assumption (LD)'s fixed bandwidth at lines 281–284. At v=mu/log L,
L >= 2, the remainder is the positive regularized logarithmic version of the
source entropy scale. An LD density envelope may replace the actual full-band
dimension by monotonicity. The statement explicitly retains q >= 2 and physical
intervals; see `docs/paper-gaps/alvv16_low_energy_family_scope.tex`.

The sharper accuracy-dependent MPS rate and running time remain separate.
No independent area-law or entropy theorem supplies the physical tail estimate.

## Verification

All checks read only the fully built TN5e19c052124518e40871bb67a1ce5398dd3b6416
provider and its own QIC518e8d2053793d108d1ad52638a89f22028bafca package.
The private source closure includes the unchanged public exposure of the
inverse-scale improving-error lemma and the scalar entropy coefficient from
QIC9de8464c. Every selected importer of a changed existing source was
re-elaborated before use. Outputs and temporary diagnostics are confined to
`/tmp/tnlean-ld-entropy-5e19-20261102`.

Final strict timings and foundation evidence are recorded in the immutable
manifest accompanying this checkpoint. The three production files use the
default heartbeat budget; no higher option is retained. No ordinary/full build
or compiled blueprint declaration check is claimed here; these remain for
coordinated integration. Shared sources, caches and Mathlib were untouched.

Integration must regenerate the AreaLaw and root import aggregators for the
three new modules and register `ch35_alvv_low_density_entropy.tex` in the
area-law chapter. Generated aggregators and the chapter router are deliberately
excluded from this source-only contribution.

Final actual-name strict checks passed in 10.864 seconds (original-band
refinement), 11.903 seconds (capped entropy), and 8.662 seconds (regularized
entropy). The fresh imported three-name inspection passed in 8.038 seconds
and reported only `propext`, `Classical.choice` and `Quot.sound`. Temporary
inspection sources were removed. Source blueprint resolution, mathematical
role classification, added-prose review, the tactic pattern scan and whitespace
checks passed. Production files contain no proof-integrity blockers or test
commands.
