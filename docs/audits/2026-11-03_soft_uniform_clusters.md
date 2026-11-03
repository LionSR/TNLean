# Uniform numerical precision for physical soft clusters

The three softened bulk regions and two unchanged windows of a finite chain
admit a spectral comparison whose hypotheses involve only prescribed scalar
parameters. The regional minima are selected once. The comparison uses the
same centered soft Hamiltonian throughout, including all five original
regional energy shifts.

The sources are ALVV, arXiv:1602.08828v2, `t:aisefficient`, lines 1373–1420,
and the corrected residual and norm-stability estimates documented in
`docs/paper-gaps/alvv16_soft_regional_residuals.tex` and
`docs/paper-gaps/alvv16_cluster_approximation.tex`. The new blueprint entries
are auxiliary lemmas, rather than assertions that the printed algorithm has
been formalized.

## Mathematical statement

Let the crossing count be C≤4 and the centered original ground energy satisfy
0≤E≤C. Softening exactly regions {0,2,4}, with centers in [e_j−10,e_j],
gives a soft ground energy μ≥−30. Hence the reverse residual threshold

    U = 2(E−μ+19g/20+30+3C+2)

is at most 156+2g. The two scalar inequalities in
`soft_cluster_scalar_residual_budgets` therefore imply the actual forward
and reverse residual bounds without a hypothesis involving μ.

For windows of width at most 2ℓ, the same attained regional minima give

    ‖G‖ ≤ M = 3t(1+log m)+4ℓ+34.

The lemma `soft_cluster_actual_window_losses` applies QICLean's numerical
finite-window precision bound. With

    ξ = min(1, τg²/[20000(M+g+8)]),

the literal lower and upper window losses are each at most τ/400.
The physical theorem `exists_five_region_soft_uniform_clusters` applies
both estimates to the existing single physical residual construction.
Every Hermitian approximation Ghat with ‖G−Ghat‖≤ξ has its own invariant
cluster at E+g/4, unchanged through E+3g/4. Its dimension equals the original
full ground-space dimension, and the two spaces are mutually 3τ/200-close.
The original ground energy is E+Σe_j. No gap or closeness assumption on either
softened matrix occurs in the theorem's signature.

The original regional minima, their common normalized minimizing vector,
and the centered energy E precede all centers and soft parameters. The
norm estimate consumes precisely these same minima. The proof does not
repeat the physical residual construction or select another Hamiltonian.

## Scope

The physical theorem retains explicit numerical residual conditions.
A separate scalar parameter-existence theorem can discharge them before
choosing a chain. Construction of an actual MPO approximation, a common
improving family, and an adaptive algorithm are further steps. In particular,
a pointwise choice depending on an estimated middle energy is not a family
chosen before all random samples. No such exchange of choices is asserted.

## Verification

The two numerical lemmas pass strict elaboration together in 3.952 seconds;
the physical theorem passes in 7.585 seconds. Both checks use the package's
strict implicit arguments, standard Mathlib linters, warnings as errors and
default proof-resource limits. Their dependency sources and objects are
protected by hashes against the fully built TNLean 88ab31ce / QICLean e817ea0
pair, with the separately checked spectral-precision, physical-cluster and
soft-norm dependencies supplied explicitly.

These are private, source-level checks against Lean/Mathlib 4.35.0-rc3.
All three new declarations have only the standard axioms `propext`,
`Classical.choice` and `Quot.sound` (imported inspection: 4.747 seconds).
The temporary inspection source was deleted. A read-only mathematical review
confirmed the constants, witness order and preservation of the original
regional data. Complete source/blueprint synchronization, theorem roles,
reader-facing prose, generated imports, pattern scan and whitespace checks
pass. The two-page mathematical excerpt compiles without overfull boxes.

Ordinary combined build and compiled blueprint checks remain required after
integration. Upstream main has independently advanced to Mathlib 4.36.0-rc1;
artifacts from that version are not mixed into these checks. No Mathlib
source was compiled and no ordinary build cache was modified.

One early local check was rejected by the source-hash guard after its
temporary input changed before completion. It is excluded from verification.
Subsequent checks each use a distinct immutable temporary source and import
map. Other failed diagnostics are retained separately from the successful
source records.
