# Range projections and physical detectability

For a positive nearest-neighbour chain H=sum h_i of contractions, the
actual range projections P_i preserve the original bond supports and satisfy
H <= sum P_i and ker H=ker sum P_i. Consequently the physical even/odd
product of their complements obeys

    ||DL(P)x||^2 <= 4/(4+gamma) ||x||^2

for every vector x orthogonal to the entire original kernel, when every
nonzero eigenvalue of the original H is at least gamma>0. There is no
ground-space dimension, unit-vector or upper-gap hypothesis. Positive local
dimension is explicit. The proof uses the original spectral quadratic-form
bound, kernel invariance of the constructed even/odd product, and the physical
energy estimate for the same range projections. A gap of the new Hamiltonian
is not assumed.

This is the range-projection reduction preceding the detectability argument
in ALVV, arXiv:1602.08828v2, Section 6.1, lines 1457–1460. The regional
frustration-free truncated Hamiltonian, its spectral comparison and its rank
estimates remain separate work.

## Existing structures and source reuse

The construction uses the existing Matrix.IsHermitian.supportProj and its
positive-semidefinite specialization. No parallel projection, gap or support
definition is introduced. The shared supportProj_eq_cfc identity replaces
duplicated indicator calculations in CfcConjugation and
RelativeEntropySupportIntegral. The norm comparison uses Mathlib cfc_mono
and spectrum.norm_le_norm_of_mem, with the empty matrix index treated
separately. The sum-kernel argument reuses the existing positive-sum kernel
lemma in MatrixAux. The physical support proof uses the existing commutant
characterization of supportedOperators, rather than a second description of
local support.

## Private verification

The read-only providers are TNLean e6785a190e5ffe603dd9ca238451696c70bdc7b5
and QICLean 01f237e808b03fb0612ceb617f9bca2c407da927. The TNLean revision
is a documentation-only successor of checked mathematical source 908de62.
Strict named-module checks passed for all three new modules and both
refactored companion modules. The final imported inspection covers the six
new public declarations and both directly affected older public results.
Only propext, Classical.choice and Quot.sound occur. Exact source and private
object hashes are in /tmp/tnlean-range-projectivization-20261029/manifest.json.
The foundation inspection verified that its private objects were unchanged.

These elaborations wrote only temporary outputs; no provider source, package
pin or ordinary build cache was changed. Mathlib was not rebuilt, no altered
cache artifacts were copied, and no permanent test fixture was added.
Canonical combined-library and compiled-blueprint checks remain for common
integration.
