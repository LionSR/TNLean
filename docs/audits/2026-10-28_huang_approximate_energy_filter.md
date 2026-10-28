# Gaussian filtering at an approximate ground energy

`Huang/ApproximateEnergyFilter.lean` proves the spectral estimates needed for
[Huang, arXiv:1406.6355v6](https://arxiv.org/abs/1406.6355v6), Section 5.4,
equation (19) and Lemma 18. It does not assert the normalized energy conclusion
of that lemma or construct a finite matrix product approximation.

Let H be Hermitian, let Γ be a unit eigenvector of energy E₀, and suppose

H − E₀I ≥ Δ(I − |Γ⟩⟨Γ|),     Δ > 0.

For a variance h ≥ 0 and energy estimate E, the actual Gaussian integral is

Gₕ(H − EI) = f(H),     f(x) = exp(−h(x − E)²/2).

If |E − E₀| ≤ Δ/2, the module proves

‖Gₕ(H − EI) − c₀ |Γ⟩⟨Γ|‖ ≤ exp(−hΔ²/8),
     c₀ = exp(−h(E₀ − E)²/2).

The ground coefficient cancels exactly. At every excited energy λ, one has
λ − E ≥ Δ/2, and the spectral norm gives the estimate without a dimension
factor. A separate theorem proves exp(−1/2) ≤ c₀ ≤ 1 whenever
h(E₀ − E)² ≤ 1. Zero variance is included through the point-mass convention.

The operator depends on H, E and h. The number c₀ is an analytical quantity
involving the true ground energy. The present statement does not require the
constructed finite family to be rescaled by that unknown number. A subsequent
viability argument must retain its positive lower bound when normalizing a
witness, together with the finite-operator approximation error.

The main proofs reuse QICLean's exact Gaussian eigenvector coefficients,
ground-or-excited spectral dichotomy and rank-one ground-projection identity,
and Mathlib's continuous functional calculus norm bound. The small eigenbasis
action helper is recorded in the tactic ledger as a candidate for consolidation
with its companion-library counterpart. All mathematical imports are from
Mathlib and QICLean; the generic Gaussian results belong upstream in QICLean.

The actual module passes strict separate compilation with warnings treated as
errors. The imported foundation fixture checks all three public declarations,
and every observed axiom is among `propext`, `Classical.choice` and `Quot.sound`.
The checked module SHA-256 is
`bc4023f21db6814a80e6265a3bbdfc6e8d164b5e246a63e7657ce0e7f061a93a`.
Checks read the existing prebuilt dependencies and write only private temporary
objects; Mathlib is not rebuilt. The ordinary locked module build also passed
(9.1 seconds for this module), reusing the prebuilt Mathlib cache. The next
integrated full-library and compiled blueprint gates remain pending for this
additional contribution.

An independent mathematical review checked the
energy-shift sign, finite-spectrum functional calculus, ground projection,
amplitude budget, empty-dimension case and the distinction from the normalized
source conclusion. No material defect was found. The new blueprint section
passes configured ChkTeX and was rendered and inspected.
