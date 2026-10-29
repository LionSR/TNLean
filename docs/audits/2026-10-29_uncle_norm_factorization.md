# Actual two-wall norm factorization and quadratic growth

Source: arXiv:1210.6613, `Papers/1210.6613/UncleHMPS.tex`,
Lemma `lemma:exptransferoperator` and the first assertion of
`lemma:lowenergystates`, lines 1165–1265. This stacks on the exact finite
transfer norm identity in #10320 and the actual wall Gram calculations in
#10317. No local Lean build, elaboration, or checkdecls was run.

The source context is the normalized standard form: unital diagonal
blocks and faithful stationary dual trace-one densities. The final generic
norm theorem derives strict mixed damping in both orientations from the
full perturbation witness. Intermediate transfer estimates retain explicit
mixed-gap inputs for reuse, while the final theorem has no supplied
mixed-gap, diagonal-injectivity or primitivity hypothesis. All new Blueprint
entries remain `notready`.

`UnclePrimitiveTransfer.lean` derives actual pure-block geometric decay
from block injectivity and unitality. The adjoint letter family is
injective by span induction and trace preserving by unitality. Existing
QICLean word-spread and peripheral-adjoint results give primitivity of the
original transfer. Perron eigenvector uniqueness for irreducible positive
maps makes fixed matrices scalar. The stationary trace functional then
identifies the canonical projection and gives a strict complementary
spectral-radius gap. No primitive, complementary-gap, or convergence
hypothesis is introduced into the public bound.

`UncleMixedDamping.lean` derives strict mixed damping from the actual full
perturbation span. The block-diagonal channel is unital with a faithful
stationary block density. A peripheral mixed eigenvector satisfies the
Kraus intertwining identities by the existing QICLean weighted Schwarz
equality. Coefficients isolating the second block identity and zero first
block force that eigenvector to vanish. Conjugate transpose proves the
reverse mixed gap. This removes the previously explicit mixed spectral
assumptions from the main generic norm theorem; it does not replace them
by an operator-norm-below-one premise.

`UncleNormFactorization.lean` replaces the two separated pure transfer
powers in the actual finite contraction by those canonical projections.
The replacement error is bounded using geometric decay, unital pure-map
contractivity, faithful normalized trace contraction, and the actual
linear moving-wall map bounds from #10317. The operator trace is bounded
through the norm of its existing finite-dimensional continuous linear
functional. The leading term is the exact rank-one contraction already
proved in #10320. The resulting actual complex transfer error is at most
C*(N+1)^2*z^N, with C>0 and 0<z<1.

The exact physical norm identity then gives actual squared norm divided
by (N+1)^2 tending to the real part of the product of the actual wall
slopes. This statement has no positive-slope or norm-growth premise.

`UncleNormGrowth.lean` derives diagonal block injectivity from one full
perturbation witness by surjective diagonal projections. Combining the
normalized norm limit with the derived pair-space genericity in #10317
gives eventual quadratic upper and lower bounds on the actual source trial
for almost every wall pair, under one arbitrary additive Haar measure.
The positive coefficient is derived, not stipulated. No full perturbation
condition is imposed on every varied wall pair merely to prove this norm
bound; the fixed witness supplies nonidentity of the actual quadratic forms.

The ground-space overlap estimates, projection away from the complete
finite ground space, and the final variational spectral argument remain
separate. No gaplessness or infinite-volume spectrum theorem is claimed.
Hosted Lean acceptance of these new modules remains pending.
