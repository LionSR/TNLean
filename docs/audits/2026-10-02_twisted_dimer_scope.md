# The twisted dimer: length dependence and factorization

The construction in [issue #7611](https://github.com/LionSR/TNLean/issues/7611)
answers the question following Theorem 4.14 of arXiv:1606.00608: structure
coefficients of a renormalization fixed point can depend on circumference.
The tensor is a construction of this project, rather than an example printed
in that paper. This note distinguishes its established properties from the
additional non-factorization assertion investigated in
[issue #7751](https://github.com/LionSR/TNLean/issues/7751).

Let \(\Pi_\pm\) be the projectors onto the Bell vectors
\((|00\rangle\pm|11\rangle)/\sqrt2\), and put
\(\sigma=(7/8)\Pi_++(1/8)\Pi_-\) and
\(\sigma'=(7/8)\Pi_+-(1/8)\Pi_-\). At every positive length the density
operator, written in bond and flag coordinates, is
\[
\rho_N=2^{-N}\bigl(\sigma^{\otimes N}\otimes I^{\otimes N}
                 +\sigma'^{\otimes N}\otimes Z^{\otimes N}\bigr).
\]
The developed results establish positivity, trace one, explicit refinement
and coarse-graining channels, failure of simplicity in the sense of
Definition 4.7, vertical canonical form, and fusion with the normalized
coefficients \(7/10\) and \(1/10\). No pair of positive rescalings of the
two normal representatives makes their displayed coefficient family
independent of circumference. These are assertions at the specified physical
cut and for the stated representatives.

## What the factorization calculation establishes

Group the incoming bond \((R_{m-1},L_m)\) with the flag at site \(m\).
On one such cell define
\[
V=(I-\Pi_-)\otimes I+\Pi_-\otimes X.
\]
This is a self-adjoint unitary on the complete eight-dimensional cell,
including the complement of the two Bell vectors. It satisfies
\[
V(\sigma\otimes I)V^*=\sigma\otimes I,
\qquad
V(\sigma\otimes Z)V^*=\sigma'\otimes Z.
\]
Consequently the product of these gates, transported back to the site
coordinates, conjugates \(\rho_N\) to
\[
\sigma^{\otimes N}\otimes\tau_N,
\qquad
\tau_N=2^{-N}(I^{\otimes N}+Z^{\otimes N}).
\]
Both factors have trace one. The first is the mixed-Bell bond product;
the second is the even-parity flag state, identified with normalized
Example 4.12 of the source. Both factors have explicit renormalization
channels in the existing development.

The identity is proved by
`MPOTensor.TwistedDimer.mpo_eq_unitary_factorization` in
`TNLean/MPS/MPDO/TwistedDimerUnitaryFactorization.lean`. The exact factor
identifications and their channels are in `TwistedDimerFactorStates.lean`
and `TwistedDimerBondRFP.lean`. The construction provenance is preserved in
[the September 5 calculation](2026-09-05_twisted_dimer_unitary_factorization.md).
The more general finite-group separation is treated in
`rfp_intrinsic/sections/02_groups.tex`.

## Disposition of the broad assertion

The assertion that these weights cannot be separated into an independent
bond factor is withdrawn when neighboring-register regrouping and these
specified unitary gates are allowed. The displayed identity is a direct
factorization of the actual density operators, at every positive length.
Thus failure of simplicity and the obstruction to rescaling normal
representatives do not establish non-factorization under those operations.

The construction does not claim non-factorization under a narrower class
consisting only of on-site physical unitaries and virtual similarities.
Such a class changes the mathematical question, and the existing operator
identity neither proves nor disproves the corresponding tensor statement.
There is no general non-factorization theorem to attach to this example.
A future theorem about that narrower relation must specify the permitted
factors and whether blocking is allowed. It must not be presented as a
consequence of the coefficient-rescaling obstruction.

## One tensor-power construction

For the consolidation requested in
[issue #7786](https://github.com/LionSR/TNLean/issues/7786), `powN` denotes
the constant-family instance of `Matrix.finKronecker`, and
`gPow k N = powN (gLoc k) N`. Multiplication, conjugate transpose, and
identity are handled by the existing `Matrix.finKronecker_mul`,
`Matrix.finKronecker_conjTranspose`, and `Matrix.finKronecker_one`.
The former private proofs `powN_mul`, `powN_conjTranspose`, and `powN_one`
are removed. The mathematical statements of the dimer results are unchanged.
