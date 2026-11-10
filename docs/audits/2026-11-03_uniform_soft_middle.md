# Fixed native soft tensors before the estimated energy

The new native construction starts from the actual positive-contraction
nearest-neighbour terms and one regional lower energy eI <= A. Its site
tensors and closing coefficient matrices are chosen before every estimated
energy p <= e. With z=exp((p-e)/t), the represented native matrix is

    Z(z)=traceChainOperator(Acore, sum_a z^a C_a).

It and its physical placement are Hermitian for every real z. For every
p <= e, one has 0<z<=1 and both the native principal restriction and the
original-chain soft term h_(m,t)(A-pI) differ from this same Z(z) and its
placement by norm at most xi. The scalar pI is kept exact and separate.
No family, supplied heat approximant, tensor representation or cut-rank
bound occurs among the hypotheses. The lower energy is a genuine scalar
order certificate, as in the existing heat approximation theorem; a
physical application supplies the actual regional minimum already chosen
by its single physical constructor.

## Actual construction and order of choices

Each required heat atom exp[-a(A-eI)/t], a=0,...,m, is approximated once
using the original masked local terms. Each actual operator chain is then
Hermitianized and restricted once to native coordinates. A block-diagonal
sum produces one fixed site family. Its closing coefficients contain the
exact heat coefficients c_a. Thus every estimate p changes only powers of
z in the cap, without selecting a new tensor family. The exact heat
expansion and sum|c_a| <= W=t*2^(m+1) imply a uniform error bound because
z^a <= 1. The cluster order is the same explicit logarithmic ceiling as in
the existing prescribed-accuracy constructor. The bond is

    B=2*r^2*q^r*(m+1).

There is no extra local-sum contribution: pI is represented separately.
Empty native intervals are permitted. The physical chain has N+1 sites,
so it is nonempty; local dimension q>0 supplies the exterior configuration.
The assumption t>=3m with m>=1 keeps all heat times in [0,1/3].

The common-closing theorem strengthens the existing weighted-sum proof to
fixed arbitrary input caps Q_a and all weights at once. It includes empty
chains. The three previous weighted-sum signatures are byte-identical,
and remain active specializations with Q_a=I and final cap absorption.
The finite cap-linearity identity is shared with the subsequent polynomial
interpolation argument; it introduces no second operator representation.

The existing native supported-slice proof has been moved byte-identically
from the pointwise soft-middle module to NativeIntervalMPOApproximation.
Its two old public consumers retain byte-identical signatures. The numerical
heat-base proof is exposed unchanged in its current owner, rather than
repeating the logarithm estimate. These preservation checks are recorded
in the external verification manifest.

## Source scope

This is supporting operator algebra for ALVV arXiv:1602.08828v2,
def:soft-trunc, lem:exp-approx-eff and prop:Cheby-AGSP-eff, lines 1178-1189,
1262-1268 and1311-1333. It uses the corrected interaction-label cluster
estimate and lower-energy normalization documented in
[the cluster-approximation note](../paper-gaps/alvv16_cluster_approximation.tex).
The one-sided lower-estimate convention is retained. The theorem does not
assert a common improving family, polynomial interpolation, automatic
count/error calibration, an adaptive measurable choice, or the printed
running time. In particular, it does not identify arbitrary tensor choices
from the previous pointwise existence theorem with the newly chosen
uniform family. The next interpolation step must retain these actual fixed
cores and polynomial cap coefficients.
