# Physical calibration for interleaved collective trimming

The supporting theorem
`TNLean.MPS.AreaLaw.exists_physical_dg_interleaved_filter_family`
constructs the clipped target, polynomial tensor-factor family and one common
MPS reference from the original positive nearest-neighbour chain. Its constants
precede the chain data; its families precede every candidate space and trimming
threshold. The reference precedes every interval. The actual operation is the
family image of the current space followed by collective trimming of an
orthonormal basis of that image.

The source is ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`, lines
1668–1670, and the parameter selection in lines 1797–1805. The correction to
the recursive assignment and the integer-round issue are documented in
[the approximation parameter note](../paper-gaps/alvv16_approximation_parameters.tex).
This is a supporting long-interval theorem, not a formalization of the entire
printed algorithm.

## Coupled estimates with independent analytic scales

Write r for the full ground-space dimension, g=min(gamma,1), and m=max(q,50).
The failure scale is fixed as (L+1)^(-2) before the family is chosen. Define

- w=1+log r+2 log(L+1), v=1+log m+log(1/g)+log(1+w);
- ell=ceil[C(v^6/g+sqrt(w)v^3/sqrt(g))], D=(m ell^2)^(22ell);
- s=ceil[4096r(log D+w)], a=3/(32D^12 s^5), tau=a^2/2^20;
- epsilon=200 tau, t=Ctail(1+log(1/g)+log(1/tau));
- Delta=1/(200000D^12).

Universal Ctail,C derive the physical tail bound
288 exp(11/8) exp(-(t-g)/8) <= epsilon g/10^6 and squared polynomial suppression
at most Delta for every physical spectral width at most 3t+4ell. Thus the
strict inequality D^12 Delta<10^(-5) concerns the same actual count used by
the family. Neither a desired tradeoff nor existence of a suitable analytic
scale is assumed. The count retains the explicit logarithmic bound
22(C+1)(14+2log(C+1))(v^7/g+sqrt(w)v^4/sqrt(g)).

A physical reference U has dimension r, mutual tau-closeness to the original
full ground space and the existing sharp all-span MPS bound Dref=r^2 B.
Every actual clipped target is mutually tau-close to the original space, and
therefore mutually 4tau-close to this same U. The whole exterior is retained,
so its Schmidt-rank estimate is Dref^2. At any positive threshold at most
a/(256Dref sqrt(L+1)), the actual interleaved step has error
Delta delta/(1-delta+Delta delta)+a/16 for the clipped target. The separate
original-target error is twice the sum of this quantity and tau. The actual
image operator has minimum target norm gain one; identity action on a
nonconstant low-energy band is not assumed.

## Scope

The physical theorem covers intervals longer than 4ell and retains capped-gap
quantitative dependence. The second spectral value is part of source (DG),
not an added uniqueness hypothesis. The initial successful Haar sample,
finite stopping envelope, recursive sampled tree and adaptive probability are
not conclusions of this theorem. No printed running time is claimed. The
short-interval construction and actual iteration theorems remain separate
results to be composed with this calibrated step.
