# Simultaneous energy estimates on the same actual interval tree

The contribution constructs one scalar function on all valid intervals of
the existing calibrated physical interleaved tree. It retains the same
chosen targets T, operator families F, family sizes N, merge operation and
retained spaces. All original parameter formulas, word bounds, dimension
bounds, generator rank bounds and literal sampled-merge identities remain
conclusions for those objects. No second physical family is selected.

## Recursive construction

The function is constructed by well-founded recursion on interval length.
At a short interval, its value is an actual attained minimum of the
original regional Hamiltonian. The minimum and a normalized eigenvector
are obtained from the proved physical adjacent-interval minimum theorem;
no minimum, eigenvector or energy estimate is supplied as an input.

At a long interval [l,r), let k=l+floor((r-l)/2). Both child intervals are
strictly shorter because the leaf width 4ell is positive. The two already
assigned scalar values have lower error at most 49/16. The fixed node
update constructs attained collar minima cL,cR and the center

    pMiddle = p(l,k)+p(k,r)-cL-cR-2.

The original positive connecting bond bounds the parent error of the
child sum by 57/8 <= 8. Consequently the middle center lies in the full
one-sided interval [eMiddle-10,eMiddle]. The node then uses the same
family's literal one-word image of the actual retained child spaces.
Its scalar value is the actual least eigenvalue of the raw native soft
operator compressed to that image, minus three. The complete orthonormal
eigenbasis, actual compression eigenvector equations and decreasing
ordering are part of the node certificate, inherited without weakening
from the proved physical callback.

The recursive value carries its original-regional error certificate.
The defining equation proves that the node relation uses precisely the
values of that same function on the two children. The resulting one-sided
bound is

    e[l,r)-49/16 <= p(l,r) <= e[l,r)

for every valid interval. At short leaves the error is zero. Values outside
the valid interval domain are set to zero only to express the result as a
total function on pairs of natural numbers; all mathematical conclusions
are restricted to valid intervals.

The physical theorem obtains the existing tree once and applies this
recursion to its proved node updates. Family and target choices still
precede the trimming accuracy; the scalar assignment follows the chosen
merge operation. The leaf and node statements include weak endpoint cuts
and intervals of length zero. The fixed-tree recursion assumes only positive
local dimension and positive leaf width. The physical spectral-gap theorem
retains its original hypotheses and derives positive local dimension.

## Source and scope

The source is ALVV, arXiv:1602.08828v2, Figure fig:algo1 at line 1631 and
its energy argument at line 1807, in
References/1602.08828/local_alg_arxiv_v2.tex. The one-sided soft-center
interface is Definition def:soft-trunc at lines 1178–1185.

The invariant belongs to the corrected hard-clipped construction. The
update has the proved downward bias by three and uses actual collar
minima. It is not an identification with literal soft Generate, its printed
energy-power count, or its running-time assertion. In particular, actual
finite-dimensional minima and eigenspaces here are mathematical existence
constructions. No efficient computation or adaptive joint sampling law is
asserted. The existing false printed cluster and soft-energy records and
counterexamples remain unchanged. The scope is recorded in
[the regional centering note](https://sirui-lu.com/TNLean/paper-gaps/alvv16_soft_regional_energy_centering.pdf).
