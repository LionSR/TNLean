# Native MPS and Ritz extraction from the same interleaved root

`exists_physical_dg_interleaved_tree_ritz_approximation` constructs the NEW
interleaved balanced tree at the common radius used by all final raw-filter
and collective-trim iterates. Its initial native root and terminal Ritz space
both have the displayed all-span MPS bound. The proof calls no constructor
of the older one-final-trim tree and no independent MPS approximation theorem.

## Common radius and actual objects

The interleaved tree has radius bound xiTree=a/(256Dref sqrt(L+1)). Set
Ntree=ceil(1/a), ETree=Dref*Ntree. The ceiling yields a*Ntree>=1 and hence

    1/(1000ETree sqrt(L+1)) <= xiTree.

Apply the existing automatic SAME-candidate refinement with Dtree=ETree and
Dfilter equal to the actual interleaved D. For eta>0 it chooses

    A=||H||-mu>0, c=gamma/A, rho=eta*gamma/(2A+eta*gamma),
    n=ceil((4/c)log(1/rho))+1, epsilonFinal=c^2*rho/32768,
    b=r^2 Bfinal, Dcommon=max(ETree,b),
    Nfinal=ceil(100D^12/(c*rho)),
    xi=1/(1000Dcommon*Nfinal sqrt(L+1)).

The actual final physical reference, its accuracy and this xi precede every
initial candidate. The API derives xi>0, xi<=xiTree and the strict source
radius comparison sqrt(L*r*b)*xi<eta/(10000D^12). Instantiate the NEW tree
at exactly this xi. Its actual root S0 is 3/200-viable for original G, and its
native image W0 is 3/200-close to G by whole-interval coordinate transport.
All initial root vectors have MPS bond at most

    Bout=10^6(Dcommon*Nfinal)^2(L+1)M^2, M=D^6s^3.

This uses the actual recorded generators, retaining the extra span-count
factor. The final objects remain literal definitions:

    Kraw=toEuclideanCLM(I-||H||^{-1}H),
    S=fullIntervalFilterTrimIterate(Kraw,xi,S0,n),
    W=nativeFullIntervalSpace(S),
    R=the actual lowest-r compressed Ritz space of H on W.

The existing refinement theorem derives n>0, W rho-close to G, dim(S)<=M,
R<=W, dim(R)=r, both directed errors<=eta/2 and the all-span MPS bound Bout
for R. The exact equality A*rho/((1-rho)*gamma)=eta/2 is already part of
that result. No reference, initial/final viable space, numerical filter,
trial energy, truncation estimate or spectral comparison is supplied.
The source's second spectral value remains a physical input as in (DG).

The physical interval families precede eta. The root can depend on eta
through xi, but is selected once at that common radius and is then the
actual initial space of every final iterate. The literal parent operations
and their chosen Haar unitaries are retained alongside all interval
viability, dimension and weighted recorded-rank bounds.

## Quantitative scope

The source is ALVV, arXiv:1602.08828v2, Figure fig:merge-prime,
lines 1668–1670, and final refinement, lines 1809–1817. Block leaves,
g=min(gamma,1), the fixed nominal sampling/failure scale, the larger integer
parent count and honest length/rank-dependent D remain explicit. The final
count n is in rho; it is not identified with the printed count, as recorded
in the final-filter-gain note. No adaptive joint probability, source
energy-estimation invariant or running time is asserted. Uniform polynomial
simplification for the NEW variable-D profile is a separate corollary.
