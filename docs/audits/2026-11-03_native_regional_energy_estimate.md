# Native interval compression and a one-sided regional estimate

`exists_native_regional_compressed_energy_estimate` constructs one actual
Hermitian matrix K on the native configurations of an interval J, whose
identity extension is the original sum of bonds internal to J. K and
its canonical least eigenvalue e are chosen before every candidate S
and loss delta. If S is delta-viable for the entire original ground
space in the existing region-first tensor coordinates and

    0 <= delta <= 1/[100(L+1)],

then S has positive dimension. The actual orthogonal compression of K
to S has least ordered eigenvalue lambda in [e,e+3]. Therefore the
actual scalar p=lambda-3 lies in [e-3,e]. No gap, unique ground vector,
native matrix, local low-energy witness or compressed minimum is
assumed. Empty intervals, L=0 and q=1 remain covered by the stated
positive local dimension hypothesis.

## Relation to the source energy-estimation step

This is a conditional variational auxiliary supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631-1632 and its proof
at lines 1793-1807. The explicit loss condition is not supplied by the
recorded constant-accuracy tree result: loss 3/200 does not satisfy it.
Even the separate D^-6 estimate need not be bounded by 1/L under the
currently chosen scales.

The source constructs a separate untrimmed powered image of the child
product for energy estimation. It compresses the same generated soft
regional Hamiltonian on that image. Source line 1807 uses its smaller
norm and the accuracy of that separate image. Connecting those actual
objects and proving their quantitative energy estimate remain required;
this result does not close that energy invariant or the GEN procedure.
It does not change the retained merge space, its recorded dimension, or
its bond bound. It makes no runtime claim and does not use the false
printed cluster estimate. The corrected cluster construction and its
explicit dependence remain separate.
