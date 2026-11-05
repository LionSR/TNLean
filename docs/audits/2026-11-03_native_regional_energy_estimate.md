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

## Construction and verification of the minimum

Designated nearest-neighbour supports imply that the original regional
matrix is supported on J. Fix the zero configuration of its complement
and take the actual matrix slice on J. The supported-matrix identity
shows that its identity extension is the original regional matrix.
Hermiticity and positive scalar lower bounds restrict to this slice.
The positive shift by the native canonical minimum lifts back to the
full space. These two comparisons identify that canonical minimum with
the actual attained full regional minimum returned by
`exists_regional_ground_energy_bound`.

The tensor coordinate isometry is exactly the one used in the current
regional improving families: complementary configurations followed by
native interval configurations, the product orthonormal basis, and the
exchange of factors. A singleton instance of the existing Kronecker
conjugation theorem proves the intertwining with the actual native
matrix. No representation identity is supplied as a hypothesis.

Pull S tensor the full complement back through this isometry. The
original-ground energy theorem constructs a nonzero vector in that
physical candidate with centered energy at most three times its squared
norm. Transport it to the tensor product. The previously proved tensor
energy minimum lemma produces a genuine unit local vector in S, giving
the variational upper bound e+3 for the actual compression. Positivity
of K-eI gives the lower bound e. The generic matrix comparison and
compression arguments are owned by the separate QICLean module
`Analysis/CompressionEnergyBounds.lean`.

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

## Verification

The exact physical module passed private strict actual-name elaboration
in 14.155 seconds at the default heartbeat budget. Its imported public foundation
audit passed in 4.620 seconds, with only propext, Classical.choice and
Quot.sound. It reads the immutable
checked TNLean provider 478e8a08f8d97cec4064070a29170a0953362d3e and
QICLean 9578336a5123a76001a1218e271132091c828de2, with only the new
checked QIC comparison leaf supplied as an explicit private object.
The source/object closure, build inputs and prebuilt Mathlib object
were guarded before and after checking. New objects are only under
/tmp; no provider source or shared cache was changed and no Mathlib
source was built. Ordinary combined and compiled-book checks remain
required after adoption.
