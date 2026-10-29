# Fifth-root Weyl ingredients for the finite-prefix question

This is a partial mathematical construction for the remaining obligation
in [#10386](https://github.com/LionSR/TNLean/issues/10386), attached to
SPWC10 (arXiv:0909.5347), Theorem 5, source lines 850–880.
It is **not a proved counterexample** to the all-volume hypothesis.
In particular, a translation-invariant one-dimensional space alone does
not establish a fixed positive interaction with unique frustration-free
ground space at every permitted volume.

## Actual source-written matrix ingredients

Fix a primitive fifth root of unity \(q\). For \(u,v,i,j\in\mathbb Z/5\mathbb Z\), set
\[
 W(u,v)_{ij}=\begin{cases}q^{ui}&j=i-v,\\0&\text{otherwise}.\end{cases}
\]
The exponent is interpreted through the well-defined character of the
finite additive group. The actual multiplication law is
\[
 W(a,b)W(c,d)=q^{-cb}W(a+c,b+d).
\]
The three physical matrices are
\[
 X=W(1,0),\qquad Y=W(0,1),\qquad Z=q^{-1}W(-1,-1).
\]
Thus \(XY=qYX\), \(YZ=qZY\), \(ZX=qXZ\), and \(XYZ=1\).
The matrix source records an exact scalar exponent for every physical
word, rather than stipulating its virtual charge.

If the letter counts are \((a,b,c)\), the virtual charge is
\((a-c,b-c)\pmod5\). At fixed degree, this charge determines all three
count residues because three is invertible modulo five. At degree seven,
the central charge is absent and every other charge occurs. At degree
eight every charge occurs. A finite Fourier sum expresses each matrix
unit as a linear combination of the actual charged matrices. Therefore
the actual tensor is injective at every degree at least eight and is normal. It is not
injective at degree seven, because every degree-seven word is traceless.
Finally every degree at least eight has an actual word with nonzero
trace: each such degree is a nonnegative combination of three and five.

These statements are written without placeholders in
`MPS/Examples/ShortMomentum/{Charges,WeylWords,WeylSpans,LetterRelations}.lean`.
They have not been compiled. Their Blueprint entries remain not ready.
The character sum reuses QICLean's Weyl-twirl theorem; matrix-unit span
uses the existing TNLean matrix-unit helper.

The explicit dual matrices
\(D_{u,v}=q^{-uv}W(-u,-v)/5\) satisfy
\(\operatorname{tr}(W(p)D_q)=\mathbf1_{p=q}\).
Consequently `LocalSpace.lean` derives the exact actual local boundary-space
characterization at every length: its coefficients are the actual word phase
times an arbitrary function of total charge. The converse constructs the
boundary matrix from the trace-dual family. This is a local characterization,
not a supplied global-intersection hypothesis.

The cyclic exponent comparison is derived in `CyclicPhases.lean`.
`SevenCyclicObstruction.lean` gives two explicit physical words detecting
unequal cyclic phases at each of the 24 nonzero charges. Cancelling the
nonzero character factors in two actual local boundary vectors proves
that their seven-site cyclic agreement forces both vectors to vanish.
The actual seven-site periodic main-sector parent space is therefore
zero. This supplies the main exceptional-volume obstruction without
asserting the long-volume classification.

The same phase detection extends to every degree at least seven: use
explicit initial words at degrees seven, eight, and nine, then append
one copy of each physical letter. `CyclicBoundaryClosure.lean` therefore
derives that two actual global boundary vectors agreeing across the
cyclic cut close to the actual periodic trace line at every such degree.
This does not supply global boundary-space membership from local constraints.

`LongIntersection.lean` derives the actual one-step open intersection
whenever the shared middle has at least eight sites, by full actual word
span, the existing trace-pairing reconstruction, and the actual inverse
fourth power of the first letter. The two exceptional overlap steps
producing eight and nine sites remain to be proved before iteration
from seven-site constraints is justified.

## Proposed fixed-interaction construction: obligations still open

The intended main local space is the actual seven-site boundary MPS
space of \((X,Y,Z)\). An independent two-letter sector would use the
existing one-particle vector with a primitive seventh-root weight.
The local interaction would be the orthogonal-complement projector of
the direct sum of these two spaces, embedded in disjoint physical
alphabets. This gives one fixed positive local term once constructed.

The following are still required before any full counterexample claim:

1. Prove that the actual seven-site main relations imply adjacent cyclic
   q-commutation and transfer of five equal letters, in every surrounding
   physical configuration.
2. Prove completeness of the homogeneous relations and classify their
   **periodic** solutions at all lengths at least eight: the main sector
   should have exactly the actual nonzero trace-MPS line. The exceptional
   length-seven zero space is now derived separately. Reachable charges
   or a normality witness alone do not prove long-volume uniqueness.
3. Prove that the disjoint-alphabet local direct sum forces every global
   solution into the direct sum of the two uniform global sectors.
4. Supply the actual weighted one-particle overlap obstruction and its
   nontrivial cyclic phase, then assemble the fixed-projector kernel
   calculation at **all** permitted positive lengths.
5. Check the source's entire hypothesis set and the intended meaning of
   its all-volume conclusion. In particular, the already proved eventual
   fixed-tensor branch is not contradicted by an exceptional short length.

The separate one-particle overlap development addresses item 4. No
supplied local-kernel classification, finite-volume representation, or
norm-growth premise is being substituted for the remaining proof.

## Verification boundary

No Lean, Lake, cache operation, or local elaboration is run, as requested.
Native import, Blueprint synchronization/roles, prose, line-length,
proof-integrity, and diff checks are run before publication. Such checks
are source-policy evidence only; they do not certify Lean elaboration.
