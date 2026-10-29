# Local conjugation equations: delivered steps and remaining #7017 obligations

Base: `origin/main` at `3af48c184`, including the merged #8808 gate
Fundamental Theorem. Source: `Papers/1703.09188/paper_v2.tex`, Proposition
`prop1conj`, lines 1006–1039; equations `uconjugation`, `vconjugation`.

## Delivered proof text

`TNLean/MPS/MPU/ConjugationSymmetry.lean` adds nine declarations:

1. `Matrix.kronecker_map_star_mul_eq_one_of_gate_conjugation` derives
   `(conj(x)*x) ⊗ (conj(y)*y) = 1` from the literal local equation
   `conj(u) = (x ⊗ y)*u` and `u*uᴴ = 1`. It conjugates the equation twice
   and cancels the actual gate with its adjoint; the identity is not assumed.
2. `Matrix.transpose_eq_self_or_transpose_eq_neg_of_gate_conjugation` uses
   the existing common-sign theorem from #7711 to obtain the common
   symmetric or skew-symmetric case directly from that local gate equation.
3. `MPOTensor.mapStar` names coefficientwise conjugation without any index
   exchange. `MPOTensor.mpo_map_star` identifies the periodic operator of the
   coefficientwise conjugate tensor with the coefficientwise conjugate
   periodic operator, including length zero. It uses products and traces.
4. `Matrix.IsUnitaryBetween.map_star` transports both rectangular unitary
   identities. `MPOTensor.TwoSiteStandardFormData.mapStar` conjugates the supplied
   standard form, including its actual half factors, into a standard form
   of the conjugate tensor with exactly the conjugate supplied gates.
5. `MPOTensor.twoSiteUnshiftedLayer_map_star` and
   `MPOTensor.twoSiteShiftedLayer_map_star` conjugate the two circuit layers.
6. `MPOTensor.TwoSiteStandardFormData.map_star_mpo_eq_of_gate_conjugation`
   contracts both displayed local equations to conjugation invariance at
   every positive length of the supplied blocked tensor. The proof uses
   the exact two-layer circuit and cancellation of the internal unitaries.

The hypotheses are the actual supplied standard-form data and the local
equations in the direction being proved. There is no hypothesis asserting
existence of the missing gauges, no new symmetry predicate, and no parallel
source/admissible family. The common sign is obtained from the first local
equation alone. The second local equation is used in the circuit contraction.

## Exact current Fundamental Theorem boundary

`IsMPUCanonicalFormII.exists_source_gate_unitary_gauges_of_mpo_eq` now
provides the two unitary gauges from equal periodic operators at every
length greater than one. Its arbitrary-decomposition version,
`exists_source_gate_unitary_gauges_of_mpo_eq_sourceFactorsOf`, accepts both
compact decompositions for each comparison tensor and gives the same gate
equations after the explicit source-rank reindexings. These results are
present and must not be replaced by a supplied gauge-existence hypothesis.

To finish #7017's forward direction, one must transport the chosen compact
decompositions and canonical-form-II data under entrywise conjugation,
identify the resulting source factors with the conjugates of the supplied
factors, and remove the rank reindexings in the comparison equations.
The new `TwoSiteStandardFormData.mapStar` transports a supplied open
standard form; it does not by itself prove those chosen source-cut and
canonical-data identifications. The Fundamental Theorem is currently stated
for gates from the source factors, rather than arbitrary supplied open data.
Thus the exact forward local equations remain unproved here.

The existing gate converse in `FundamentalTheoremGates.lean` gives equality
at every positive blocked length. For the standard form of `blockTwo U`,
these are the original lengths `2*N`. The parity issue in
`docs/paper-gaps/mpu_standard_form_parity_gap.tex` prevents inferring the
unblocked all-length gate converse from this API. This audit does not claim
that the parity counterexample by itself refutes the conjugation proposition.
Any all-length conclusion must be justified separately or the exact theorem
must be stated on blocked families.

The source Blueprint node `prop1conj` stays `\notready`, with no new
`\leanok`. The two new auxiliary entries also stay `\notready` pending
compilation. Issue #7017 stays open.

## Source-only validation

No Lean build, elaboration, cache mutation, or compilation is run, as the
user explicitly requested. Checks inspect the pinned Mathlib signatures
for rectangular `Matrix.map_mul`, `Matrix.conjTranspose_map`,
`Matrix.mul_kronecker_mul`, list-product transport and trace transport, and
the exact circuit equality and unitary-gauge cancellation already in TNLean.
The generated import check, tactic-pattern scan, declaration/tag source
check, TeX formatter, whitespace/line-length check, and proof-integrity
placeholder scan are run. The source-only Blueprint scanner reports all
nine new declarations covered; its repository-wide scan also reports 547
unresolved references outside this addition, so full Blueprint synchronization
is not claimed. No compiled `checkdecls` is run. These checks do not establish
kernel acceptance.

## Hosted diagnostic repair

Hosted job `123398370707` found three elaboration errors in the first draft:
composition under `List.ofFn` was not unfolded, the local polymorphic
unitarity helper had a universe inference mismatch, and the circuit equality
was invoked without the ring length. The repair uses `Function.comp_def`, a
shared theorem with explicit gate arguments, and `(N := N)`. This repair is
source-checked against those existing logs; no local Lean command was run.
