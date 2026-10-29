# Actual pure outputs of physical-port unitary dilations

Issue #8640, native tracker #8622. Source: Piroli, Styliaris and Cirac,
arXiv:2103.13367v3, main-text paragraphs “Quantum circuits and LOCC” and
“State transformations with QC and LOCC”. The source HTML was checked at
https://arxiv.org/html/2103.13367v3, lines 39–56. The approximate relation
in lines 102–107 traces ancillas and separately fixes the number of composed
QCcc channels. Those conditions are not equated with a quantum-depth bound.

## Existing bounded compiler

Main already contains bounded-register routing, a compiler with overhead
2*ceil(log_d B)*T uniform in chain length, original-port input/output with
reset of designated data/scratch memory, and a genuine unitary realization
with local product-zero environments and one final discard. This work does
not reintroduce those constructions or claim they are missing.

## Actual new derived step

`PhysicalPortPureOutput.lean` derives a pure-vector output identity for the
actual compiled unitary when the actual channel sends a pure input to a
specified normalized pure output. It keeps the existing physical ports,
spatial environment ownership, intersite depth and equality of the channel
on all operators. The output factors into the specified system vector and
a derived normalized environment vector. No decoupling premise is supplied.

The proof writes the actual joint vector as a coefficient matrix C. Its
actual marginal gives C*C†=P for the rank-one projector P onto the target.
P²=P and the existing Mathlib positive Gram zero criterion imply (1-P)*C=0.
Thus C=P*C and the environment coefficients are exactly star(phi)*C.
The marginal trace and normalization of phi normalize that vector. The
actual dilation equality supplies the marginal identity; this is not an
assumed purification or opaque simulator.

## Precise limits

The environment need not be a product over spatial sites and need not
reset to its initial zero state. The new theorem is an exact pure-output
bridge, not a robustness theorem for approximate outputs. It does not
construct a fixed number of source QCcc blocks, prove their internal
measurement/control restrictions, or identify unrestricted enlarged-site
protocols with the source relation. Issue #8640 remains open.

## Verification

No local Lean invocation, compilation, build or persistent Lean fixture.
New proof text is a draft candidate with Blueprint notready; source/API,
import, prose, deterministic LaTeX formatting, tactic-pattern, width,
integrity and diff checks do not establish Lean acceptance. Hosted checks
must validate the result. No placeholders, axioms or parallel predicates.
