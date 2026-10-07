# Provenance validator fixtures

These files are test data, not production Lean modules or evidence of a compiled
port. Every build/axiom log synthesized by the test suite is explicitly synthetic.

`Source.lean.txt` is the unchanged first 13 lines of
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`lean/OAI/MathematicalPhysics/TensorNetwork/VectorColumn.lean` (Apache-2.0).
The source prefix has no copyright/author header. The license is retained at
`LICENSES/openai-math-Apache-2.0.txt`. This is a copied **excerpt**, not an example
of a copied whole-module ledger classification.

`Adapted.lean.txt` changes the real source `OAI.PolynomialPEPS.Vertex` to
`Example.Vertex`, spells the natural-number type `Nat`, omits unrelated source
and imports, and supplies a visible provenance notice. This is an adaptation
fixture only. It is not imported into TNLean or claimed as a theorem.

The four `planned-*` fixtures exercise all reuse kinds. The replacement fixture
uses a synthetic commit and proposed companion path; it does not assert that a
library theorem exists. The three `invalid-*` JSON fixtures must fail. Further
negative cases in the test suite mutate valid rows and source/evidence files to
exercise semantic checks, including changed modules marked copied.
