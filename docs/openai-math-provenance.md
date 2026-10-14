# Code from openai/math

TNLean formalizes parts of the September 24, 2026 area-law and polynomial-PEPS
manuscripts published in
[`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a).
That repository is licensed under Apache-2.0; [the license](../LICENSES/openai-math-Apache-2.0.txt)
is its root `LICENSE`, byte for byte. No `NOTICE` file exists at that revision.

## Rules

- **Original proofs** written from the manuscript cite it in the module's
  References section, as for any paper. No further notice is needed.
- **Copied or adapted Lean code** carries a notice in the module header naming
  the upstream file, the pinned revision and the changes made
  (Apache-2.0 §4(b)), retains any upstream copyright or attribution notice
  verbatim (§4(c)), and is listed in the table below.
- Prefer an existing Mathlib or QICLean result over porting an upstream one.
  Generic mathematics belongs in QICLean, tensor and lattice mathematics in TNLean.

Verification is ordinary CI: the module builds with the package options and
contains no `sorry`, `axiom` or `native_decide`. Do not commit build logs, axiom
transcripts or other evidence archives.

## Adapted code

| TNLean module | Upstream file | Declarations |
| --- | --- | --- |
| `TNLean/PEPS/Approximation/SquareGridSource.lean` | `lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean` | `Vertex`, `ForwardAdjacent`, `ForwardEdge`, `Pinned.IncidentEdge`, `Pinned.State`, `Pinned.LocalTensor`, `Pinned.contractPEPS` |
| `TNLean/PEPS/Approximation/SquareGridSource.lean` | `lean/OAI/MathematicalPhysics/TensorNetwork/VectorColumn.lean` | `Vector.IncidentEdge`, `Vector.State`, `Vector.Tensor`, `Vector.Tensor.contract`, `Vector.Tensor.maxBondDim` |
| `TNLean/PEPS/Approximation/PinnedRegionalState.lean` | `lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean` | `Pinned.RegionConfiguration`, `Pinned.joinConfigurations`, `Pinned.coefficientMatrix`, `Pinned.reducedDensity` |
| `TNLean/PEPS/Approximation/SourceApproximation.lean` | `lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean` | `Pinned.HasPEPSApproximation` |
| `TNLean/PEPS/Approximation/SourceApproximation.lean` | `lean/OAI/MathematicalPhysics/TensorNetwork/VectorColumn.lean` | `Vector.PhaseErrorAtMost` |

All other modules citing these manuscripts contain original proofs.

## Assistance

Upstream attribution and assistance disclosure are separate. Each implementation
PR names the tool and model that assisted it and the accountable human reviewer
under [the contribution policy](../.github/CONTRIBUTION_POLICY.md).
