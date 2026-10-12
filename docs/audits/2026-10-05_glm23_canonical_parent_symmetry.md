# GLM23 canonical parent symmetry under explicit adjoint closure

Source: `Papers/2203.12563/REsubmission.tex`, v3, compatibility at
lines 431–469, Section 5 at lines 1236–1320, and Appendix B at lines 2457–2466. The vendored
source and license are recorded in `Papers/NOTICE.md` and the main
GLM23 source inventory. This is a conditional physical-parent result,
not a construction of the source's weak-Hopf realization.

## Mathematical dependency chain

1. `BoundaryParentCommutation` derives invariance of the actual
   arbitrary-boundary MPS support from the length-independent
   `IsBoundaryCompatible` condition. If the entire local MPO boundary
   range is adjoint-closed, the support and its orthogonal complement
   are invariant. Consequently the canonical local parent `I-P` commutes
   with every boundary operator. Adjoining the ambient identity to the
   auxiliary star algebra does not assume that the MPO's represented
   support unit is the ambient physical identity.
2. `BoundaryCut` expands a periodic boundary trace over a prefix and
   complement using matrix units. The prefix formula permits arbitrary
   global boundaries and empty cuts. Its cyclic-window form requires
   the global virtual boundary to commute with every tensor letter;
   the individual cut boundaries remain unrestricted. This proves
   local-to-periodic commutation for every cyclic placement, including
   wrapping windows.
3. `NonzeroInteraction` uses the rank bound on the boundary map to prove
   that the canonical local interaction is nonzero when
   `d^L > D^2`. It requires neither injectivity nor a supplied spectral gap.
4. `BoundaryParentHamiltonian` combines these results for the actual
   cyclic sum of local terms, in both Euclidean and function-space
   coordinates. It retains positive interaction length and `L ≤ N`.
5. `BlockBoundarySelector` defines the unweighted direct-sum MPO and
   each summand's virtual selector. Each selector commutes with every
   assembled tensor letter and its trace extracts exactly the selected
   periodic operator, even at length zero and for zero-dimensional
   summands. A selector need not be central in the full commutant when
   equivalent blocks occur.
6. `BlockBoundaryParentHamiltonian` therefore proves commutation with
   every labelled MPO individually. Operator and state labels may be
   different finite types. Only adjoint closure of the whole assembled
   boundary range is required; separate closure of each label is absent.

7. `BoundaryUnitSupport` uses length-independent compatibility to identify
   the output state boundary from one positive injectivity length `L₀`.
   A fixed boundary `U` with `O_U^{L₀}=I` then fixes every boundary MPS,
   the entire ground space, and its canonical projection at every positive
   target length `n`: `Q_n P_n=P_n`. There is no ordering condition between
   the two lengths, no adjoint-closure hypothesis, and no nonzero-dimension
   premise. One-site variants specialize the same argument.
8. `BoundaryProjectionAverage` derives canonical support-projection
   commutation from the actual target-length adjoint-closed boundary range.
   For finite actual boundary families `X_i,Y_i`, the sole family
   normalization `∑ O_Xᵢ O_Yᵢ=Q_n`, combined with the unit-support criterion,
   gives `E_n(P_n)=P_n`. The literal canonical-parent average is therefore
   `Q_n-P_n`, while its ambient completion is `I-E_n(P_n)=I-P_n`.
   Only this ambient completion receives the dimension-based nonzero
   result. Empty index families and zero dimensions are retained wherever
   the explicit hypotheses can hold.

## Scope and the weak-Hopf distinction

The local adjoint-closure assumption is explicit and has not been derived
from an MPO fusion algebra in this package. No unit, duality, dagger,
weak-Hopf integral, physical coproduct realization, gap, or exact periodic
ground-space characterization is inferred from arbitrary-boundary
compatibility alone.

For a weak-Hopf average, `E(I-P)=Q-E(P)` with `Q=ρ(1)`; this differs from
the ambient complement `I-E(P)`. The nonzero theorem here concerns the
canonical ambient parent. The companion note
`docs/paper-gaps/glm23_wha_parent_completion.tex` gives an independently
reviewed mathematical example where the uncompleted average vanishes.
That example is not a Lean weak-Hopf instance, and it is consistent with
Appendix B read as constructing `I-E(P)`. The source WHA assertion remains
open until its physical representation is constructed and its specific
adjoint closure, unit-support condition, and normalized finite families are
derived. The positive injectivity/calibration criterion is sufficient; it
is not an assertion that arbitrary compatible tensors or every block family
already satisfy it. No averaged-projector conclusion is carried as a premise.

## Verification

All eight exact production sources passed targeted compilation on 5 October
2026 with the pinned Lean and dependency versions. All four regression files
passed the strict CI option set. All fifteen guarded axiom reports enforce exactly
`propext`, `Classical.choice`, and `Quot.sound`. This is a targeted source
checkpoint; no full-repository result is inferred from it.

The tests cover empty cuts, wrapping windows, a zero nonunital MPO,
nonzero canonical interactions, different operator/state labels, and
individual-block extraction, target lengths shorter than calibration lengths,
a zero state-bond dimension, empty averaging families with all dimensions
zero, and `Q_n=P_n` yielding zero literal parent average. The unit-support
regression also shows why its positive-length restriction cannot be dropped.
These tests do not substitute signature checks for a claimed weak-Hopf construction.

The final averaging production source has SHA-256
`4217c0ba8d4dfd9b454908171b620316c28a55ab4dedb9e97095ddb8c758a766`;
its strict test has SHA-256
`f3e75e0dccce36250e3ea8174eeab37b9f743a66fc6ed1193f5cfe76220230cb`.
The test's five exact standard-three guarded reports passed together with
strict elaboration. This does not upgrade the mathematical weak-Hopf example
in the companion note into a checked weak-Hopf instance.

All 34 public declarations have exactly one owner in
`ch30_mpo_boundary_parent.tex`. The original 24 owners remain in their original
entries. The ten added declarations are owned as follows:

- `thm:glm_boundary_parent_local` adds
  `MPOTensor.IsBoundaryCompatible.groundSpaceES_starProjection_commute_mpoWithBoundary`.
- `thm:glm_boundary_unit_support` owns
  `MPOTensor.IsBoundaryCompatible.mpoWithBoundary_mulVec_eq_of_one_length_eq_one`,
  `MPOTensor.IsBoundaryCompatible.mpoWithBoundary_mulVec_eq_of_one_site_eq_one`,
  `MPOTensor.IsBoundaryCompatible.mulVec_eq_of_mem_groundSpace_of_one_length_eq_one`,
  `MPOTensor.IsBoundaryCompatible.toEuclideanLin_comp_groundSpaceES_starProjection`,
  and `MPOTensor.IsBoundaryCompatible.toEuclideanLin_comp_groundSpaceES_starProjection_of_one_site`.
- `thm:glm_boundary_projection_average` owns
  `MPOTensor.IsBoundaryCompatible.sum_mpoWithBoundary_groundSpaceES_starProjection`,
  `MPOTensor.IsBoundaryCompatible.sum_mpoWithBoundary_parentInteractionES`,
  and `MPOTensor.IsBoundaryCompatible.one_sub_sum_mpoWithBoundary_groundSpaceES_starProjection`.
- `thm:glm_boundary_average_nonzero` owns
  `MPOTensor.IsBoundaryCompatible.one_sub_sum_mpoWithBoundary_groundSpaceES_starProjection_ne_zero`.

Independent mathematical review found no blocker in the original conditional
parent results. Their focused seven-page blueprint preview had been rendered
and visually inspected. The three Tenkz networks are byte-for-byte unchanged
by the averaging extension. Their matrix-unit orientation remains
`tr(E_ba XU) tr(E_ab V)`, summing to `tr(XUV)`. The enlarged eight-page focused blueprint and four-page completion note
were rendered and every page was visually inspected. Final logs contain no
warnings, unresolved references, overfull boxes, or underfull boxes. New
formulas, hypotheses, declaration badges, and source links are legible and
unclipped. Both edited TeX files pass pinned latexindent 3.24.7 idempotence
checks. Static source checks resolve every referenced label and dependency
and confirm all ten new declarations have exactly one blueprint owner.

Subsequent integration commits must satisfy exact-head repository CI and
review gates. The live PR and its check runs record that validation; this
source checkpoint does not certify later trees or full-paper completion.
The standalone companion-note and focused blueprint renders are separate
documentation checks; neither is a full-repository build.
