# Issue #234 audit — remaining commuting-parent-Hamiltonian and decorrelation gaps

## Scope of this audit

Issue #234 is no longer missing its basic surface.
On current `main`, the repository already contains:

- `TNLean/MPS/ParentHamiltonian/Commuting.lean` with
  - `MPSTensor.IsCommutingParentHam`
  - `MPSTensor.IsNNCPH`
  - `MPSTensor.rfp_implies_nncph`
  - `MPSTensor.nncph_implies_rfp`
- `TNLean/MPS/ParentHamiltonian/Decorrelation.lean` with the backward decorrelation theorem
  `Decorrelation.commutingHam_isDecorrelated`
- `TNLean/MPS/RFP/Decorrelation.lean` with the abstract
  commuting-idempotent algebra and the extended
  `HasCommutingParentHam` / `IsDecorrelated` API
- `TNLean/Axioms/Beigi.lean`, which records the two sanctioned trusted assumptions
  currently used by the Theorem 3.10 wrappers.

So the honest remaining work for #234 is **not** “define commuting parent Hamiltonians.”
It is the pair of deeper follow-up gaps described below.

## Small formal progress landed so far

The first parent-Hamiltonian follow-up added two theorem wrappers to
`TNLean/MPS/ParentHamiltonian/Commuting.lean`:

- `MPSTensor.HasProductPairLocalProjectors.isNNCPH`
- `MPSTensor.ProductPairBridge.isNNCPH`

Those results are immediate from the already-proved unfolded commutation theorem in
`TNLean/MPS/RFP/CommutingBridge.lean`, but they matter conceptually: they isolate the internal
`RFP ⟹ NNCPH` task to **constructing the product-pair witness**, rather than reproving the NNCPH
wrapper each time.

The 2026-04-25 follow-up records the upstream Appendix B input and adds a conditional internal
route that does not call `Axioms.rfp_to_nncph_commute`:

- `MPSTensor.AppendixBStructuralData` bundles the structural decomposition
  $A_i = X \Lambda U_i X^{-1}$;
- `MPSTensor.AppendixBStructuralData.ofRFP` extracts that bundle from
  `rfp_nt_structural_full` under the normal, RFP, and left-canonical hypotheses;
- `MPSTensor.AppendixBStructuralData.twoSiteAmplitude` defines the two-site amplitude
  determined by that specific structural witness;
- `MPSTensor.AppendixBProductPairExtraction` names the remaining chain-space extraction from a
  fixed structural witness, using its structural two-site amplitude;
- `MPSTensor.rfp_implies_nncph_of_appendixBExtraction` proves NNCPH from RFP plus that extraction,
  without calling `Axioms.rfp_to_nncph_commute`.

In other words, the internal part of the forward direction now factors as

1. obtain Appendix B structural data from `rfp_nt_structural_full`;
2. construct product-pair extraction data through that witness's two-site amplitude;
3. apply the product-pair theorem to get NNCPH.

## Gap 1 — replacing `Axioms.rfp_to_nncph_commute`

The forward direction of Theorem 3.10 is currently discharged by the sanctioned declaration
`Axioms.rfp_to_nncph_commute`.

After the wrappers and Appendix B structural data above, the missing internal theorem is more precise:

> for the structural witness produced by `AppendixBStructuralData.ofRFP`, construct an
> `AppendixBProductPairExtraction`; equivalently, construct a `ProductPairBridge A`
> (or at least `HasProductPairLocalProjectors A N` for each finite `N`).

### What is already available

- `TNLean/MPS/RFP/StructuralFull.lean` proves the full Appendix B structural form
  `rfp_nt_structural_full`.
- `TNLean/MPS/RFP/CommutingBridge.lean` now records this output as
  `AppendixBStructuralData` and names the remaining chain-space extraction as
  `AppendixBProductPairExtraction`.
- `Commuting.lean` exposes both the final wrapper `ProductPairBridge.isNNCPH` and the conditional
  theorem `rfp_implies_nncph_of_appendixBExtraction`.

### What is still missing

A theorem of the following shape is still not present:

- **target shape**: `IsRFP A` + normality (+ the normalization data needed to invoke the Appendix B
  form) `→ AppendixBProductPairExtraction (AppendixBStructuralData.ofRFP A ...)`
  (and hence `ProductPairBridge A`)

Concretely, the missing work is to turn the structural decomposition
$$A_i = X \, \Lambda \, U_i \, X^{-1}$$
into

- an explicit repeated two-site amplitude on even chains, and
- a family of chain-level projectors whose values are exactly the nearest-neighbor `localTerm`s.

This is a genuine chain-space construction problem on `NSiteSpace d N`; it is **not** a remaining
issue about the NNCPH definition itself.

## Gap 2 — the forward decorrelation theorem is blocked on tensor locality

`Decorrelation.commutingHam_isDecorrelated` proves the backward implication
(commuting parent Hamiltonian `⟹` decorrelation) in the current abstract setting.

The converse is still unavailable for a good reason: the present abstract predicate
`Decorrelation.HasCommutingParentHam` deliberately omits tensor-locality constraints. Because of
that omission, the file also contains the trivial witness
`Decorrelation.HasCommutingParentHam.ofIdem`, showing that any idempotent projector admits a formal
`HasCommutingParentHam` witness if one ignores locality.

Therefore an abstract theorem of the form

- `IsDecorrelated P_K ObsA ObsB → HasCommutingParentHam P_K`

would be mathematically vacuous on the current API.

### Exact missing infrastructure

A non-vacuous forward proof needs tensor-product locality data that the current `NSiteSpace` model
still does not expose:

1. a tensor-factor / local-support API for `H_A ⊗ H_X ⊗ H_B` inside `NSiteSpace`;
2. partial traces onto the `AX` and `XB` regions (or an equivalent support-projection API);
3. support projectors of those partial traces;
4. a refined `HasCommutingParentHam` predicate asserting that the witnesses really act on `AX` and
   `XB`, not just on the ambient space.

Only after those four pieces exist does the forward direction of Proposition D.3 become
non-vacuous.

## Practical conclusion

Issue #234 should remain open, but its remaining content is now sharply separated:

1. **internal forward direction**: replace `Axioms.rfp_to_nncph_commute` by constructing
   `ProductPairBridge A` from the Appendix B structural form;
2. **tensor-local decorrelation direction**: strengthen the decorrelation API with genuine locality
   data, then prove the forward implication.

The present Lean surface reduces the first item to a single concrete extraction problem after
`rfp_nt_structural_full`: build `AppendixBProductPairExtraction` for the structural witness, then
apply `rfp_implies_nncph_of_appendixBExtraction`.
