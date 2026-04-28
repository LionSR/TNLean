# 2026-04-28 — Issue #982 FT-based symmetry triage

Issue #982 asks that symmetry be proved by the Fundamental Theorem rather than
by the string-order development or the periodic-FT track.  I checked the current
Lean files, blueprint, issue threads, and the relevant paper passages.

## Existing injective theorem path

The injective case is already on the Fundamental-Theorem route.

* `MPSTensor.gaugeEquiv_twistedTensor_of_injective` in
  `TNLean/MPS/Symmetry/Defs.lean` proves, for every group element `g`,
  `GaugeEquiv A (twistedTensor A U g)` from injectivity and on-site symmetry.
  Its proof is exactly
  `(sameMPV_iff_gaugeEquiv_of_injective hA).1 (hSymm g)`.
* `MPSTensor.sameMPV_iff_gaugeEquiv_of_injective` in
  `TNLean/MPS/FundamentalTheorem/Basic.lean` is the wrapper around
  `MPSTensor.fundamentalTheorem_singleBlock`.
* `MPSTensor.virtual_rep_of_symmetric_injective` in
  `TNLean/MPS/Symmetry/VirtualRepresentation.lean` chooses those gauges and uses
  gauge uniqueness plus `MPSTensor.twistedTensor_mul` to package them as a
  bond-space projective representation.
* `MPSTensor.hasStringOrder_of_symmetric_injective` in
  `TNLean/MPS/Symmetry/StringOrder.lean` consumes
  `virtual_rep_of_symmetric_injective` later.  It is downstream of the FT-based
  virtual representation theorem, not the proof of that theorem.

The blueprint now says this explicitly in
`blueprint/src/chapter/ch13b_symmetry.tex`, in the proof of
`lem:gauge_equiv_twisted` and the new remark
`rem:injective_symmetry_ft_route`.

## Paper passages checked

* `Papers/2011.12127/TN-Review-main.tex` lines 1084--1090 state the injective
  symmetry route: equality of normal MPS implies a gauge, and applying a global
  on-site symmetry gives
  `\sum_j U_{ij}(g) A^j = e^{i\phi(g)} X^\dagger(g) A^i X(g)`.
* The same file at lines 1103--1105 records the projective law
  `X_g X_h = e^{i\omega(g,h)} X_{gh}` for virtual symmetries.
* Lines 1743--1744 say the Fundamental Theorem is the basic tool for phase
  classification under symmetries, with `B^i = \sum u_{ij} A^j`.
* Lines 1896--1900 give the equal-MPV Fundamental Theorem corollary: in
  canonical form, equal MPV families imply a global gauge.
* `Papers/0802.0447/StringOrder-v10.tex` lines 306--311 prove the separate
  string-order/local-symmetry criterion for pure FCS.  That is a detection and
  rigidity result, not the shortest route to the virtual gauge in the injective
  case.
* `Papers/quant-ph_0608197/MPSarchive.tex` lines 742--763 give the TI canonical
  form, lines 849--879 give the periodic sector decomposition, and lines
  1002--1014 state canonical-form uniqueness.
* `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 187--190 recall gauge
  equivalence as the basic same-MPV mechanism, lines 227--231 explain blocking
  by common periods, and lines 271--301 give the BNT expansion used by the
  non-injective canonical-form route.

## Issue-thread context

* #982 itself has only the title/body request and no comments.
* #652 is the non-periodic canonical-form umbrella.  The current thread no
  longer asks for a direct same-norm shortcut; it has been refined to the
  sector-level route through common live blocks, BNT sector comparison, zero-tail
  bookkeeping, and finite-length span equality.
* #942 remains open as the broad common-live-block tracker, but its thread now
  points to the more precise common blocking work in #969.
* #944 is the BNT representative overlap/span tracker.  PR #955 supplied the
  one-sided overlap data; PR #960 transported representative spans; PR #976
  added the common-phase-cover span adapter.  The remaining input is deriving
  the common live family and phase-cover maps from the structural reduction.
* #969 is the live common-blocking issue.  PR #975 introduced the common
  cyclic-sector family; PR #981 supplied the iterated-blocking relabeling.  The
  thread still records the remaining flattening, zero-tail transport, and later
  injectivity/Wielandt blocking obligations.
* #970 is the live-block span-equality issue.  PR #976 supplied
  `MPSTensor.mpv_span_eq_of_common_phase_cover`, so the remaining span step is
  to construct the common live family and surjective phase-cover maps.
* #840 states the current global priority: parent Hamiltonians and
  canonical-form reduction.  Its canonical-form ranking is #942/#944, now
  refined by #969/#970.
* #924 says to clean up the full canonical-form reduction without using the
  periodic track; #932 asks issue/PR reports to cite LaTeX line numbers and
  quote the relevant source.  This audit follows that convention.
* Open symmetry-labelled issues #619, #622, #664, and #829 belong to the
  periodic-FT track.  They are useful background for periodic symmetry results,
  but they should not be the main route for #982.
* #335 and #330 record that the injective symmetry/SPT blueprint chapter now
  exists and includes string order.  This supports the conclusion above: string
  order is present as a later consequence/detection theory, while the virtual
  gauge for injective symmetric MPS comes from the Fundamental Theorem.

## Remaining non-injective/multi-block route

For a non-injective tensor `A`, the corresponding symmetry theorem should compare
`A` with `twistedTensor A U g` using the non-periodic equal-case FT after the
canonical-form reduction is completed.  The expected route is:

1. use on-site symmetry to get `SameMPV₂ A (twistedTensor A U g)`;
2. apply the after-blocking/canonical-sector equal-case theorem once #969,
   #970, and #944 discharge the remaining common-live, zero-tail, injectivity,
   and span inputs;
3. package the resulting sector-level virtual data into a permutation/phase
   action on canonical sectors, and then into projective data on each invariant
   sector when the relevant stabilizer action is fixed.

No new follow-up issue is needed yet: #969, #970, #944, and the umbrella #652
already track the prerequisites.  A separate symmetry packaging issue would be
appropriate only after those FT inputs expose the sector-level comparison as a
public theorem.
