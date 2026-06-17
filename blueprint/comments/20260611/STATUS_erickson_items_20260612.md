# Status of Erickson's chapter-12 string-order/SPT comments (addressed 2026-06-12)

The report `chapter12_spt_string_order_report.md` (against `blueprint-v6.pdf`)
reviews the compiled chapter 12, "Symmetries and String Order"
(`blueprint/src/chapter/ch13b_symmetry.tex`). Its numbered items resolve to:
Definition 12.60 = `def:is_same_spt_phase`, Theorem 12.61 =
`thm:has_string_order_of_symmetric_injective`, Theorem 12.62 = the theorem
renamed below, Section 12.6 = the retitled SPT section.

Every impactful claim was verified against the Lean source and the local
source paper `Papers/0802.0447/StringOrder-v10.tex` before acting (PR #2663).
One framing correction resulted; see item 2.

## Item-by-item resolution

| # | Erickson's point (report section) | Status | Where |
|---|---|---|---|
| 1 | The cocycle-extraction backbone (virtual gauge, projective representation, cocycle, coboundary freedom) is correct (§1). | **Confirmed; no change needed.** The chain from on-site symmetry to the virtual projective representation, the 2-cocycle identity, and gauge independence of the class is intact and `\leanok`. | ch13b `thm:virtual_rep_injective`, `cor:virtual_rep_cocycle`, `thm:cocycle_gauge_independence` |
| 2 | The chapter's string order is a broad boundary-witness notion and must be explicitly distinguished from the paper's "fixed physical endpoint" string order (§3). | **Addressed, with corrected framing.** The distinction is real and is now stated, but the source's own definition is *already existential* over the endpoint operators and the twist (display `SOP`, lines 112–122), so the contrast is *physical versus virtual* endpoints, not existential versus fixed-endpoint. The source itself notes that a particular endpoint choice can vanish while the symmetry persists; that caveat is now quoted in the chapter. Verification also surfaced two deviations the report missed: positive limit versus uniform all-length lower bound, and adjoint-channel versus multiplicative left boundary. The faithful physical-endpoint formalization is tracked separately. | ch13b `def:string_order_boundary_param`, `def:has_string_order`; scope marker on the string-order predicate; `docs/paper-gaps/pgwsvc08_string_order_virtual_boundary.tex`; issue #2660 |
| 3 | Theorem 12.61 should be read as symmetry detection (peripheral eigenvalue / virtual implementability), not as a physically robust phase-distinguishing order parameter (§4). | **Addressed.** A new remark states that the universality theorem holds irrespective of the cocycle class, that string-order existence is equivalent to local symmetry, and that the separating invariant is the cocycle class. | ch13b `rem:string_order_symmetry_diagnostic` |
| 4 | Theorem 12.62 ("String order is an SPT invariant") is misleading: its proof only uses 12.61 and never the cocycle data (§5). | **Confirmed and addressed.** Verified in Lean: the proof discharges both directions by the universality theorem and takes no same-phase hypothesis. Retitled "String order existence agrees for any two injective symmetric tensors"; the Lean theorem renamed `stringOrder_invariant_of_samePhase` → `hasStringOrder_iff_of_symmetric_injective` (no deprecated alias: the old name encoded a hypothesis the theorem does not have); statement-level `\uses` corrected; the proof is now literally `iff_of_true` of two universality instances. | ch13b `thm:has_string_order_iff_of_symmetric_injective`; `TNLean/MPS/Symmetry/StringOrder.lean` |
| 5 | Existence of string order is not equivalent to (nontrivial) SPT order; the invariant is the cocycle class (§6). | **Addressed.** Stated in the section preamble and in the new remark; the commutator-phase test (already formalized) remains the computable non-triviality criterion. | ch13b §12.6 preamble, `rem:string_order_symmetry_diagnostic`, `thm:nontrivial_of_comm_phase` |
| 6 | Add an explicitly external classification theorem (Chen–Gu–Wen; Schuch–Pérez-García–Cirac) after Definition 12.60 (§§7–8, 10). | **Addressed as a remark.** House style states external, unformalized results in remark environments without `\lean`/`\leanok` (model: ch11b `rem:cor_4_1_projective_rep_spt`); a theorem environment would add an unproven node. The remark states both directions of the classification, cites `ChenGuWen2011` (arXiv:1008.3745) and `Schuch2011Phases` Section II.F (arXiv:1010.3732; both keys already in `references.bib`), and says explicitly that Definition 12.60 takes cohomologous cocycles as the *definition* of phase equality. | ch13b `rem:spt_classification_not_formalized` |
| 7 | The chapter is missing both halves of the true classification proof: gapped-path invariance and completeness (§9). | **Acknowledged; out of scope.** Requires infrastructure absent from the repository (paths of tensors/Hamiltonians, gap along a path, symmetric local unitaries). Tracked as a long-term item. | issue #2661 |
| 8 | Rename Section 12.6 and retitle/restate Theorem 12.62 (§10). | **Adopted in adapted form.** Section retitled "SPT Phase Labels and String-Order Universality" (content-descriptive variant of the report's suggestions). The report's replacement Proposition (spectral radius one / virtual implementability) was *not* adopted as the 12.62 statement: those facts are already separate formalized theorems, and the existing Lean statement of 12.62 is exactly the universality iff, now titled truthfully. | ch13b §12.6, `thm:twisted_transfer_spectral_radius_le_one`, `thm:local_symmetry_iff_spectral_radius` |
| 9 | Recommended diagnosis sentence (§11). | **Reflected.** The section preamble and the two remarks carry its content: extraction is formalized, the string-order theorem holds in the virtual-boundary reading, classification is external, the invariant is the cocycle class. | ch13b §12.6 |

Not adopted: a blueprint citation of Pollmann–Turner (arXiv:1204.0704, refined
selection rules diagnosing the class) — no entry in the blueprint bibliography
and not needed for the corrected statements; it is referenced in issue #2661.

## Summary

The report's substantive complaints are confirmed by direct verification and
are implemented: the SPT section no longer presents string-order existence as
a classifying invariant, the classification theorem is stated as external with
precise citations, and the virtual-boundary reformulation of the string-order
definition is documented against the source with a paper-gap note and an
elimination plan (issue #2660). The one place the report's framing was
inaccurate — the source's string order is itself an existence statement over
physical endpoints, not a fixed-endpoint Haldane parameter — is corrected in
the new prose, which follows the source. The missing classification halves are
tracked in issue #2661.
