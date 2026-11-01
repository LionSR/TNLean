# Direct supplied-tensor finite windows

Source: CPSV17, `Papers/1703.09188/paper_v2.tex`, StandardForm/SF,
lines 603–622, and the actual finite conjugation in eq:appendix-1,
lines 2300–2306.

The existing direct-standard-form finite theorem fixed one exterior
cell to the left and allowed an arbitrary tail. The existing arbitrary
original-site prefix/suffix theorem instead requires a standard form of
`blockTwo (blockTensor U k)`. A tensor constructed directly from its
unitary gates supplies standard-form data for itself and need not have
an unblocked preimage. Applying the original-site theorem to such data
would silently insert a different blocking hypothesis.

The new module treats that directly supplied tensor W, of physical size
d*d, with arbitrary p/s W-cell buffers. It reuses the public complete
input/output three-cell-plus-tail equivalences and adds only a prefix
with product associativity and Fin.appendEquiv. Every configuration is
included. The existing buffered three-block word intertwiner supplies
the actual coefficient identity for prefix/window/suffix words, with the
periodic seam still in the trace. Finite matrix multiplication therefore
intertwines the actual input and output matrices. Actual periodic
unitarity derived from the supplied standard form gives conjugation.
The final theorem returns to the original full finite configurations.

No unblocked tensor, preimage under blocking, second blocking scale,
independently assumed local action or output support identity is added.
The standard-form datum itself remains explicit, matching the separate
scoped Blueprint entry. This module does not construct that datum or
assert the global QCA-to-MPU equivalence.

No Lean invocation, elaboration or build was run. All new entries remain
notready. Source-only validation includes pinned API scouting, generated
imports, full Blueprint synchronization/duplicate tags, role/prose checks,
formatter, width/whitespace and proof-integrity scans. Hosted checking is
required before acceptance.
