# Explicit local quantum-double Hamiltonian terms

Date: 2026-10-05. Source baseline: `75c609dea22e633770ed1ea9609e985b282550a8`.

## Source evidence and exact scope

The source is SCP10, `Papers/1001.3807/paper_v3.tex`, lines 2832–2940:

- 2832–2840 describes the local, four-block plaquette and two-block bond terms in the binary case.
- 2861–2877 gives the general-group product-one constraint, the left/right physical action and the printed unnormalized group sum.
- 2896–2908 prescribes clockwise rotation and the exact blocked tensor `K(p,q,r,s) = (p q⁻¹, q r⁻¹, r s⁻¹, s p⁻¹)`.
- 2914–2923 interprets virtual bond colors and lists the three blocked Hamiltonian families.

`figs6/tc-lattice.pdf` and `figs6/tc-blocked-lattice.pdf` were rasterized and inspected. They establish only the checkerboard incidence, blocking and shared bonds used here. The physical arrow and nonabelian multiplication convention is fixed separately by Equation (7.10) and its clockwise footnote, source lines 2896–2908. No literal arrow-by-arrow agreement with the earlier checkerboard figures is asserted or used in the proofs. The missing `renorm-as-diff-doubles` artwork was not reconstructed or claimed as evidence. All local position and multiplication conventions are stated explicitly in the new fragment.

This checkpoint concerns exact physical operators and actual finite open contractions for an arbitrary finite group, with the entire four-spin or sixteen-spin ambient physical space retained. It does not establish the full-lattice common kernel, all placed-term commutators, or the unblocked arbitrary-group physical renormalization.

The two-block statement is a genuine range equality as well: the actual two-tensor contraction image equals the range of the product of the normalized bond average and the two local flatness projectors. The reverse inclusion uses explicit boundary colors for every allowed physical pair. The hole projector commutes with the northern coherent bond action because its ordered holonomy transforms by conjugation, not because nonabelian holonomy is pointwise invariant.

## Normalization correction

If `V_u V_v = V_(uv)`, then `S = Σu V_u` satisfies `S² = |G| S`. The printed `1 − S` does not annihilate invariant vectors for a nontrivial group. The corrected constraint projector is `A = |G|⁻¹ Σu V_u`, and the Hamiltonian term is `1 − A`. This correction is distinct from normalization of the unnormalized blocked tensor `K`.

The companion note is [`scp10_quantum_double_local_hamiltonian.tex`](../paper-gaps/scp10_quantum_double_local_hamiltonian.tex). It records the exact correction and outstanding global obligations.

## Diagram contracts

The fragment is [`ch24_peps_quantum_double_local_terms.tex`](../../blueprint/src/chapter/ch24_peps_quantum_double_local_terms.tex). Its three native Tenkz diagrams depict:

1. One `K` tensor. Virtual north/east/south/west are `p,q,r,s`; physical northeast/southeast/southwest/northwest are `a,b,c,d`. All eight legs are open. Signature: `(4 virtual, 4 physical)`, with alphabet `G` on each leg.
2. The actual east–west two-block contraction. The sole internal wire is `q(left) = s(right) = x`, summed exactly once. Six external colors remain free; two physical wires each carry a full `G⁴` tuple. Signature: `(6 virtual, 2 physical)`.
3. The actual four-block hole contraction. The internal matches are `NW.E = NE.W = x`, `NW.S = SW.N = y`, `SW.E = SE.W = z`, `NE.S = SE.N = w`. Eight exterior colors are free; four physical wires each carry a full `G⁴` tuple. Signature: `(8 virtual, 4 physical)`. The ordered selected spins are `NW.b, SW.a, SE.d, NE.c`, which telescope as `x y⁻¹, y z⁻¹, z w⁻¹, w x⁻¹`.

The diagrams contain no undocumented scalar, no omitted physical registers, and no arbitrary reassignment of nonabelian multiplication order. Comments adjacent to each picture record its formula, incidence map, contractions and boundary signature.

## Declarations and validation

The fragment has 70 unique declaration tags. Key conclusions are:

- `range_siteMap_quantumDoubleKTensor` and `range_siteMap_quantumDoubleKTensor_eq_ker_localTerm`: the genuine one-block image is both the product-one projector range and the explicit local zero-energy kernel.
- `quantumDoubleKBondAverage_isStarProjection`, `quantumDoubleKBondAverage_mulVec_eq_self_iff`, and `quantumDoubleKBondAverage_contraction`: normalized averaging, its exact invariant-space condition, and invariance of the actual contracted columns.
- `range_quantumDoubleKBondContraction` and `mem_range_quantumDoubleKBondContraction_iff`: the full two-block image equals the independently defined constraint-projector range, equivalently simultaneous local flatness and coherent bond invariance.
- `quantumDoubleKPlaquetteProjector_contraction`: the full sixteen-spin plaquette projector fixes the actual four-tensor contraction.
- `quantumDoubleKPlaquetteHolonomy_topBond` and `quantumDoubleKPlaquetteProjector_commute_topBondAverage`: the exact nonabelian conjugation law and the resulting full-ambient commutation.

All names have namespace `TNLean.PEPS`. The comparison `quantumDoubleDualToK_spins` is only a physical relabelling between two blocked conventions; it is not the unblocked renormalization.

The four production modules passed a targeted strict rebuild with zero warnings:

- `QuantumDoubleLocalConstraint`: 2.52 seconds.
- `QuantumDoubleBondAverage`: 3.12 seconds.
- `QuantumDoubleBondParent`: 2.90 seconds.
- `QuantumDoublePlaquetteConstraint`: 6.97 seconds.

The audit of axioms for all 70 named production definitions, theorems and abbreviations found only `propext`, `Classical.choice` and `Quot.sound`. The frozen test source, `TNLeanTest/QuantumDoublePhysicalTerms.lean`, has SHA-256 `34cdec122e2afc43591ef754dd61067143a6feedfffe536b1e0ad5324514ef48` and 12 guarded checks of axioms. These are targeted Lean-build receipts; the diagram and declaration-name checks do not replace elaboration.

The new focused regression is runnable from the repository root:

```sh
python3 scripts/test_tenkz_quantum_double_local_terms.py --no-render
python3 scripts/test_tenkz_quantum_double_local_terms.py --output-dir /tmp/qd-local-review
```

With pinned Tenkz `08a6493f3605dcf2ca5b512823ccb2698dfc027b`, XeLaTeX and pdftoppm, it verifies:

- all three pictures independently and together with the actual print preamble;
- exact glyphs, typed ports, wire incidences, external tuple labels, and emitted signatures `(4,4)`, `(6,2)` and `(8,4)`;
- source existence, unique ownership and complete reverse coverage of all 70 declarations in the four production modules, without claiming to replace Lean elaboration or the full blueprint declaration checker;
- seven rejected mutations covering shared incidences, physical/virtual type, shared-color label, hole product order, omitted normalization and wrong-sided physical multiplication;
- an exact nonabelian `S₃` fixture for local image equality, one- and two-block explicit preimages, group-action order, actual shared-color contraction invariance, four-block hole flatness, and the conjugation law on arbitrary, including non-flat, selected spins;
- no Tenkz topology, bounding-box, overlap or equation audit findings;
- no unresolved references or overfull boxes in the two-pass combined render.

The normalization/scope note also compiles in two pdflatex passes without warnings or overfull boxes. Individual diagram PNGs, the combined mathematical pages and the note were visually inspected. Python syntax and focused whitespace checks pass; the blueprint fragment is formatted with pinned latexindent 3.24.7.

This is focused validation of standalone new material. No whole-book web/PDF build or whole-book `checkdecls` is claimed. No router, import aggregate or existing source cache was changed.
