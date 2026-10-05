# PEPS ground-state diagrams: source coverage and first additions

Source: `Papers/1001.3807/paper_v3.tex`, arXiv:1001.3807v3,
*PEPS as ground states: degeneracy and topology*. Baseline: `e0f1c0bcc`.
The diagrams use the pinned Tenkz revision `08a6493f`.

## Source inventory

The local source contains 116 image inclusions using 110 distinct image paths.
These counts describe source artwork, not independent mathematical results.
Some equalities contain several included images; conversely, a single image
may contain several contraction steps.

| Source section | Source lines | Image inclusions | Distinct images |
| --- | --- | ---: | ---: |
| MPS and PEPS | 423–602 | 7 | 7 |
| Injective MPS | 603–831 | 15 | 13 |
| G-injective MPS | 832–1268 | 17 | 17 |
| G-injective PEPS | 1269–1665 | 25 | 21 |
| Isometric PEPS, including excitations | 1666–2611 | 37 | 37 |
| Examples | 2612–3019 | 15 | 15 |

The baseline has native Tenkz pictures in 16 of the 249 `ch24_peps*.tex`
files. Most belong to the separate PEPS Fundamental Theorem development,
so counting these as coverage of this paper would be misleading.
The quantum-double chapter already draws regular two-tensor contraction
and the two-cycle torus closure. It does not reproduce all 110 source images.

## Added equations

Each picture is written beside its mathematical statement or proof, with
adjacent comments specifying source passage, index interpretation,
contractions, and open boundary. A bundled virtual index is explicitly
identified as a bundle; it is not presented as one microscopic lattice bond.

| Blueprint file and entry | Equation | Open virtual/physical indices per panel |
| --- | --- | --- |
| `ch24_peps_examples.tex`, `def:peps_g_injective` | Four-leg virtual invariance from `figs3/ug-sym` | (4,1), (4,1) |
| `ch24_peps_g_injective_strip_intersection.tex`, `thm:peps_g_injective_strip_intersection` | `tr(ABM)=tr(NBC)=tr(ABCX)`, inhomogeneous version of `figs2/trAAM`, `trNAA`, `trAAA` | (0,3), (0,3), (0,3) |
| `ch24_peps_g_injective_range_equivalence.tex`, `thm:peps_g_injective_invariants_range` | `T P_G = T` | (1,1), (1,1) |
| `ch24_peps_g_injective_cut_range.tex`, `thm:peps_regular_ginjective_cut_range` | `C = T Sᵀ` and `C Lᵀ = T` | (0,2), (0,2); (1,1), (1,1) |
| `ch24_peps_semiregular_bond_isometry.tex`, `def:peps_multiplicity_bond_map` | `J(X_i)_(k,a),(l,b) = m_i^(-1/2) (X_i)_(k,l) δ_(a,b)` | (4,0), (4,0) |

The cut diagrams depict the already-proved matrix equalities, not the full
lattice manipulation in Theorem 6.9. The multiplicity diagram is the bond
map from the end of Section 7; it does not claim the complete PEPS equivalence
from this local isometry alone. The symmetry diagram explicitly assumes a
factorized four-leg action and allows contragredient factors. All physical
indices in the strip and symmetry pictures remain visible.

No Lean declarations, hypotheses, proof-status markers, or declaration links
are changed by this batch.

## Remaining source figure families

The following need separate source-to-theorem checks and diagrams; they are
not covered by the six added equations.

- **PEPS concatenation and intersection:** `figs3/c-eq-ab`, `ab-inv`,
  `apply-ab-linv`, `grow-N`, `grow-M`, `grow-intersect`, `prove-grow`.
  The existing two-site contraction picture does not show the averaged inverse
  or the entire overlapping-region argument.
- **Torus closure and degeneracy:** the `figs3/close-*` family,
  `closure-inv`, `boundary-lin-indep`, and `move-strings-*`.
  The existing closed 2-by-2 network shows the inserted group elements but
  not every change of cut or simultaneous-conjugacy argument.
- **Accessible virtual systems and renormalization:** `figs4/phys-op-*`,
  `virt-op-from-phys`, `iso-accessbonds*`, and `renorm-*`.
  The projected physical and virtual spaces must be distinguished in each
  identity; drawing an unrestricted inverse would change the mathematics.
- **Entropy and commuting parent terms:** `figs4/blockentropy-*`,
  `ham-proj-*`, and `ham-comm-*`. Keep the simple-connectedness and regular
  representation hypotheses, and distinguish normalized reduced densities
  from unnormalized contraction matrices.
- **Flux and charge excitations:** the `figs5` family. Match endpoint group
  labels, string orientation, conjugation, and the particular physical
  transport theorem before drawing a deformation or braiding equality.
- **Toric-code and quantum-double examples:** `figs6/tc-*`, `proj-as-peps`,
  `kitaev-as-twirl`, `double-as-twirl`, and `double-with-V-Theta`.
  The new multiplicity picture covers only the final bond transformation.

## Validation

- `scripts/test_tenkz_peps_groundstate.py`: all six source equations render;
  all 13 panels have the exact typed open-boundary counts above.
- `scripts/tenkz_blueprint_sweep.py` on the six changed equation units:
  13 pictures, zero hard findings, zero advisories.
- `scripts/test_tenkz_pic.py`: SVG ink, cache reuse, and single-edit
  invalidation checks pass.
- `scripts/test_tenkz_blueprint_sweep.py`: equation-unit extraction passes.
- `scripts/check_tenkz_demolition.py` and `git diff --check`: pass.
- A four-page contextual PDF compiled with the blueprint print preamble;
  all pages and a one-page diagram sheet were visually inspected. No
  overfull boxes were reported.
- Full declaration synchronization was attempted. It reports 523 missing
  references with the QICLean dependency absent in this isolated worktree;
  no declaration links were added or removed here. This is not a successful
  full `checkdecls` or Lean build.

The web-compatible `tenkzequation` environment is presentational: the general
sweep compares its equation boundaries only at advisory severity. The new
regression therefore asserts each exact boundary explicitly and fails on a
mismatch. This does not claim that the global equation-scope migration is done.
