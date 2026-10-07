# Regular PEPS reblocking diagrams

Date: 2026-10-05.

## Source and mathematical scope

The coefficient-level redraws accompany Observations 6.5–6.6 of
[arXiv:1001.3807v3](https://arxiv.org/abs/1001.3807v3). The exact local source
is [paper_v3.tex, lines 1830–1909](../../Papers/1001.3807/paper_v3.tex#L1830-L1909).
All three original figures were rasterized and inspected:

- [renorm-gg-sym.pdf](../../Papers/1001.3807/figs4/renorm-gg-sym.pdf)
- [renorm-g-id-and-split.pdf](../../Papers/1001.3807/figs4/renorm-g-id-and-split.pdf)
- [renorm-fixedpoint.pdf](../../Papers/1001.3807/figs4/renorm-fixedpoint.pdf)

The diagrams retain the distinction between three statements:

1. Literal four-site contraction and periodic physical regrouping have
   scalar factor one, for arbitrary tensors and all positive coarse periods.
2. The regular four-site Gram operator has factor
   `c_B = |G| ∏ c_i`. The extra group order is from the internal cycle with
   unnormalized bonds, not from geometric regrouping.
3. For a homogeneous regular G-isometric tensor and untwisted coarse torus
   periods at least three, a product of block-local physical maps, with input
   and output regrouping, is an isometry on the derived physical support.
   It maps the actual fine state to the **same original** coarse tensor state
   times the normalized Bell product, with the stated positive scale.
   Normalization removes that scale. No ambient-unitary extension, twisted
   closure theorem, or small-period Bell-separation theorem is asserted.

The relative coordinate is `a⁻¹b`, with that order. Thus the drawings apply
to every finite group, including nonabelian groups. Surplus endpoint physical
registers remain distinct; none are silently summed away.

## Four displays and their incidence checks

The new fragment is
[`ch24_peps_regular_reblocking_diagrams.tex`](../../blueprint/src/chapter/ch24_peps_regular_reblocking_diagrams.tex).
It owns no theorem declarations.

- The literal block has corners 0, 1, 2, 3 clockwise from the upper right.
  Its four named internal bonds reproduce all four `lambda_i` leg lists in
  the geometric contraction. Eight separately labelled boundary indices and
  four physical outputs give signature **(8 virtual, 4 physical)**.
- The two-bond display fixes the common regular matrix from the neighboring
  averages and groups the other incident indices outside the drawing.
  Relative coordinates turn two copies of `L_q` into `L_q` and two identity
  tensors joined by a single virtual bond. Both panels have signature
  **(0, 4)**. The joined identities have coefficients `delta_(r,s)`, equal
  to `sqrt |G|` times a normalized Bell vector, rather than a unit-normalized
  pair without its scalar.
- The local target in relative boundary coordinates is the original `A`
  tensor and four independent identity tensors. It has eight virtual
  inputs and five physical outputs, signature **(8, 5)**. It is not equated
  directly with the four-physical-output block: the stated support map and
  positive ratio of site factors intervene.
- The normalized global identity contracts the full fine physical register
  into the support isometry. Its two output registers are the complete
  original coarse and surplus configurations. Both panels have signature
  **(0, 2)**. State boxes have no open virtual boundary; the coarse box and
  the Bell box are disconnected tensor factors.

The matrix and state diagrams are coefficient-level versions of the source,
not facsimiles of its hidden group sums or its ambient-unitary wording.
The source-to-index comments explain every aggregation and normalization.

## Reproducible checks

With XeLaTeX and the checkout pinned by `tenkz.toml` available:

```sh
python3 scripts/test_tenkz_peps_regular_reblocking.py
# Retain PDFs, page PNGs and event logs for inspection:
python3 scripts/test_tenkz_peps_regular_reblocking.py --output-dir /tmp/reblocking-review
```

The script uses `TENKZ_ROOT` or the ordinary `.deps/tenkz` lookup. It never
runs Git or depends on a local commit object, and therefore also works in
shallow or exported checkouts with the source inputs present. Temporary
rendering does not populate the repository image cache.

Checks passed:

- Four individual source displays, six panels total, and a combined
  three-page document using the real print preamble.
- Exact source corner/boundary incidences, local equality-pair contraction,
  original-tensor identity factors, and normalized state connection.
- All six typed boundary signatures, with no kernel errors.
- Tenkz checks for empty pictures, dialects, crossings, kernel diagnostics,
  bounding boxes, label overlaps, equation groups and equation boundaries.
  No findings and no overfull boxes.
- Seven malformed source variants rejected: wrong internal incidence,
  swapped exterior label, mistyped physical leg, wrong Bell endpoint,
  replacement of the original local tensor, replacement of the original
  coarse state, and reversed nonabelian relative-coordinate order.
- Python byte compilation and pinned latexindent 3.24.7 formatting with a
  second-pass idempotence check.
- All four individual images and all combined pages inspected against the
  source figures. Page breaks preserve every complete network.

The isolated combined fixture does not load theorem owners or the bibliography,
so cross-fragment references and citations need the ordinary integrated
blueprint build. These diagram checks do not claim a full blueprint build,
Lean elaboration, or repository-wide CI. ChkTeX was not available in the task
environment. The new fragment uses explicit incidence coordinates, with no
`lattice={2x2}` DSL token requiring a warning-29 suppression.

No routers, imports, workflows, existing proof files, source-paper files or
shared diagram macros were changed by this task.
