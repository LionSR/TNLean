# Finite rectangular bulk checkpoint — Lean verification blocked

Base: `f8ebaf5180d79443e38644adaa176cd452a24aa8` (published #8707 integration).
Branch: `codex/scp10-finite-bulk`.

This is an **unverified source checkpoint**, not a completed formalization.
No Lean elaboration or axiom audit of the new declarations has succeeded.
The blueprint entry is `notready`, with no new `leanok` claims.

## Candidate mathematics

`TorusDualRectangle.lean` constructs a bottom-row/column comb. It contains
prefix cancellation, reverse-edge cancellation, the column/east square exchange,
four-direction comb-edge identities, arbitrary labelled path induction, and
homotopy of paths with the same lifted endpoints. The steps have explicit
rectangle bounds and preserve east/west/north/south labels. Period bounds make
the projection injective on the closed lifted rectangle. The intermediate
projection theorem is stronger: it does not require injectivity, because it
compares paths with the same lifted endpoints even when the image wraps.

`TorusDualRectangleFlux.lean` applies the existing arbitrary-exterior-matrix
contraction theorem to this derived homotopy. No homotopy, gauge, crossing-count
equality, flatness, or abelian-group assumption is a hypothesis of the new
geometric conclusion. The tensor hypothesis is virtual invariance at the swept
primal sites. The original unrestricted source gap is retained; this does not
prove arbitrary-region avoidance, vacuum reduced-density equality, or equality
between winding classes.

Source inspected: `Papers/1001.3807/paper_v3.tex`, lines 2181–2214, particularly
the deformation lemma and its invariance argument at lines 2199–2214.
The old unpublished `791f42a4` packet was not accessed or used.

## Local environment and exact blocker

- Installed the exact Lean 4.35.0-rc3 Linux release under
  `/workspace/tooling/lean-4.35.0-rc3-linux`; `lean-toolchain` unchanged.
- Dependency sources fetched from the existing manifest, without `lake update`.
- Mathlib source pin: `c55e6e786f49471c72fbddbec5415808896aec1e`.
- After advancing to the current integration, QICLean source was checked out
  at `8d5389d23c8e675a0117442e1a0d2c683a4bad41`, exactly matching the new manifest.
- `lake exe cache get` built only the cache utility, not Mathlib theorem modules.
- First cache invocation hit read-only `/home/agent/.cache/mathlib`; setting
  `MATHLIB_CACHE_DIR=/workspace/tooling/mathlib-cache` resolved that path error.
- The corrected command failed with `CONNECT tunnel failed, response 403` at
  `https://cache.mathlib.org/mathlib4-master/f/<hash>.ltar`. The Azure endpoint
  `https://lakecache.blob.core.windows.net/mathlib4-master/f/<hash>.ltar` also
  returned 403, including an escalated network probe. No approval rejection
  occurred; the network proxy itself refused the destination.
- Mathlib's prebuilt `.olean` files and all TNLean prerequisite artifacts remain
  absent. A direct strict-option elaboration attempt stops at the first import:
  `unknown module prefix 'TNLean'`. It does not reach the new proof bodies.
- No Mathlib source rebuild, stale artifact substitution, or dependency update
  was attempted. Interrupted the futile cache downloader after diagnosing 403.

Smallest recovery: allow the official pinned cache endpoint, or transfer its
matching prebuilt artifacts. Exact-head PR CI can instead elaborate the files
using the normal cache setup. Strict regressions have been added to the existing
PEPS regression loop. Axiom output must still be inspected for the new geometry
and its actual-contraction corollary; no axiom result is claimed here.

## Checks completed

- `python3 scripts/test_tenkz_dual_rectangle.py`: PASS with pinned Tenkz
  `08a6493f3605dcf2ca5b512823ccb2698dfc027b` and XeLaTeX.
- Checked both directed routes, their lifted endpoints, and the two swept
  primal-site centers; rejected four mutations (wrong corner, duplicate name,
  wrong stroke, wrong swept center).
- Eight Tenkz event-stream audits passed: empty pictures, dialects, crossings,
  kernel checks, bounding boxes, label overlaps, equation groups and boundaries.
- Geometry-only dotted routes have no tensor indices or physical legs.
  The figure illustrates only `N,N,E ~ E,N,N`, not the entire path-induction
  theorem and not a density-matrix assertion.
- `git diff --check`: PASS.
- `python3 scripts/tactic_pattern_scan.py`: ran. The new proofs share a single
  composition pattern within this one module; no cross-file promotion is due.
- Source scan: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafeCast` or
  `unsafeCoerce` declarations in the new production modules. This syntactic
  scan is not a substitute for compilation or `#print axioms`.

The other-dot GLM23 and MPU-gauging modules were not edited.
