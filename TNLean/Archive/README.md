# TNLean Archive

This directory contains retired and documentary Lean files.

- **CFII** means **"Canonical Form II"**, i.e. the **IrreducibleFormII** gauge coming from arXiv:1606.00608.
- The files in this directory are retained for reference, historical context, and checked alternate routes.
- They are **not** part of the active TNLean library surface.
- They are excluded from the root `TNLean.lean` import list.

The old public modules at the former paths have been removed as part of the
post-reorganization cleanup.  The archived bi-canonical periodicity
reformulations were also removed: code should use the current
positive-fixed-point peripheral theorem and
`TNLean.MPS.Transfer.Irreducible.BlockingViaAdjoint` rather than the old
unital-and-trace-preserving formulations.

## Place in the layers

The archive belongs to no layer of `docs/library_layers.md`. Its modules may
import production modules (they import `MPS/Tensor`, `MPS/Transfer` and
`MPS/Operator` modules, QICLean and Mathlib), and no production module may
import an archive module. The import, small-module and pass-through checks
skip this directory; CI builds a changed archive module explicitly.
