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
`TNLean.MPS.BlockingPeriodicityCFII_viaAdjoint` rather than the old
unital-and-trace-preserving formulations.
