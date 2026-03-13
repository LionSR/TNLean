# TNLean Archive

This directory contains retired and documentary Lean files.

- **CFII** means **"Canonical Form II"**, i.e. the **IrreducibleFormII** gauge coming from arXiv:1606.00608.
- The files in this directory are retained for reference, historical context, and checked alternate routes.
- They are **not** part of the active TNLean library surface.
- They are excluded from the root `TNLean.lean` import list.

The compatibility shims at the old module paths have been removed as part of the post-reorganization cleanup. Code that previously imported `TNLean.Channel.PeripheralClosure`, `TNLean.MPS.BlockingPeriodicity`, or `TNLean.MPS.BlockingPeriodicityCFII2` should be updated to use the new `TNLean.Archive.*` paths or the current active modules.
