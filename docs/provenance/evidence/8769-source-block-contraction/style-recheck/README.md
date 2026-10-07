# Source-block comment correction

The source at `b4255389867855a1d06df5247542da6eec19ef66` removes one trailing space from a provenance
comment in `SourceBlockMatrix.lean`. The mathematical declarations are unchanged.
The seven public declarations of that module were recompiled with package options
and warnings as errors, then imported for a fresh axiom audit. All reports use only
Lean's standard axioms. The audit records 4347 imported artifact hashes.
The rebuilt artifact was written to a new temporary directory; earlier proof
artifacts and their historical evidence were preserved.

The corresponding seven provenance entries now cite this exact source revision.
The remaining fourteen entries and the earlier blueprint and regression records
retain their original, explicitly recorded revisions. The original build evidence
remains a historical record and is superseded for the seven affected entries by
the commands in this directory. This was a direct Lean check, not a Lake build.
