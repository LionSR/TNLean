# Verification of the entropy and radius estimates

The production sources are frozen at `548f23f7b274af443eb3644d8153f15148565c31`. All six files below were checked byte for byte against that revision. The audit sources have only documentation changes after that revision.

The guarded three-module build exited successfully. The shared build log is `build.log`; the radius kernel report is in the neighbouring `8757-radius-scales` directory. Both strict read-only audit commands exited with code zero. Every one of the seven declarations depends only on `propext`, `Classical.choice`, and `Quot.sound`. Exact commands and log hashes appear in the two provenance shards.

`kernel_lock_run.py` preserves the lock runner used by the recorded build command. It acquires the canonical repository lock before invoking this worktree's build wrapper. The prebuilt Mathlib cache was present; QICLean dependencies were built from source after their release-artifact download was unavailable.

The current provenance policy, frozen at revision `806099b4dddcce591b3a62ee1921926a6af5ad55`, validates all seven entries in these two shards. `provenance.log` records the policy and schema hashes. This validation checks the immutable Lean source, original-proof notices, exact kernel reports and raw log hashes; it does not claim a repository-wide provenance audit.

The source-level blueprint synchronization and reverse-coverage checks passed for the three new modules (`blueprint-sync.log`). This verifies declaration spelling and chapter coverage; it is distinct from the repository-wide kernel `checkdecls` command, whose root module is not built in this worktree.

These are auxiliary results. The boundary implication assumes the partition and its quantitative estimates; the radius comparison assumes the stated radius power bound. Neither the full area law nor Proposition 10.2 is claimed here.

## Source hashes

- `TNLean/PEPS/AreaLaw/EntropyDimension.lean`: `642cd1e991bd47852921c49558893b06c74336101d68919fd2762c3a2e15c93d`
- `TNLean/PEPS/AreaLaw/BoundaryEntropyAssembly.lean`: `a3c312b2c65bb6b698432c751f0e065e52a948f9857dfedc42d692843638d4f9`
- `TNLean/PEPS/AreaLaw/Amplification/RadiusScales.lean`: `94d252d5a6486c9ea3f2f1bfb24feab163f7e8db8ae02ca630b7d02c244e2938`
- `lakefile.toml`: `5c46488fd489a22ebaeec33b872160f36ebc58c23f43c66cc53b1404d48317b2`
- `lake-manifest.json`: `be6fe72fb55036aacaf02c0897b3e81fd70692bcda40219c055e4dd771a8e681`
- `lean-toolchain`: `bc84812c94489d1e3e191baa1dc10d5eb684382d7fe9d2a5ab085e72c1c67e47`
