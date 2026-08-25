# tenkz companion extraction

TNLean no longer vendors the tenkz TeX package. The package, corpus, manual,
and its CI live in [LionSR/tenkz](https://github.com/LionSR/tenkz).

```text
TN_SOURCE_SHA=85a12e6b524310795bb7aaa7d3e3fc33a59566c0
TENKZ_PIN=tenkz-v0.7.1
TENKZ_SHA=2210cfd15c166c8410e80420a9f7c7478010f997
```

The freeze SHA is TNLean `origin/main` at extraction. tenkz history is a
`git filter-repo` image of that tree's tenkz paths; the filtered tip of
those blobs is `24e66c540` (#7157), with the standalone-repo commit
`2210cfd15` (`tenkz-v0.7.1`) on top.

TNLean consumes the tag and immutable commit recorded in `tenkz.toml`
through `scripts/fetch_tenkz.py`, which clones into gitignored
`.deps/tenkz`. Remaining in-tree consumers:

- `blueprint/src/Packages/tenkz_pic.py`
- `scripts/audit_cpsv16_labels.py`
- `scripts/test_audit_cpsv16_labels.py`
- `scripts/tenkz_blueprint_sweep.py`
- `scripts/test_tenkz_blueprint_sweep.py`
- `scripts/test_tenkz_pic.py`
- `scripts/test_tenkz_equation_web.py`
- `scripts/test_tenkz_peps_torus.py`
- `scripts/test_tenkz_index_routing.py`
- `scripts/check_tenkz_demolition.py` (retired tensor-network catalogue)

Package-owned GitHub issues were transferred to LionSR/tenkz. TNLean #5693
remains here because it concerns adoption in the blueprint. New package work
opens on LionSR/tenkz.
