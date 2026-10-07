# Verification of one-dimensional sources on unused pairs

Source revision: `8eccd116408d22a115220881e7e07c96aa4f23ea`.

The new blueprint statements agree with the final three Lean modules. The completion retains the original inventory as a literal suffix, adds normalized sources only at previously absent unordered pairs, and gives both endpoint spaces dimension one. Its exact recovery is proved uniformly over the original memory. The final consumer carries the dimension-one conclusion for every pair absent from the original composition, and factors through actual local contractions. Finiteness concerns the prescribed parties of one gate; no bound on their number or common source spaces for different branches is asserted.

All 11 public declarations occur exactly once in the new fragment and are covered by the separate imported-declaration audit. The declaration manifest and that audit have identical name sets. The latter was performed by the proof verifier at the same source revision and records only `propext`, `Classical.choice`, and `Quot.sound`.

The following checks succeeded:

- Reader-facing prose, `chktex`, and the repository's pinned `latexindent` comparison on the new fragment.
- Full-source blueprint synchronization: 20,076 theorem-like entries (`sync.json.total_blueprint_refs`) and 20,082 unique declaration references (`sync.log`); no missing declarations or duplicate tags reported. The predecessor recorded 20,065 entries and 20,071 unique references; the saved declaration lists differ by exactly the 11 new declarations, with no removals.
- Static dependency analysis of the complete copied blueprint: 7,350 labelled mathematical entries and 18,306 dependency edges, without cycles or duplicate labels.
- A focused PDF and web rendering containing the new fragment and the preceding three PEPS fragments, with no rendering warnings. The PDF has 12 pages; pages 10–11 containing the new material were visually inspected, with no clipping, overlap, or broken mathematical expressions.
- Browser validation of all four focused mathematical pages: 618 typeset expressions, no failures.

`commands.json` records the rendering and validation commands, working directories, elapsed times, and exit codes. `source-revision.json` verifies that the four rendered fragments and the content router are byte-identical to the named commit. The web build used the installed pinned texra-blueprint tool environment and a disposable copy of the pinned tenkz sources. All generated files are confined to this temporary directory.

The empty-party and singleton-party regression theorems both instantiate the actual completion theorem and prove that its resulting inventory is empty while retaining normalization, pair coverage, and exact source-free recovery. They passed raw Lean with the package options and `warningAsError=true`; a subsequent imported audit reports only the three standard axioms above. Their complete source, commands, hashes, and logs are in `/tmp/tnlean-unused-pair-regression`. The first test attempt used an unnecessary `Fintype` assumption; its linter rejected that assumption. Replacing it by `Finite` gave the final clean check. The initial diagnostic is retained separately.

This verification used direct Lean elaboration of the regression and the separately compiled imported declarations. It did not run a local Lake build or full-root `leanblueprint checkdecls`, and it did not modify a dependency cache.
