# SCP10 source preservation snapshot

This branch preserves recovered source from the unpublished October 5 SCP10 work. It is a recovery archive, not an accepted formalization or a merge candidate. Reintegrate files at their original paths only through separately validated changes; do not merge this archive wholesale.

The expanded snapshot contains 20 source/test/document files: 16 production modules, 2 Lean tests, a blueprint leaf and a historical audit. Seven production files match recorded original SHA-256 hashes; the remaining 13 files are reconstructions without original digests. The manifest gives the status of each file.

No current Lean build or regression test has validated these copies. The original packet used an older QICLean pin. Historical audit text and blueprint badges are preserved as historical source, not current acceptance claims. Missing dependency modules must be restored or replaced and the complete import closure strictly checked before any mathematical result is counted as reinstated.

The historical inventories describe 54 production modules and ten tests from the earlier integration; they do not mean those files are all recovered. The separate digest table records 31 historical reviewed files. File identity, compilation, source faithfulness and merged coverage are distinct checks.

The five direct missing imports against published #8707 head f8ebaf51 are recorded in dependency-frontier.json. Their transitive dependencies may require additional restoration. Reconstruction and dependency recovery continue separately. No new proof, merge or deployment is claimed by this snapshot.
