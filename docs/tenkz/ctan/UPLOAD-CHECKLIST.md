# Uploading tenkz to CTAN

The steps between a release head and an accepted upload, in order. Nothing
here authorizes a version bump: the version is whatever
`tex/tenkz/tenkz.sty` declares, and only the release-preparation change
named by `RELEASE-POLICY.md` §3 may change it.

## 1. Before building the archive

- [ ] The release head is the exact commit the campaign signed off. The
      archive is a function of the tree, so any later commit is a different
      archive.
- [ ] The standing gates listed in `RELEASE-POLICY.md` §2 are green at that
      head.
- [ ] `python3 scripts/tenkz_ctan.py check` passes at that head, with a TeX
      installation present so the clean-install check runs rather than being
      skipped. Add `--require-smoke` to make its absence a failure.
- [ ] `python3 scripts/tenkz_ctan.py sync` shows the version and date the
      release artifacts agree on. Disagreement is the release-preparation
      change's work, not the archive builder's.
- [ ] The manual is built reproducibly and is ready to be carried by the
      archive. Open work: the archive currently stages no manual, because
      its reproducible build is not finished. CTAN expects documentation in
      the package, so this is the last blocking item before an upload, not a
      refinement.

## 2. Building the archive

```
python3 scripts/tenkz_ctan.py archive --out build/ctan
```

writes `build/ctan/tenkz/` (the tree as it will unpack),
`build/ctan/tenkz-VERSION.zip`, and the archive's digest beside it. Record
the digest in the release notes and in the announcement's archive-hash
field.

- [ ] The digest recorded in the release notes is the digest the command
      printed at the release head, produced by the environment that built the
      uploaded archive. The staged tree is byte-identical wherever it is
      built; the archive's compressed bytes additionally depend on the
      compression library, so a digest is quoted for one archive rather than
      as a property of the version.
- [ ] The archive unpacks into a single `tenkz/` directory.

## 3. The upload form

CTAN's form asks for the fields below. The values come from the staged
material, so they are reviewed with it rather than typed fresh each time.

| Field | Value |
|---|---|
| Package name | `tenkz` |
| Version | the `\ProvidesPackage` version at the release head |
| License | Apache License 2.0 (CTAN's free-license key `apache2`) |
| Author | Sirui Lu |
| Maintainer contact | sirui.lu@mpq.mpg.de |
| Summary | tensor-network diagrams from a description of the network |
| Description | the opening section of the staged `README.md` |
| Home page | https://github.com/LionSR/TNLean |
| Repository | https://github.com/LionSR/TNLean |
| Bug tracker | https://github.com/LionSR/TNLean/issues |
| Support | the same tracker |
| Suggested directory | `graphics/pgf/contrib/tenkz` |
| Announcement | `docs/tenkz/ANNOUNCEMENT-1.0-draft.md`, with every pending field filled |

A note on the license, for whoever fills the form. The repository is under
the Apache License 2.0 and the package inherits it; CTAN accepts that
license and classifies it as free. LaTeX packages more often carry the LaTeX
Project Public License, and some distribution tooling assumes it. Choosing
to add LPPL 1.3c as an alternative is a maintainer decision, and it must be
made before the upload rather than after, because a license stated on CTAN
is hard to correct later.

## 4. After the upload

- [ ] The announcement's CTAN URL, release URL, archive hash, and freeze
      commit are filled in.
- [ ] The package appears in TeX Live's next update, and the `hobby` and
      `spath3` dependencies are recorded so a distribution build does not
      drop them.

## What the check proves, and what it does not

`scripts/tenkz_ctan.py check` proves the archive is a function of the tree:
it builds twice, under two file-creation masks and in two directories, and
compares the bytes. It walks the load graph from `tenkz.sty` and refuses a
runtime file the entry point does not load, or a load the pinned manifest
does not know about. It reads the version from the one declaration that owns
it and rejects a README, citation record, or archive name that states
another. It normalizes permissions and rejects compilation leftovers and
names outside the invariant ASCII subset. Finally it unpacks the archive on
its own and compiles a picture against it, so a runtime file the archive
forgot is a failed run rather than a silent fall-back to the repository copy.

It does not judge the manual, the prose, or the mathematics, and it does not
know whether the release campaign permits a tag. Those are read by the
gates in `RELEASE-POLICY.md` §2 and by the campaign harness in
`tests/tenkz/release-harness/`.
