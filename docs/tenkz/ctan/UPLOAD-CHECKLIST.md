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
- [ ] `python3 scripts/tenkz_ctan.py offline` passes. It is part of `check`
      above and repeated here because it is the reading an arXiv submission
      gets rather than an installation: the archive is unpacked flat, a case
      of each picture class is compiled beside it with no installer or
      fetcher reachable, and each result is audited.
      `docs/tenkz/ctan/DEPENDENCIES.md` states what the isolation is and what
      it does not prove.
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
      drop them. They are the two libraries that come from packages of their
      own rather than from pgf; `docs/tenkz/ctan/DEPENDENCIES.md` traces every
      load to the code that reads it.

## What the check proves, and what it does not

`scripts/tenkz_ctan.py check` proves the archive is a function of the tree:
it builds twice, under two file-creation masks and in two directories, and
compares the bytes. It walks the load graph from `tenkz.sty` and refuses a
runtime file the entry point does not load, or a load the pinned manifest
does not know about. It reads the version from the one declaration that owns
it and rejects a README, citation record, or archive name that states
another. It normalizes permissions and rejects compilation leftovers and
names outside the invariant ASCII subset. Finally it unpacks the archive on
its own and compiles a picture against it, asking the engine to record every
file it opened and requiring that every tenkz file resolved inside the
unpacked directory — so a runtime file the archive forgot is a failed run
rather than a silent fall-back to a copy already installed on the machine.

It then reads the same tree as an arXiv source submission and compiles against
it. The submission reading is stricter than the installation one: the tree has
to be flat, has to be the runtime rather than the sources a runtime is
generated from, has to name no path on the machine that built it, and has to
call no primitive that would need a shell. Against the flattened archive it
compiles a case of each picture class the release is judged on, with the user
TeX trees emptied, every installer and fetcher shadowed by a script that
records its own call and fails, and font and format generation refused. Each
result goes through the event audit and has to show its own class in the
stream, so a run that produced a PDF and no tensor network fails.

Every finding is a printed line of the report, and the check prints all of
them: a staged name an unpacking tool would misread does not cut the report
short. The commands that write stop on those same findings, read from the
same checks, because a command that writes has nowhere to put one.

It does not judge the manual, the prose, or the mathematics, and it does not
know whether the release campaign permits a tag. Those are read by the
gates in `RELEASE-POLICY.md` §2 and by the campaign harness in
`tests/tenkz/release-harness/`.
