# Notice for the `Papers/` directory

This directory contains the arXiv LaTeX sources of the papers whose results
TNLean formalizes. They are included as reference material for the
formalization, either with the permission of their authors or under the public
license recorded below. Copyright in these works remains with their authors
and, where applicable, their publishers.

**The paper source files are not covered by the repository's license.** The
top-level `LICENSE` (Apache License 2.0) applies to the Lean code, the blueprint,
and the other original content of this repository, including this notice and
`external_sources.toml`; it does not apply to the paper source files. Among the
files listed in the table below, entries marked `non-exclusive-distrib 1.0` or
`assumed 1991-2003` are present under author permissions specific to this
repository; the arXiv licenses alone grant no downstream redistribution right,
and that permission is not inferred for additional works. Entries marked
`CC BY 4.0` are redistributed under the linked Creative Commons license. The
version of record for each paper is the arXiv posting or the journal
publication.

[`external_sources.toml`](external_sources.toml) also pins external source
artifacts used by the MPU audits. A `download-only` entry records metadata only:
neither its source archive nor its extracted source file is part of this
repository. `scripts/verify_external_paper_sources.py` recovers the file from
the official e-print into ignored build output only when called with `--fetch`,
and verifies both the archive and extracted-file digests. A `vendored` entry is
an unchanged archive member kept under `Papers/` under its recorded
redistribution license. Without `--fetch`, the verifier checks only source files
already present locally; thus a clean checkout can verify the vendored entries,
whereas a `download-only` entry first requires the explicit network fetch.

| arXiv ID | Title | Authors | arXiv license |
|---|---|---|---|
| [quant-ph/0405174](https://arxiv.org/abs/quant-ph/0405174) | Reversible Quantum Cellular Automata | B. Schumacher, R. F. Werner | assumed 1991-2003 |
| [quant-ph/0608197](https://arxiv.org/abs/quant-ph/0608197) | Matrix Product State Representations | D. Pérez-García, F. Verstraete, M. M. Wolf, J. I. Cirac | assumed 1991-2003 |
| [0802.0447](https://arxiv.org/abs/0802.0447) | String Order and Symmetries in Quantum Spin Lattices | D. Pérez-García, M. M. Wolf, M. Sanz, F. Verstraete, J. I. Cirac | assumed 1991-2003 |
| [0909.5347](https://arxiv.org/abs/0909.5347) | A quantum version of Wielandt's inequality | M. Sanz, D. Pérez-García, M. M. Wolf, J. I. Cirac | non-exclusive-distrib 1.0 |
| [1001.3807](https://arxiv.org/abs/1001.3807) | PEPS as ground states: degeneracy and topology | N. Schuch, I. Cirac, D. Pérez-García | non-exclusive-distrib 1.0 |
| [1010.3732](https://arxiv.org/abs/1010.3732) | Classifying quantum phases using MPS and PEPS | N. Schuch, D. Pérez-García, I. Cirac | non-exclusive-distrib 1.0 |
| [1210.6613](https://arxiv.org/abs/1210.6613) | Frustration free gapless Hamiltonians for Matrix Product States | C. Fernández-González, N. Schuch, M. M. Wolf, J. I. Cirac, D. Pérez-García | non-exclusive-distrib 1.0 |
| [1606.00608](https://arxiv.org/abs/1606.00608) | Matrix Product Density Operators: Renormalization Fixed Points and Boundary Theories | J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete | non-exclusive-distrib 1.0 |
| [1708.00029](https://arxiv.org/abs/1708.00029) | Irreducible forms of Matrix Product States: Theory and Applications | G. De las Cuevas, J. I. Cirac, N. Schuch, D. Pérez-García | non-exclusive-distrib 1.0 |
| [1804.04964](https://arxiv.org/abs/1804.04964) | Normal projected entangled pair states generating the same state | A. Molnár, J. Garre-Rubio, D. Pérez-García, N. Schuch, J. I. Cirac | non-exclusive-distrib 1.0 |
| [1903.09439](https://arxiv.org/abs/1903.09439) | Mathematical open problems in projected entangled pair states | J. I. Cirac, J. Garre-Rubio, D. Pérez-García | non-exclusive-distrib 1.0 |
| [2011.12127](https://arxiv.org/abs/2011.12127) | Matrix Product States and Projected Entangled Pair States: Concepts, Symmetries, and Theorems | J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete | non-exclusive-distrib 1.0 |
| [2203.12563](https://arxiv.org/abs/2203.12563) | Classifying phases protected by matrix product operator symmetries using matrix product states | J. Garre-Rubio, L. Lootens, A. Molnár | [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) |
| [2405.00439](https://arxiv.org/abs/2405.00439) | Fractional domain wall statistics in spin chains with anomalous symmetries | J. Garre-Rubio, N. Schuch | [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) |
| [2502.20257](https://arxiv.org/abs/2502.20257) | Symmetry defects and gauging for quantum states with matrix product unitary symmetries | A. Franco-Rubio, A. Bochniak, J. I. Cirac | non-exclusive-distrib 1.0 |
