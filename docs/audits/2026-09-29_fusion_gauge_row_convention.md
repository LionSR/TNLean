# Fusion-gauge row convention

Issue: #8088, under #8011. Checked against the arXiv:1511.08090v2 source
archive, `AnyonsPEPS.tex` line 169, immediately after equation `gauge`.
The mathematical formula is retained in
`Papers/1511.08090/fusion-gauge-excerpt.tex`, with its download URL and the
SHA-256 digest of the original TeX file.

The source writes

\[
X'_{ab,\mu}^{c}=\sum_\nu (Y_{ab}^{c})_{\mu\nu}X_{ab,\nu}^{c}.
\]

The old `regauge_fusionTensor` used the entry with indices `ν μ` instead.
This was an internally consistent column convention, but it did not match
the convention attributed to the source. The difference matters for a
specified nonsymmetric matrix; scalar gauges cannot detect it.

A fusion tensor is a column of `fusionSynthesis`. Consequently the source's
row convention acts on synthesis coordinates on the right by the transpose
of `Y`. The corresponding analysis map acts on the left by the transpose of
`Y⁻¹`. The pair gauge and both tree gauges must therefore use transposes.
The abstract covariance identity remains `F' = G_R⁻¹ F G_L`, with `G_L` and
`G_R` now defined using those transposes. The inverse identity changes in the
same way through its existing definitions.

The Lean definitions and the blueprint are aligned with that row convention.
The coefficient theorem explicitly uses `Y μ ν`; the general synthesis and
F-matrix identities provide checks beyond the multiplicity-one case. No
parallel convention or compatibility alias is introduced.
