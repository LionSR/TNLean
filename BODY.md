## Summary
- audit `blueprint/src/chapter/ch04_channels.tex` against the current public Channel API on `origin/main`
- add missing `\lean{}` / `\leanok` coverage for core Ch. 2 / Ch. 4 / Ch. 5 channel declarations used or discussed in Ch. 4
- tighten a few chapter-local statements so the blueprint hypotheses match the current Lean signatures

## What changed
- added Ch. 4 entries for missing public declarations in the current main-branch API, including:
  - `IsChannel.pos`, `IsPositiveMap.map_isHermitian`
  - `KadisonSchwarz.kadison_schwarz`, `KadisonSchwarz.hilbertSchmidt_contraction`, `KadisonSchwarz.ks_gap_eq_sum_squares`, `KadisonSchwarz.kraus_commute_of_ks_equality`, `KadisonSchwarz.ks_equality_of_peripheral_eigenvector`, `KadisonSchwarz.multiplicative_domain_left`, `KadisonSchwarz.multiplicativeDomain`, `KadisonSchwarz.multiplicativeDomainStarSubalgebra`
  - `ChoiJamiolkowski.choiMatrix_id`
  - `kraus_sum_mul_conjTranspose_of_unital`, `kraus_same_map_of_isometry_combination`
  - `exists_stinespring_dilation`, `exists_stinespring_isometry_of_cptp`
  - `POVM.naimarkKraus_spec`, `POVM.sum_naimarkKraus_conjTranspose_mul`, `POVM.naimarkProjection_apply`
  - `Instrument.total`, `Instrument.update`, `Instrument.probability`, `Instrument.posteriorState`
  - `channelDet_eq_linearMap_det`, `unitaryChannel_isChannel`, `channelDet_unitary_eq_one`, `channelDet_norm_eq_one_of_unitaryChannel`, `channelDet_norm_le_one_of_channel`, `channelDet_norm_eq_one_iff_exists_unitaryChannel_of_channel`
  - `Kraus.fixedPoints_in_multiplicativeDomain`, `Kraus.krausCommutant`, `Kraus.fixedPoints_starSubalgebra`, `Kraus.krausCommutantStarSubalgebra_isGreatest_adjointFixedPointStarSubalgebras`
- updated the Ch. 4 Kadison--Schwarz / fixed-point proofs to reference the newly added local chapter entries rather than later-chapter-only labels
- increased the Chapter 4 `\lean{}` count from **88** on `origin/main` to **111** on this branch

## Audit notes
- this PR stays strictly within `blueprint/src/chapter/ch04_channels.tex`
- current `origin/main` does **not** contain `TNLean/Channel/FixedPoint/ChoiEffros.lean`, so there was no honest Choi--Effros declaration to tag here; existing conditional-expectation material remains covered in `ch06_spectral.tex`
- helper-level declarations in `TNLean/Channel/POVM/Uniqueness.lean`, `TNLean/Channel/Stinespring.lean`, and the determinant split modules were audited, but only the public results with clear Chapter 4 mathematical content were added to the chapter

## Verification
- `lake build`
- `cd blueprint && leanblueprint web`
- `cd blueprint && leanblueprint checkdecls`
- before/after count:
  - `git show origin/main:blueprint/src/chapter/ch04_channels.tex | grep -o '\\lean{' | wc -l` → `88`
  - `grep -o '\\lean{' blueprint/src/chapter/ch04_channels.tex | wc -l` → `111`

Closes #321.
Related to #317.
