# Coefficient and degree of the same interleaved Ritz output

The strengthened physical theorem chooses one universal positive constant
before local dimension and gap. For the actual selected coefficient C and
natural degree k, it bounds both log(max(C,1)) and k by that constant times
U^10/g², where U=1+log(max(q,50))+log(1/g) and g=min(gamma,1).
The coefficient and degree still precede length, Hamiltonian, ground multiplicity
and requested accuracy. Both apply to the same interleaved-tree Ritz output;
no older root or independent MPS approximation is substituted.

## Numerical argument

The selected coefficient is named by an explicit scalar definition. Its
logarithm is at most
10^7(K+1)(u³/g+5g^(-1/4)u+1)(1+KD+log(1/g)+log(1+1/gamma)).
For u≤U, g≤gamma, log(1/g)≤U and KD≤CK U^7/g, the last two factors are
at most 7U³/g and (CK+4)U^7/g. The coefficient logarithm therefore has
the claimed capped-gap dependence. The previously established degree estimate
has the same scale, and the larger of the two universal constants serves both.

The numerical construction and its substantial count/reference proof are
shared once. Both earlier numerical signatures and both earlier physical
signatures are byte-identical active corollaries. The actual physical
root/refinement/Ritz proof after parameter selection is unchanged. The
preservation checks are recorded in
/tmp/alvv-interleaved-coefficient-preservation-20261103.json.

## Scope

This supports ALVV, arXiv:1602.08828v2, t:alg1, lines 1777–1817, for the explicitly
modified construction. The capped gap, block leaves, fixed nominal failure
target and enlarged integer counts remain. No adaptive joint probability,
source energy-estimation invariant or running time is asserted. The relevant
notes remain docs/paper-gaps/alvv16_approximation_parameters.tex and
docs/paper-gaps/alvv16_final_filter_gain.tex in TNLean.

## Verification

The immutable provider was TN 20cad76ebfa6e770263c4a5d5333917c5b226ed9,
with its own QIC 98ba564e3c9603dc93d2173e3dc87a85ce750456. Fresh explicit
source/object overrides covered every affected selected importer. The scalar
coefficient owner passed strict checking in 8.827 seconds with three protected
pairs. The shared numerical owner passed in 9.403 seconds with seven pairs.
The affected physical owner passed in 21.651 seconds with 771 pairs.
The imported nine-declaration foundation inspection passed in 35.44 seconds
with 772 protected pairs and reported only propext, Classical.choice and
Quot.sound. Its temporary source was removed.

An initial attempt to place all coefficient analysis inline exhausted the
unchanged 200,000-heartbeat limit after 54.512 seconds. This diagnostic is
retained under the private diagnostics directory. Factoring the genuine
scalar coefficient estimate resolved it; no budget was increased and no
unchanged source was rerun merely to obtain a faster timing. The historical
31.415-second compilation observation remains recorded in the preceding audit.
No provider, dependency cache or Mathlib source was changed. Ordinary combined
library and compiled-book gates remain separate integration checks.
