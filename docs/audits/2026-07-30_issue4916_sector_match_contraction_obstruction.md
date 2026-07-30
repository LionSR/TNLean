# Sector-match contraction obstruction

## Scope

This note records the obstruction encountered while attempting to prove
`periodicOverlap_gaugeEquiv_of_sector_match` in
`TNLean/MPS/Periodic/Overlap/SectorMatch.lean`.

The intended argument is arXiv:1708.00029, Appendix A, lines 1023–1117.
No alternative argument was substituted.

## Source argument

Before the contraction begins, lines 985–1002 have produced, for every matched
pair of sectors, a phase and an ambient corner partial unitary
\[
  U_v=P_uU_vQ_v
\]
such that the blocked corner tensors satisfy `eq:BCmprop`. In particular,
\[
  U_v^\dagger U_v=Q_v,\qquad U_vU_v^\dagger=P_u.
\]

The concatenation at lines 1041–1056 uses these support identities when
successive blocked factors are multiplied. The application of the inverses
\(\Omega_{u+1},\ldots,\Omega_u\) at lines 1057–1062 then leaves the uniform
product-tensor identity `eq:resultprop`.

## Lean-side mismatch

The current input to `sectorTensor_proportional_of_blockedMatch` is
`hBlockMatch`. For each sector it supplies only a `GaugePhaseEquiv` between the
abstract compressed tensors
`blocksA u` and `blocksB (u + q)`. The cyclic decomposition also supplies
multiplicative, adjoint-preserving linear equivalences
\[
  \varphi^A_u:M_{\dim A_u}(\mathbb C)\longrightarrow P_uM_D(\mathbb C)P_u,
  \qquad
  \varphi^B_v:M_{\dim B_v}(\mathbb C)\longrightarrow Q_vM_D(\mathbb C)Q_v.
\]
However, the available API contains no theorem spatially implementing the
induced isomorphism between these two ambient corners. The missing theorem must
produce a matrix \(U_v\) satisfying
\[
  U_v=P_uU_vQ_v,\qquad
  U_v^\dagger U_v=Q_v,\qquad
  U_vU_v^\dagger=P_u,
\]
and transport the compressed gauge-phase equation to `eq:BCmprop` in the
ambient matrix algebra.

This is not supplied by `GaugePhaseEquiv`: its gauge matrix acts on the
compressed bond space, whereas `cornerLetter`, `cornerProd`, and
`repeatedBlocks_of_globalGauge` require matrices on the ambient bond space.
The dimension equality in `GaugePhaseEquiv` is necessary but does not itself
construct the spatial corner implementer.

## Consequence for the existing contraction lemmas

The two available contraction results begin strictly after this missing step:

- `cornerProd_blockMatch_pow` assumes a direct scalar equality of ambient
  corner products. It has no corner implementers and therefore cannot express
  `eq:BCmprop`.
- `exists_cornerProd_contraction_of_sectorRightInverse` contracts one ambient
  corner family after its right inverse has been lifted. It does not transport
  the same coefficients through the matched \(B\)-family and cancel adjacent
  corner implementers.

Thus source lines 1041–1062 do not currently transfer: the term whose adjacent
partial unitaries the paper cancels cannot be stated from `hBlockMatch`.
Proceeding directly from the compressed gauge matrices would require a new
argument not present in the cited contraction.

## Required continuation

The source-faithful continuation requires the following result before the
\(\Omega\)-contraction.

1. Prove spatiality for two full complex matrix corners represented by the
   supplied multiplicative, adjoint-preserving corner equivalences.
2. Apply it to each compressed unitary gauge to obtain the ambient partial
   unitaries \(U_v\) and the ambient blocked identity `eq:BCmprop`.
3. Add the gauge-aware cyclic concatenation lemma in which adjacent identities
   \(U_{v+1}^\dagger U_{v+1}=Q_{v+1}\) telescope.
4. Combine that lemma with
   `exists_cornerProd_contraction_of_sectorRightInverse` to obtain the uniform
   product-tensor identity.
5. Only then apply
   `exists_kappa_product_one_of_piTensorProduct_eq_root_smul`, the
   left-canonical unit-modulus normalization,
   `exists_fin_complex_unit_cyclic_coboundary_shift_of_prod_eq_one`, and
   `repeatedBlocks_of_globalGauge`.

The first item is the missing formal ingredient corresponding to the ambient
unitaries already present at arXiv:1708.00029, Appendix A, lines 985–1002.
