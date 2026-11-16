# Issue map: MPO symmetries after Garre-Rubio, Lootens and Molnár

Maintainers' map of the open issues of the campaign (tracker #8012, related
trackers #8315 and #8011) to their source statements, the Lean declarations
already on main, and their status. Source: `Papers/2203.12563/REsubmission.tex`
(arXiv:2203.12563v3) unless stated otherwise. Reviewed 2026-11-16 against main
`73007e1`.

| Issue | Source statement | On main | Open | Status |
|-------|------------------|---------|------|--------|
| #8048 | §4.3, lines 865–992; `TRSF1group` line 954, γ display lines 935–952; corrected in `docs/paper-gaps/glm23_time_reversal_l_symbol.tex` | `MPOTensor.GroupFamily.FusionData.exists_real_cohomologousTo_omega_of_timeReversal`, `omega_cohomologousTo_star_of_timeReversal`, `nonempty_bondGauge_timeReversal` (`MPOSymmetry/TimeReversalAnomaly.lean`); scalar side in `TNLean/Algebra/ScalarThreeCocycleTimeReversal.lean` | Tensor-level derivation of `conj L / L = γ_{gh,x} / (γ_{h,x} γ_{g,h·x})` from action data commuting with time reversal | Idle; overlaps the files of #10626, so wait for it to land |
| #8050 | §5, lines 1219–1780: main theorem line 1231, `defsym` 1241, `defphase` 1255; App. B lines 2457–2475 | Foundations of §§2–3, mixed tensor and interpolation (`ArbitraryPhysicalMixed*.lean`, `MixedEndpoint*.lean`, `JointMixedEndpoint*.lean`) | Invariance of the L class along a gapped symmetric path; the classification theorem | Idle; multi-PR |
| #8053 | §6, lines 1991–1993; L = F near line 605; `docs/paper-gaps/glm23_fibonacci_module_rank_scope.tex` | Uniqueness of the regular module (`MPS/Examples/Fibonacci/FibonacciNIMRepClassification.lean`, `FibonacciSymmetricFamilyDecomposition.lean`, `FibonacciAnomaly.lean`); exact gauges (`FibonacciAction.lean`); F-symbols (`FibonacciFSymbol.lean`) | Exact fusion and action trees of the two-block realization and `actionLMatrix τ τ = F^{τττ}_τ` up to multiplicity gauge | Idle (claim of 2026-10-30, no branch work) |
| #8054 | §6, lines 2003–2201 (construction) and 2224–2233 (zippers) | `boundaryTensor`, `mpo_boundaryTensor_mul`, `mpo_boundaryTensor_conjTranspose` (`MPS/MPU/GroupCocycleMPO/ArbitraryBoundary.lean`); zippers in `MPOSymmetry/PBCGroupProjector.lean` | Coset states for a subgroup trivializing ω, with the printed action tensors and L-symbols | Idle; overlaps the files of #10626 |
| #8948 | §5.3, from line 1695; final paragraph of `docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex` | `arbitraryPhysicalMixedInteraction`, `tendsto_arbitraryPhysicalMixed_groundSpace_starProjection` | (a) a symmetrized path Hamiltonian commuting with the mixed operators; (b) block-diagonal interpolation of block-injective endpoints | Idle; statement of (a) needs the symmetrized parent Hamiltonian |
| #10519 | arXiv:2204.05940 `mpo.tex` lines 866–875, 880, 1409–1421; `docs/paper-gaps/mrgscp22_pre_bialgebra_counit_scope.tex` | `exists_counit_iff`, `dualRepresentationCounit`, `toPreBialgebraOfDualRepresentation` (`MPS/MPDO/CompleteZipperFusionCoassoc.lean`) | Construct the fusion family from an abstract pre-bialgebra with a unital injective representation | Idle; multi-PR |
| #8060 | arXiv:2405.00439 `MPU-DW.tex` lines 2069–2118 | `MPS/MPU/TruncationCommutator.lean` | Finite-group detector and its endpoint dependence | In progress: #10641 |
| #7574 | arXiv:1703.09188 `lemma:sym-trafo-swap`, lines 2065–2085 | `MPS/MPU/Examples/SwapSymmetryTransport.lean`, `SwapBlockedSymmetryTransport.lean` | Stabilized comparison with identity ancillas | In progress: #10640 |
| #8321 | Retyping of associator and L-symbol data | `FusionData`, `ActionData`, `lSymbol` (`MPOSymmetry/Associator.lean`, `AnomalyObstruction.lean`) | Migration to Mathlib cochains | In progress: #10626, stacked on #10616 and #10615 |
| #8322 | lines 458–568 and 1795–1805 | `MPOTensor.IsFusionRing` (`MPOSymmetry/FusionRing.lean`), `IsNIMRep` (`Defs.lean`) | Based rings on finitely supported integer combinations | In progress: #10636 |

Closed leaves of #8012: #7966, #7968, #8045, #8046, #8047, #8049, #8051,
#8052, #8142, #8143, #8348, #9184, #10457, #10458.
