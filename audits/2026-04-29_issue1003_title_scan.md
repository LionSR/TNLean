# Issue 1003 title scan

This scan records repository titles that still visibly differ from the naming
conventions in `docs/CONTRIBUTING.md`.

Commands used on 2026-04-29:

```bash
gh issue list --repo LionSR/TNLean --state open --limit 1000 --json number,title,url
gh pr list --repo LionSR/TNLean --state open --limit 1000 --json number,title,url
gh issue list --repo LionSR/TNLean --state closed --limit 1000 --json number,title,url
gh pr list --repo LionSR/TNLean --state merged --limit 1000 --json number,title,url
```

## Open pull requests

No open pull request failed the `type(scope): description` check among 3 open
pull requests.

## Open issues

The scan found 47 candidate open issues among 103 open issues. The most visible
candidates are:

Titles still using PR-style prefixes:

- #905 `formalization(MPS/ParentHamiltonian): periodic block decomposition of chainGroundSpace for toTensorFromBlocks`
- #874 `formalization(PEPS): prove bond-dimension equality from SameState and vertex injectivity`
- #873 `formalization(MPS/Periodic): prove m-factor cyclic contraction for blocked sector gauges`
- #872 `formalization(MPS/Periodic): extract nondecaying sector overlap from blocked gauge equivalence`
- #871 `formalization(MPS/Periodic): prove orthogonal cyclic-sector trace rigidity for self-overlap`
- #870 `formalization(MPS/ParentHamiltonian): split assembled BNT ground states into block components`
- #869 `formalization(MPS/ParentHamiltonian): add contiguous/tail restriction transport API for normal range reduction`
- #832 `formalization(Algebra/MPDO): corrected Perron-Frobenius rank-one step for Lemma C.4 (#781 follow-up)`
- #829 `formalization(MPS/Periodic): supply PeripheralEqualCaseZGaugeOfSameMPV and PeripheralEqualCaseRootFromZGauge for Thm. 3.8 (#787 follow-up)`
- #828 `formalization(MPS/Periodic): multi-block non-decaying overlap witnesses for proportional-case Thm. 3.4 (#786 follow-up)`
- #826 `formalization(MPS/MPDO): converse algebra => fusion direction for section 4.5 RFP equivalence (#612 follow-up)`
- #825 `formalization(MPS/MPDO): extract chi-matrices and trace-power formula for blocked coefficients (#612 follow-up)`
- #823 `formalization(MPS/MPDO): HasCommutingForm local-to-global bridge (from SAL+ZCL) (#782/#783 follow-up)`
- #822 `formalization(MPS/MPDO): finite-length block-separation step for biCF (LinearIndependent wordEntryFamily) (#587 follow-up)`
- #821 `formalization(Channel): minimal-Kraus construction (Channel.HasKrausRankLE E (Channel.choiRank E)) (#670 follow-up)`
- #820 `formalization(PEPS): derive HasLocalGaugeLift from SameState via blocked-middle 3-site MPS reduction (#780 follow-up)`
- #785 `formalization(entropy): mutual-information monotonicity and area-law wrappers`
- #784 `formalization(entropy): remaining von Neumann entropy and SSA core`
- #783 `formalization(rfp-mpdo): simple MPDO RFP construction from blocked tensors`
- #780 `formalization(PEPS): local gauge existence, consistency, and main theorem assembly`
- #779 `formalization(Wolf Ch5): Ando-Lieb and trace convexity consequences`
- #778 `formalization(Wolf Ch5): operator Jensen package for Corollary 5.2`
- #766 `formalization(Wolf Ch2): Lorentz normal form and SVD representation existence`
- #664 `formalization(MPS/Periodic): discharge canonicalization hypotheses to lift Thm. 4.1 from conditional to unconditional`
- #652 `formalization(MPS/CanonicalForm): close BNT grouping Gap section 1 -- unconditional CPSV17 Thm 1 from arbitrary SameMPV2`
- #622 `formalization(periodic): Thm 4.1 -- non-trivial proof of p-refinement iff p-divisibility`
- #618 `infrastructure(periodic): compression-isometry + corner-transition refactor (unblocks Tier-A bridges)`

Other open issue title forms to normalize:

- #670 `scout -- Kraus-rank minimization feasibility for Thm 4.1 reverse discharge (report-only)`
- #590 `MPS/CanonicalForm/SectorIrreducibility -- close the hLift orbit-sum lift hypothesis`
- #588 `MPS/ParentHamiltonian/UniqueGroundState -- prove chainGroundSpace_eq_mpvSubmodule_normal`
- #460 `ParentHamiltonian 3/3 -- prove spectral gap and degenerate ground space`
- #448 `PeriodicOverlap -- prove self-overlap limit and non-matching decay (Cases 1-2)`
- #82 `1708.00029 4/5 Periodic FT: proportional case, equal case, and Z-gauge construction (Thms 3.4, 3.8)`
- #81 `1708.00029 3/5 Periodic overlap dichotomy (Proposition 3.3 / Appendix A)`

Daily records still using the old date separator, written here as `[em dash]`:

- #791 `Daily Standup [em dash] 2026-04-22`
- #602 `Daily Standup [em dash] 2026-04-16`
- #601 `Daily Standup [em dash] 2026-04-15`
- #589 `Daily Standup [em dash] 2026-04-14`

## Closed issues

The scan found 116 candidate closed issues among 271 closed issues. The most
recent closed issues with visible old forms are:

- #911 `formalization(MPS/ParentHamiltonian): reverse inclusion of periodic block decomposition for chainGroundSpace (Route B)`
- #906 `formalization(MPS/CanonicalForm): Lean theorem and blueprint flip for thm:mpv_normalize`
- #877 `formalization(MPS/CanonicalForm): assemble after-blocking sector endpoint for Gap section 1`
- #876 `formalization(MPS/CanonicalForm): construct general BNT sector decomposition for Gap section 1`
- #835 `formalization(MPS/ParentHamiltonian): prove ES operator positivity via cyclic averaging (#460 follow-up)`
- #834 `formalization(Channel/FixedPoint): corner C-algebra instances and faithful-support compression for Wolf Cor. 6.6 (#27 follow-up)`
- #833 `formalization(MPS/MPDO): extract explicit eta operators from Hayashi Markov decomposition for Lemma C.3 (#781 follow-up)`
- #824 `formalization(MPS/CanonicalForm): general heterogeneous BNT-sector endpoint (#652 follow-up)`
- #819 `formalization(MPS/CanonicalForm): derive SectorFixedPointAlgebraRigidity from Wolf fixed-point algebra (#599 follow-up)`
- #787 `formalization(periodic): equal-case periodic FT with Z-gauge (Thm. 3.8)`
- #786 `formalization(periodic): proportional-case periodic FT (Thm. 3.4)`
- #782 `formalization(rfp-mpdo): simple MPDO RFP commuting-form / GSNNCH branch`
- #781 `formalization(rfp-mpdo): simple MPDO RFP local structure (Lemmas C.3-C.4)`
- #205 `[cleanup] Fix in-proof comment in Stinespring.lean (PR #162 nit)`

## Merged pull requests

The scan found 116 candidate merged pull requests among 542 merged pull
requests. The most recent merged pull requests with visible old forms are:

- #890 `feat: formalization(Wolf Ch2): ordered CP maps, Radon-Nikodym, and open-system representation (Thms. 2.3-2.5)`
- #855 `feat: formalization(Channel/FixedPoint): corner C-algebra instances and faithful-support compression for Wolf Cor. 6.6 (#27 follow-up)`
- #854 `feat: formalization(Wolf Ch2): Lorentz normal form and SVD representation existence`
- #853 `feat: formalization(Wolf Ch2): remaining foundational representation corollaries (Props. 2.2-2.4)`
- #827 `ci: switch low-criticality workflows from Opus to Sonnet`
- #790 `[codex] fix(PEPS): repair gauge uniqueness statement`
- #754 `cleanup(ParentHamiltonian): remove duplicate OpenChainRangeReduction / ExtendRight (#747)`
- #716 `cleanup(Channel/Determinant): namespace/import hygiene (#705)`
- #691 `Unconditionalize Thm 4.1 canonicalization hypotheses (#664)`
- #690 `Fix Docs & Blueprint Sync workflow failure`
- #688 `cleanup(MPS/Periodic/ZGauge): trim unused imports (#686)`
- #681 `cleanup(MPS/MPDO): close remaining section 4.5 scaffold integrity items (#625)`
