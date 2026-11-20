# Plan: the frustration-free two-dimensional area law by the short route

Source: `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex` (the reading
note of November 18, 2026), cited below as *the note*, with its equation labels. The note
specializes Theorem 1.1 of OpenAI, *A two-dimensional area law from a global spectral gap*
(September 24, 2026, revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`) to
frustration-free, finite-range, gapped Hamiltonians, and replaces the time-filtered
constraints and Poisson clocks of Proposition 10.2 by an exact sweep of local filters.

This file lists the Lean statements to prove, in order. Each step is one or two pull
requests on a branch `claude/ff2d-*`. New modules live in
`TNLean/PEPS/AreaLaw/FrustrationFree/`. Every new result gets a blueprint entry in a new
section of `blueprint/src/chapter/ch24_peps_area_law_frustration_free.tex`.

## The model, `eq:model`

For `Λ ⊂ ℤ²` finite, `h : PlaneInteraction Λ q R` (one term for each admissible support of
graph diameter at most `R`), `J, Δ > 0` and `Ω : StateSpace Λ q`, the note assumes

```
0 ≤ h_X ≤ J·1,    h_X Ω = 0,    ‖Ω‖ = 1,    Δ (1 - |Ω⟩⟨Ω|) ≤ ∑_X h_X.
```

These are the only hypotheses. Every Lean statement below must have no others (faithfulness
rule of `CLAUDE.md`). The goal `eq:goal` is

```
S_Ω(A) ≤ C(q, R, J, Δ) |∂_Λ A|   for every Λ, h, Ω, A,
```

with `C` chosen before `Λ, h, Ω, A`.

## Step 0: the model and the statement

Module `FrustrationFree/Model.lean`.

* `IsFrustrationFreeGapped h J Δ Ω : Prop`: the five conditions of `eq:model`, with
  `0 ≤ h_X` and `h_X ≤ J • 1` in the Loewner order and the gap as
  `Δ • (1 - vecMulVec Ω (star Ω)) ≤ h.hamiltonian`.
* `IsFrustrationFreeGapped.isGapped : IsGapped h.hamiltonian 0 Δ` and
  `IsFrustrationFreeGapped.groundSpace_eq : groundSpace h.hamiltonian 0 = span {Ω}`, from
  `ManyBody.isGapped_and_groundSpace_eq_span_iff`.
* `IsFrustrationFreeGapped.isHermitian`, `.norm_term_le : ‖h_X‖ ≤ J`.
* `FrustrationFreeAreaLaw : Prop`: `eq:goal` for every `q ≥ 1`, `R`, `J, Δ > 0`.
* `frustrationFreeAreaLaw_of_uniformAreaLaw : FrustrationFreeAreaLaw`, a corollary of the
  general `uniformAreaLaw`. This checks the statement. It is not the short route: its proof
  passes through the filtered constraints, and its blueprint entry says so.

## Step 1: sweep contraction, `eq:sweep`

Module `FrustrationFree/SweepContraction.lean`, abstract (an inner product space, no sites).

The note writes the sweep with `G_i = (1 - k_i)^{1/2}`. We use instead the orthogonal
projections `Π_i` onto the ranges of the terms and the factors `1 - Π_i`, so that QICLean's
detectability lemma (`ContinuousLinearMap.re_inner_sum_complementProd_le`,
`QICLean/Analysis/DetectabilityLemma.lean`) applies unchanged. This changes the sweep
operator, not any hypothesis of the note, and gives a constant at least as good:
`Π_i ≥ k_i = h_i/J` gives `∑ Π_i ≥ g (1 - P)` with `g = Δ/J`, and a projection's own
contribution vanishes after its factor, so the bound has `d²` in place of `(d+1)²`.

1. `ContinuousLinearMap.norm_sq_complementProd_le_of_gap`: projections `h_0, …, h_{m-1}`, each
   failing to commute with at most `d` others, with `h_k Ω = 0` and
   `γ ‖v‖² ≤ re ⟪v, ∑ h_k v⟫` for `v ⊥ Ω`. Then for `v ⊥ Ω`,
   `(d² + γ) ‖D v‖² ≤ d² ‖v‖²` with `D = complementProd h m`.
2. `complementProd` maps `Ω^⊥` to itself and fixes `Ω`.
3. `norm_pow_complementProd_le`: `‖D^t v‖ ≤ θ^t ‖v‖` for `v ⊥ Ω`, with
   `θ = (1 + γ/(d+1)²)^{-1/2}`, the constant of `eq:sweep`.

Module `FrustrationFree/RangeProjection.lean`, on matrices.

4. QICLean's support projection `Π_A = hA.supportProj` of a positive semidefinite `A`
   (`QICLean/Analysis/SupportProjectionOrder.lean`, `QICLean/Algebra/PosSemidefSupport.lean`)
   is an orthogonal projection annihilating `ker A`. New: `A ≤ J • Π_A` when `A ≤ J`, and
   `Π_A ∈ supportedOperators X D` when `A` is (by `ManyBody.cfc_mem_supportedOperators`).
5. `sum_supportProj_ge`: under `eq:model`, `∑ Π_X ≥ (Δ/J) (1 - P)`.

## Step 2: exact light cone, `eq:cone`

Module `FrustrationFree/LightCone.lean`.

6. A proper colouring of the overlap graph of the supports with at most `d + 1` colours,
   `d = v_R μ_R` (`v_R = 1 + 2R(R+1)`, `μ_R = 2^{v_R - 1}`); the sweep orders the terms by
   colour. Within one colour the factors have disjoint supports and commute.
7. `layer_mulVec_eq`: for one colour layer `F = ∏_{c(X) = a} (1 - Π_X)` and an operator `B`
   supported on `U`, every factor fixing `Ω̃`, `F (B Ω̃) = F_U (B Ω̃)` where `F_U` keeps the
   factors meeting `U`, supported on `N_R(U)`.
8. `sweep_pow_mulVec_eq`: `D^t (B Ω̃) = L_t (B Ω̃)` with `L_t` supported on `N_{χRt}(U)` and
   `L_tᴴ Ω̃ = Ω̃`. Stated on a general site type, so it applies on the physical sites
   enlarged by the two copies `s', e'` of the target (`AncillaSites Λ X`), with
   `Ω̃ = Ω ⊗ ξ`.

## Step 3: amplification for frustration-free terms

Module `FrustrationFree/Amplification.lean`.

9. `ffAmplificationBound`: the conclusion of `AmplificationBound q R J Δ` for every instance
   of `eq:model`, with the radius bound `r ≤ C n^{1-ε}` (stronger than
   `r ≤ C n^{(1-ε)/α}`). Proof as in the note: the typical projections and restoring estimates
   `eq:restore` (`exists_typicalProjectors_three_cuts`, `restoringOperator_estimates`), the
   time `t = ⌈(log M₀ + K log n)/|log θ|⌉`, Steps 1–2, then the polar correction
   `exists_ancilla_unitary_of_good_realization` with `D = D^t`, `D_ret = L' = L_t` (so the
   omission and truncation errors are zero) and the entropy comparison
   `mutualInformation_le_of_ancilla_unitary`.

## Step 4: assembly by two-family cancellation

Module `FrustrationFree/AreaLaw.lean`.

10. An instance-wise form of `regionalEntropy_le_of_collar_amplification_twoFamilies_constants`
    taking the collar and amplification conclusions for the given `h, Ω` only.
11. `frustrationFreeAreaLaw : FrustrationFreeAreaLaw`, from `sublinearCollarBound_real`
    (Proposition 9.6, valid for every gapped instance, so for `eq:model`), Step 3 and
    `twoFamilyDecomposition` (Proposition 11.2). Its proof does not use `amplificationBound`.

## Deferred: the scanner on the raw terms, `eq:identity`

The note also observes that the scanner of Proposition 9.2 can run on `k_i = h_i/J`
directly. The appendix of the note records that this needs the raw terms supplied to the
transport and norm-comparison data (`FiniteFamilyTransportBound` accepts arbitrary positive
supported terms; the physical scanner `scanner_estimate_actualScan` builds filtered terms
internally). Step 4 uses the existing collar bound, which holds for every gapped instance,
so this replacement shortens the proof further but is not needed for `eq:goal`. It is
planned after Step 4.

## Status

| Step | Statements | State |
|---|---|---|
| 0 | model, statement, corollary of the general theorem | planned |
| 1 | sweep contraction, range projections | planned |
| 2 | colouring, light cone | planned |
| 3 | amplification | planned |
| 4 | assembly | planned |

Deviations from the note found while formalizing are recorded in `docs/paper-gaps/` and
listed here.
