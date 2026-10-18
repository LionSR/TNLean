/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualTerminalEntropyBounds
import TNLean.PEPS.AreaLaw.Scan.PositivePrefixEntropyTransfer

/-!
# Source positive-prefix input controls the actual sharp entropy losses

The accepted quantitative continuity theorem transfers the original source
prefix input to the same supplied truncated vector. The actual terminal
geometry then bounds the literal finite maximum and every unchanged tree
average. The size threshold precedes both vectors, the scanner, and the
source entropy coefficient and exponent. No witness is selected here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 353--357, 399--404, and 868--877, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Filter
open Matrix
open scoped BigOperators

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals

open Classical in
/-- The source positive-prefix bound, at the same quantitative truncation,
gives the uniform actual pre-entropy bounds with the explicit `n^(-247)`
continuity loss at every `n` from the explicit threshold
`truncationEntropyThreshold q gap Cvol` on. Source: `08-scanner.tex`, lines 399--404 and
868--877. -/
theorem source_actualTerminal_preEntropy_bounds_of_truncationEntropyThreshold_le
    (q : ℕ) (hq : 1 ≤ q) (gap Cvol : ℝ) (hgap : 0 < gap) {n : ℕ}
    (hthr : truncationEntropyThreshold q gap Cvol ≤ n) :
    ∀ (I : Type) [Fintype I] [LinearOrder I] (Λ T : Finset (ℤ × ℤ))
      (hT : T.Nonempty) (S : CollarScan (Site Λ) I),
    S.n = n → S.graph = domainGraph Λ →
    S.depth = (fun x ↦ ambientDepth T hT x.val) →
    0 < S.n → 0 < S.K → S.r₀ ≤ S.D → 1 ≤ S.D → 4 * S.D ≤ S.m →
    ∀ L : ℕ, 8 * S.K * S.m ≤ L →
    (∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
    ∀ Ω Ωt : StateSpace Λ q, ‖Ω‖ = 1 → ‖Ωt‖ = 1 →
    ((depthPrefix S.A S.depth (L : ℤ)).card : ℝ) ≤ Cvol * (n : ℝ) ^ 2 →
    Matrix.traceDistance (Matrix.vecMulVec Ωt (star Ωt))
        (Matrix.vecMulVec Ω (star Ω)) ≤
      Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (gap / 4) / gap) →
    ∀ Ce η : ℝ,
    (∀ i : ℕ, i ≤ L →
      regionalEntropy Λ q Ω (positiveDepthPrefix S.A S.depth (i : ℤ)) ≤
        Ce * ((n : ℝ) * (L : ℝ) ^ η + n)) →
    let β := fun _ : Site Λ ↦ Fin q
    let X := S.A.filter fun x ↦ x.val ∈ T
    let σ := terminalPartition S (S.n * S.m)
    let gpre := fun j g ↦ FiniteProduct.entropy β Ωt (receiving (σ j g) false) +
      FiniteProduct.entropy β Ωt (receiving (σ j g) false ∪ middle (σ j g))ᶜ -
      FiniteProduct.entropy β Ωt (middle (σ j g))
    let gaps := (Finset.univ :
      Finset (terminalFamily S.K S.m S.M (S.n * S.m) × Fin S.K)).image
        (fun j ↦ gpre j.1 j.2)
    let gmax := (insert (0 : ℝ) gaps).max' (Finset.insert_nonempty _ _)
    let Bsh := Ce * ((n : ℝ) * (L : ℝ) ^ η + n) + (n : ℝ) ^ (-247 : ℝ)
    let B := 2 * regionalEntropy Λ q Ωt X +
      2 * Bsh + 6 * (n : ℝ) * (S.D : ℝ) * Real.log q
    0 ≤ gmax ∧ gmax ≤ max 0 B ∧
      ∀ tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m)),
        let Gpre := (∑ g, ∑ j, tree.weight j * gpre j g) / (S.K : ℝ)
        0 ≤ Gpre ∧ Gpre ≤ B := by
  classical
  have htransfer := regionalEntropy_positiveDepthPrefix_le_of_truncationEntropyThreshold_le
    q hq gap Cvol hgap hthr
  intro I _ _ Λ T hT S hSn hgraph hdepth hn hK hr hDpos hD
    L hL hrows Ω Ωt hΩ hΩt hcard htrace Ce η hsource β X σ gpre gaps gmax Bsh B
  have hsh : ∀ i : Fin (L + 1),
      regionalEntropy Λ q Ωt (positiveDepthPrefix S.A S.depth (i.val : ℤ)) ≤ Bsh := by
    intro i
    exact htransfer Λ Ω Ωt hΩ hΩt S.A S.depth L hcard htrace Ce η hsource
      i.val (Nat.le_of_lt_succ i.isLt)
  have hbound := terminalPartition_preEntropy_max_average_bounds hT S hgraph hdepth
    hn hK hr hDpos hD L hL hrows Ωt hΩt Bsh hsh
  simpa only [hSn] using hbound

open Classical in
/-- The source positive-prefix bound, at the same quantitative truncation,
gives the uniform actual pre-entropy bounds with the explicit `n^(-247)`
continuity loss. Source: `08-scanner.tex`, lines 868--877. -/
theorem eventually_source_actualTerminal_preEntropy_bounds
    (q : ℕ) (hq : 1 ≤ q) (gap Cvol : ℝ) (hgap : 0 < gap) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (I : Type) [Fintype I] [LinearOrder I] (Λ T : Finset (ℤ × ℤ))
        (hT : T.Nonempty) (S : CollarScan (Site Λ) I),
      S.n = n → S.graph = domainGraph Λ →
      S.depth = (fun x ↦ ambientDepth T hT x.val) →
      0 < S.n → 0 < S.K → S.r₀ ≤ S.D → 1 ≤ S.D → 4 * S.D ≤ S.m →
      ∀ L : ℕ, 8 * S.K * S.m ≤ L →
      (∀ d : ℕ, 1 ≤ d → d ≤ L →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
      ∀ Ω Ωt : StateSpace Λ q, ‖Ω‖ = 1 → ‖Ωt‖ = 1 →
      ((depthPrefix S.A S.depth (L : ℤ)).card : ℝ) ≤ Cvol * (n : ℝ) ^ 2 →
      Matrix.traceDistance (Matrix.vecMulVec Ωt (star Ωt))
          (Matrix.vecMulVec Ω (star Ω)) ≤
        Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (gap / 4) / gap) →
      ∀ Ce η : ℝ,
      (∀ i : ℕ, i ≤ L →
        regionalEntropy Λ q Ω (positiveDepthPrefix S.A S.depth (i : ℤ)) ≤
          Ce * ((n : ℝ) * (L : ℝ) ^ η + n)) →
      let β := fun _ : Site Λ ↦ Fin q
      let X := S.A.filter fun x ↦ x.val ∈ T
      let σ := terminalPartition S (S.n * S.m)
      let gpre := fun j g ↦ FiniteProduct.entropy β Ωt (receiving (σ j g) false) +
        FiniteProduct.entropy β Ωt (receiving (σ j g) false ∪ middle (σ j g))ᶜ -
        FiniteProduct.entropy β Ωt (middle (σ j g))
      let gaps := (Finset.univ :
        Finset (terminalFamily S.K S.m S.M (S.n * S.m) × Fin S.K)).image
          (fun j ↦ gpre j.1 j.2)
      let gmax := (insert (0 : ℝ) gaps).max' (Finset.insert_nonempty _ _)
      let Bsh := Ce * ((n : ℝ) * (L : ℝ) ^ η + n) + (n : ℝ) ^ (-247 : ℝ)
      let B := 2 * regionalEntropy Λ q Ωt X +
        2 * Bsh + 6 * (n : ℝ) * (S.D : ℝ) * Real.log q
      0 ≤ gmax ∧ gmax ≤ max 0 B ∧
        ∀ tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m)),
          let Gpre := (∑ g, ∑ j, tree.weight j * gpre j g) / (S.K : ℝ)
          0 ≤ Gpre ∧ Gpre ≤ B :=
  eventually_atTop.2 ⟨_, fun _ =>
    source_actualTerminal_preEntropy_bounds_of_truncationEntropyThreshold_le q hq gap Cvol hgap⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
