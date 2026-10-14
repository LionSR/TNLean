/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualTerminalPrefixEntropy
import TNLean.PEPS.AreaLaw.Scan.ActualTerminalCollarGeometry
import Mathlib.Tactic.FieldSimp

/-!
# Uniform bounds on the actual sharp pre-comparison entropy

Subadditivity, purity, and the actual positive-prefix approximation give
`0 ≤ gpre ≤ 2S(X) + 2Bsh + 6nD log q`. This bound controls the exact finite
maximum and the unchanged terminal-tree/band average used in the sharp
comparison. The source positive-prefix bound remains explicit.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 868--877, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals

open Classical in
/-- Bounds on the literal pre-comparison entropy at each actual terminal.
The lower bound uses subadditivity on the near and far regions, whose union
is the complement of the middle region. Source: `08-scanner.tex`, 868--877. -/
theorem terminalPartition_preEntropy_bounds
    {I : Type} [Fintype I] [LinearOrder I] {Λ T : Finset (ℤ × ℤ)} {q : ℕ}
    (hT : T.Nonempty) (S : CollarScan (Site Λ) I)
    (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hn : 0 < S.n) (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (L : ℕ) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (Ωt : StateSpace Λ q) (hΩt : ‖Ωt‖ = 1) (Bsh : ℝ)
    (hsh : ∀ i : Fin (L + 1),
      regionalEntropy Λ q Ωt (positiveDepthPrefix S.A S.depth (i.val : ℤ)) ≤ Bsh)
    (j : terminalFamily S.K S.m S.M (S.n * S.m)) (g : Fin S.K) :
    let β := fun _ : Site Λ ↦ Fin q
    let X := S.A.filter fun x ↦ x.val ∈ T
    let σ := terminalPartition S (S.n * S.m) j g
    let Q := receiving σ false
    let Y := middle σ
    let gpre := FiniteProduct.entropy β Ωt Q +
      FiniteProduct.entropy β Ωt (Q ∪ Y)ᶜ - FiniteProduct.entropy β Ωt Y
    0 ≤ gpre ∧ gpre ≤ 2 * regionalEntropy Λ q Ωt X +
      2 * Bsh + 6 * (S.n : ℝ) * (S.D : ℝ) * Real.log q := by
  classical
  intro β X σ Q Y gpre
  let U := positiveNear S.depth σ
  let V := receiving σ true
  obtain ⟨hnear, hUYeq, hfar, hXU, hXY, hXV, _, hUV, _, _, _⟩ :=
    terminalPartition_collar_geometry hT S hdepth (S.n * S.m) L hL j g
  have hQV : Disjoint Q V := by
    refine Finset.disjoint_left.mpr fun x hx hv ↦ ?_
    rw [hnear] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.disjoint_left.mp hXV hx hv
    · exact Finset.disjoint_left.mp hUV hx hv
  have hQVeq : Q ∪ V = Yᶜ := by
    ext x
    cases hx : σ x with
    | none => simp [Q, V, Y, receiving, middle, hx]
    | some side => cases side <;> simp [Q, V, Y, receiving, middle, hx]
  have hnonneg := FiniteProduct.entropy_union_le β Ωt hΩt Q V hQV
  rw [hQVeq, FiniteProduct.entropy_compl] at hnonneg
  have hpreEq : gpre = FiniteProduct.entropy β Ωt (X ∪ U) +
      FiniteProduct.entropy β Ωt (X ∪ (U ∪ Y)) - FiniteProduct.entropy β Ωt Y := by
    simp only [gpre, Q, hnear, U, FiniteProduct.entropy_compl, Finset.union_assoc]
  have hXUY : Disjoint X (U ∪ Y) := Finset.disjoint_left.mpr fun x hx hu ↦ by
    rcases Finset.mem_union.mp hu with hu | hy
    · exact Finset.disjoint_left.mp hXU hx hu
    · exact Finset.disjoint_left.mp hXY hx hy
  have hN := FiniteProduct.entropy_union_le β Ωt hΩt X U hXU
  have hF := FiniteProduct.entropy_union_le β Ωt hΩt X (U ∪ Y) hXUY
  obtain ⟨hU, hUY⟩ := terminalPartition_positiveEntropy_le hT S hgraph hdepth hn hr
    hDpos hD L hL hrows Ωt hΩt Bsh hsh j g
  have hY := regionalEntropy_nonneg Λ q Ωt hΩt Y
  rw [← hUYeq] at hUY
  simp only [regionalEntropy_eq_finiteProduct] at hU hUY hY ⊢
  constructor
  · have hV : FiniteProduct.entropy β Ωt V = FiniteProduct.entropy β Ωt (Q ∪ Y)ᶜ := by
      rw [hfar]
    dsimp only [gpre]
    rw [← hV]
    linarith
  · rw [hpreEq]
    linarith

open Classical in
/-- The literal finite maximum and every actual terminal-tree average obey
the same uniform bound. In particular, no independent leaf distribution is
introduced. Source: `08-scanner.tex`, lines 868--890. -/
theorem terminalPartition_preEntropy_max_average_bounds
    {I : Type} [Fintype I] [LinearOrder I] {Λ T : Finset (ℤ × ℤ)} {q : ℕ}
    (hT : T.Nonempty) (S : CollarScan (Site Λ) I)
    (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hn : 0 < S.n) (hK : 0 < S.K)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (L : ℕ) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (Ωt : StateSpace Λ q) (hΩt : ‖Ωt‖ = 1) (Bsh : ℝ)
    (hsh : ∀ i : Fin (L + 1),
      regionalEntropy Λ q Ωt (positiveDepthPrefix S.A S.depth (i.val : ℤ)) ≤ Bsh) :
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
    let B := 2 * regionalEntropy Λ q Ωt X +
      2 * Bsh + 6 * (S.n : ℝ) * (S.D : ℝ) * Real.log q
    0 ≤ gmax ∧ gmax ≤ max 0 B ∧
      ∀ tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m)),
        let Gpre := (∑ g, ∑ j, tree.weight j * gpre j g) / (S.K : ℝ)
        0 ≤ Gpre ∧ Gpre ≤ B := by
  classical
  intro β X σ gpre gaps gmax B
  have hb := terminalPartition_preEntropy_bounds hT S hgraph hdepth hn hr hDpos hD
    L hL hrows Ωt hΩt Bsh hsh
  refine ⟨Finset.le_max' _ _ (Finset.mem_insert_self _ _), ?_, ?_⟩
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_max_left _ _
    · obtain ⟨⟨j, g⟩, _, rfl⟩ := Finset.mem_image.mp hx
      exact (hb j g).2.trans (le_max_right _ _)
  · intro tree Gpre
    have hKr : (0 : ℝ) < S.K := Nat.cast_pos.mpr hK
    constructor
    · exact div_nonneg (Finset.sum_nonneg fun g _ ↦ Finset.sum_nonneg fun j _ ↦
        mul_nonneg (tree.weight_nonneg j) (hb j g).1) hKr.le
    · apply (div_le_iff₀ hKr).mpr
      calc
        (∑ g, ∑ j, tree.weight j * gpre j g) ≤ ∑ _g : Fin S.K, B := by
          apply Finset.sum_le_sum
          intro g _
          calc
            (∑ j, tree.weight j * gpre j g) ≤ ∑ j, tree.weight j * B :=
              Finset.sum_le_sum fun j _ ↦
                mul_le_mul_of_nonneg_left (hb j g).2 (tree.weight_nonneg j)
            _ = B := by rw [← Finset.sum_mul, tree.sum_weight, one_mul]
        _ = B * (S.K : ℝ) := by simp only [Finset.sum_const, Fintype.card_fin,
          nsmul_eq_mul, mul_comm]

end TNLean.PEPS.AreaLaw.Scan.CollarScan
