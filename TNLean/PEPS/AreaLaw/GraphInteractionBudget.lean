/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Counting interaction supports and their local weights

There is one interaction term per finite support. A support containing a specified site is
determined by deleting that site. If every such support lies in a finite neighborhood, this
gives a power-set bound independent of the cardinality of the full system.

Nonnegative interaction weights meeting a region are bounded by summing the site budgets.
The resulting bound also permits repeated visits to the same support in an interaction chain;
only the original family of supports is counted without multiplicity.

These are independently written combinatorial ingredients for the September 24, 2026
area-law manuscript, Section 2 (local counting) and Section 4, equation
`eq:quasilocal-budget`. No OpenAI Lean proof text is copied or adapted.
No spectral-gap, entropy, or connectedness assumption is used.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Sections 2 and 4; source revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators

/-!
## Declaration provenance

Provenance-ID: 8745-tnlean.peps.arealaw.card_supportfamily_le_pow_card_erase
Downstream declaration: TNLean.PEPS.AreaLaw.card_supportFamily_le_pow_card_erase
Provenance-ID: 8745-tnlean.peps.arealaw.card_supportfamily_le_pow
Downstream declaration: TNLean.PEPS.AreaLaw.card_supportFamily_le_pow
Provenance-ID: 8745-tnlean.peps.arealaw.sum_supportweights_containing_le
Downstream declaration: TNLean.PEPS.AreaLaw.sum_supportWeights_containing_le
Provenance-ID: 8745-tnlean.peps.arealaw.sum_supportweights_meeting_le_sum_siteweights
Downstream declaration: TNLean.PEPS.AreaLaw.sum_supportWeights_meeting_le_sum_siteWeights
Provenance-ID: 8745-tnlean.peps.arealaw.sum_supportweights_meeting_le
Downstream declaration: TNLean.PEPS.AreaLaw.sum_supportWeights_meeting_le
Provenance-ID: 8745-tnlean.peps.arealaw.interactionchainweightsum
Downstream declaration: TNLean.PEPS.AreaLaw.interactionChainWeightSum
Provenance-ID: 8745-tnlean.peps.arealaw.interactionchainweightsum_le_pow
Downstream declaration: TNLean.PEPS.AreaLaw.interactionChainWeightSum_le_pow
Source: September 24, 2026.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/01-preliminaries.tex
Labels: eq:ball-count.
Source: September 24, 2026.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/03-quasilocal.tex
Labels: eq:quasilocal-budget, lem:quasilocal-lr.
Independently formalized; no upstream Lean proof text reused.
These are auxiliary graph and counting results, not the complete propagation or area-law theorem.
-/

namespace TNLean.PEPS.AreaLaw

variable {V : Type*} [DecidableEq V]

/-- Distinct supports containing a site give distinct subsets after that site is removed.
This is the support-counting argument in Section 2 of the area-law manuscript. -/
theorem card_supportFamily_le_pow_card_erase (F : Finset (Finset V)) (B : Finset V) (a : V)
    (hF : ∀ X ∈ F, a ∈ X ∧ X ⊆ B) : F.card ≤ 2 ^ (B.erase a).card := by
  have hinj : Set.InjOn (fun X : Finset V => X.erase a) F := by
    intro X hX Y hY hXY
    calc
      X = insert a (X.erase a) := (Finset.insert_erase (hF X hX).1).symm
      _ = insert a (Y.erase a) := congrArg (insert a) hXY
      _ = Y := Finset.insert_erase (hF Y hY).1
  have hsub : F.image (fun X => X.erase a) ⊆ (B.erase a).powerset := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
    apply Finset.mem_powerset.mpr
    intro x hx
    obtain ⟨hxa, hxY⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_erase.mpr ⟨hxa, (hF Y hY).2 hxY⟩
  calc
    F.card = (F.image (fun X => X.erase a)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (B.erase a).powerset.card := Finset.card_le_card hsub
    _ = 2 ^ (B.erase a).card := Finset.card_powerset _

omit [DecidableEq V] in
/-- At most $2^{|B|-1}$ supports in a neighborhood contain its specified site.
The neighborhood includes the site, so the exponent also covers singleton neighborhoods. -/
theorem card_supportFamily_le_pow (F : Finset (Finset V)) (B : Finset V) (a : V)
    (ha : a ∈ B) (hF : ∀ X ∈ F, a ∈ X ∧ X ⊆ B) :
    F.card ≤ 2 ^ (B.card - 1) := by
  classical
  simpa only [Finset.card_erase_of_mem ha] using
    card_supportFamily_le_pow_card_erase F B a hF

/-- The sum of weights of supports containing a site is bounded by the number of possible
supports times the bound on each term. This applies to operator norms without requiring the
terms to be Hermitian. -/
theorem sum_supportWeights_containing_le (F : Finset (Finset V)) (B : Finset V) (a : V)
    (w : Finset V → ℝ) (J : ℝ) (hJ : 0 ≤ J) (ha : a ∈ B)
    (hB : ∀ X ∈ F, a ∈ X → X ⊆ B) (hw : ∀ X ∈ F, w X ≤ J) :
    (∑ X ∈ F.filter (fun X => a ∈ X), w X) ≤ (2 ^ (B.card - 1) : ℕ) * J := by
  have hcard : (F.filter (fun X => a ∈ X)).card ≤ 2 ^ (B.card - 1) := by
    apply card_supportFamily_le_pow _ B a ha
    intro X hX
    obtain ⟨hXF, haX⟩ := Finset.mem_filter.mp hX
    exact ⟨haX, hB X hXF haX⟩
  calc
    (∑ X ∈ F.filter (fun X => a ∈ X), w X) ≤
        ∑ X ∈ F.filter (fun X => a ∈ X), J := by
      apply Finset.sum_le_sum
      intro X hX
      exact hw X (Finset.mem_filter.mp hX).1
    _ = ((F.filter (fun X => a ∈ X)).card : ℝ) * J := by simp
    _ ≤ (2 ^ (B.card - 1) : ℕ) * J := by
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hJ

/-- A nonnegative weight on each support is counted at least once by the sites it meets.
Only the weights of the original supports occur; no multiplicity of interaction labels is
allowed in the family. -/
theorem sum_supportWeights_meeting_le_sum_siteWeights (F : Finset (Finset V)) (S : Finset V)
    (w : Finset V → ℝ) (hw : ∀ X ∈ F, 0 ≤ w X) :
    (∑ X ∈ F.filter (fun X => ¬ Disjoint X S), w X) ≤
      ∑ a ∈ S, ∑ X ∈ F.filter (fun X => a ∈ X), w X := by
  classical
  rw [Finset.sum_filter]
  calc
    (∑ X ∈ F, if ¬ Disjoint X S then w X else 0) ≤
        ∑ X ∈ F, ∑ a ∈ S, if a ∈ X then w X else 0 := by
      apply Finset.sum_le_sum
      intro X hX
      by_cases hXS : Disjoint X S
      · simp only [hXS, not_true_eq_false, ite_false]
        exact Finset.sum_nonneg fun a _ => by split_ifs <;> first | exact hw X hX | rfl
      · obtain ⟨a, haX, haS⟩ := Finset.not_disjoint_iff.mp hXS
        simp only [hXS, not_false_eq_true, ite_true]
        calc
          w X = (if a ∈ X then w X else 0) := by simp [haX]
          _ ≤ ∑ b ∈ S, if b ∈ X then w X else 0 := by
            apply Finset.single_le_sum (fun b _ => ?_) haS
            split_ifs <;> first | exact hw X hX | rfl
    _ = ∑ a ∈ S, ∑ X ∈ F.filter (fun X => a ∈ X), w X := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_filter]

/-- A uniform per-site interaction budget gives a budget proportional to the cardinality
of any region. This is the step giving $κ = v_R b₀$ in Section 4 of the area-law manuscript. -/
theorem sum_supportWeights_meeting_le (F : Finset (Finset V)) (S : Finset V)
    (w : Finset V → ℝ) (b : ℝ) (hw : ∀ X ∈ F, 0 ≤ w X)
    (hb : ∀ a ∈ S, (∑ X ∈ F.filter (fun X => a ∈ X), w X) ≤ b) :
    (∑ X ∈ F.filter (fun X => ¬ Disjoint X S), w X) ≤ S.card * b := by
  calc
    (∑ X ∈ F.filter (fun X => ¬ Disjoint X S), w X) ≤
        ∑ a ∈ S, ∑ X ∈ F.filter (fun X => a ∈ X), w X :=
      sum_supportWeights_meeting_le_sum_siteWeights F S w hw
    _ ≤ ∑ _a ∈ S, b := Finset.sum_le_sum hb
    _ = S.card * b := by simp

/-- Total weight of all length-$n$ continuations of an interaction chain beginning at $X$.
Each next support must intersect the current support; repeated supports are permitted.
This is the finite chain sum used in Section 4 of the area-law manuscript. -/
def interactionChainWeightSum (F : Finset (Finset V)) (w : Finset V → ℝ)
    (X : Finset V) : ℕ → ℝ
  | 0 => 1
  | n + 1 => ∑ Y ∈ F.filter (fun Y => ¬ Disjoint Y X),
      w Y * interactionChainWeightSum F w Y n

/-- Local site budgets bound the total interaction-chain weight by $κ^n$, where
$κ = v b$, when every original support contains at most $v$ sites.
The estimate is independent of the number of original supports. -/
theorem interactionChainWeightSum_le_pow (F : Finset (Finset V)) (w : Finset V → ℝ)
    (v : ℕ) (b : ℝ) (hb : 0 ≤ b) (hw : ∀ X ∈ F, 0 ≤ w X)
    (hcard : ∀ X ∈ F, X.card ≤ v)
    (hsite : ∀ a : V, (∑ Y ∈ F.filter (fun Y => a ∈ Y), w Y) ≤ b)
    (n : ℕ) (X : Finset V) (hX : X ∈ F) :
    interactionChainWeightSum F w X n ≤ ((v : ℝ) * b) ^ n := by
  induction n generalizing X with
  | zero => simp [interactionChainWeightSum]
  | succ n ih =>
    have hκ : 0 ≤ (v : ℝ) * b := mul_nonneg (Nat.cast_nonneg v) hb
    have hrow : (∑ Y ∈ F.filter (fun Y => ¬ Disjoint Y X), w Y) ≤ (v : ℝ) * b := by
      calc
        (∑ Y ∈ F.filter (fun Y => ¬ Disjoint Y X), w Y) ≤ X.card * b :=
          sum_supportWeights_meeting_le F X w b hw (fun a _ => hsite a)
        _ ≤ (v : ℝ) * b :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard X hX)) hb
    calc
      interactionChainWeightSum F w X (n + 1) =
          ∑ Y ∈ F.filter (fun Y => ¬ Disjoint Y X),
            w Y * interactionChainWeightSum F w Y n := rfl
      _ ≤ ∑ Y ∈ F.filter (fun Y => ¬ Disjoint Y X), w Y * ((v : ℝ) * b) ^ n := by
        apply Finset.sum_le_sum
        intro Y hY
        have hYF := (Finset.mem_filter.mp hY).1
        exact mul_le_mul_of_nonneg_left (ih Y hYF) (hw Y hYF)
      _ = (∑ Y ∈ F.filter (fun Y => ¬ Disjoint Y X), w Y) * ((v : ℝ) * b) ^ n :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ ((v : ℝ) * b) * ((v : ℝ) * b) ^ n :=
        mul_le_mul_of_nonneg_right hrow (pow_nonneg hκ n)
      _ = ((v : ℝ) * b) ^ (n + 1) := by rw [pow_succ, mul_comm]

end TNLean.PEPS.AreaLaw
