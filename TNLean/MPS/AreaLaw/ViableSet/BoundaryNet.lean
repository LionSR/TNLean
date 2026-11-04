/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.GluingCoordinates
import QICLean.Analysis.TraceNormNet

/-!
# A trace-norm net on the actual boundary space

At any cut of a chain, the intervening region has configuration dimension at most `q`.
For a bond of dimension `m ≤ D`, the trace-norm unit ball of boundary matrices therefore
has an `η`-net with at most `(2 ⌈(q D)²/η⌉ + 1)^(2(q D)²)` elements. The net is on the
actual boundary space, without extending the bond to dimension `D`.

This is the chain specialization of the net in Landau, Vazirani and Vidick,
arXiv:1307.5143v1, Lemma 2.4, `algo53.tex`, lines 451–460.

**Local fix (net cardinality):** A complex square matrix of size `c` has `2c²` real
coordinates, in place of the source's printed exponent `2c`. Here `c ≤ q D`.
The corrected grid size and step are documented in the QICLean note
https://sirui-lu.com/QICLean/paper-gaps/lvv13_trace_norm_net.pdf.
-/

open Matrix

namespace TNLean.MPS.AreaLaw

variable {L q k m D : ℕ}

/-- A trace-norm `η`-net on the unit ball of the `n × n` complex matrices, chosen once for
every positive radius, and empty otherwise. QICLean's net theorem supplies the choice.
Source: LVV13, arXiv:1307.5143v1, Lemma 2.4, `algo53.tex`, lines 451–460. -/
noncomputable def rectangularTraceNormNet (n : Type*) [Fintype n] [DecidableEq n] (η : ℝ) :
    Finset (Matrix n n ℂ) :=
  if hη : 0 < η then
    Classical.choose (Matrix.exists_finset_rectangularTraceNorm_net (n := n) hη)
  else ∅

/-- The cardinality bound of the chosen net. -/
theorem card_rectangularTraceNormNet_le {n : Type*} [Fintype n] [DecidableEq n] {η : ℝ}
    (hη : 0 < η) :
    (rectangularTraceNormNet n η).card ≤
      (2 * ⌈(Fintype.card n : ℝ) ^ 2 / η⌉₊ + 1) ^ (2 * Fintype.card n ^ 2) := by
  simp only [rectangularTraceNormNet, hη, ↓reduceDIte]
  exact (Classical.choose_spec (Matrix.exists_finset_rectangularTraceNorm_net (n := n) hη)).1

/-- Every matrix of trace norm at most one is within `η` of a point of the chosen net. -/
theorem exists_mem_rectangularTraceNormNet {n : Type*} [Fintype n] [DecidableEq n] {η : ℝ}
    (hη : 0 < η) (Y : Matrix n n ℂ) (hY : rectangularTraceNorm Y ≤ 1) :
    ∃ X ∈ rectangularTraceNormNet n η, rectangularTraceNorm (Y - X) ≤ η := by
  simp only [rectangularTraceNormNet, hη, ↓reduceDIte]
  exact (Classical.choose_spec (Matrix.exists_finset_rectangularTraceNorm_net (n := n) hη)).2
    Y hY

/-- On the actual site-and-bond boundary space of a bond of dimension `m ≤ D`, the chosen
net has at most `(2 ⌈(q D)²/η⌉ + 1)^(2(q D)²)` points. Chain form of LVV13,
arXiv:1307.5143v1, Lemma 2.4, `algo53.tex`, lines 451–460, with the corrections documented
in the module docstring. -/
theorem card_boundary_rectangularTraceNormNet_le (hq : 1 ≤ q) {η : ℝ} (hη : 0 < η)
    (hm : m ≤ D) :
    (rectangularTraceNormNet (CutSite L q k × Fin m) η).card ≤
      (2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / η⌉₊ + 1) ^ (2 * (q * D) ^ 2) := by
  classical
  refine (card_rectangularTraceNormNet_le hη).trans ?_
  have hdim : Fintype.card (CutSite L q k × Fin m) ≤ q * D := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      Nat.mul_le_mul (card_cutSite_le (L := L) (k := k) hq) hm
  have hsq := Nat.pow_le_pow_left hdim 2
  have hceil : ⌈(Fintype.card (CutSite L q k × Fin m) : ℝ) ^ 2 / η⌉₊ ≤
      ⌈((q * D : ℕ) : ℝ) ^ 2 / η⌉₊ :=
    Nat.ceil_mono (div_le_div_of_nonneg_right (by exact_mod_cast hsq) hη.le)
  exact pow_le_pow (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hceil) 1)
    (Nat.succ_le_succ (Nat.zero_le _)) (Nat.mul_le_mul_left 2 hsq)

/-- A finite trace-norm net on the actual site-and-bond boundary space, with a cardinality
bound depending on an upper bound for the bond dimension: the existence form of the chosen
net `rectangularTraceNormNet`. Chain form of LVV13, arXiv:1307.5143v1, Lemma 2.4,
`algo53.tex`, lines 451–460, with the corrections documented in the module docstring. -/
theorem exists_finset_boundary_rectangularTraceNorm_net (hq : 1 ≤ q) {η : ℝ}
    (hη : 0 < η) (hm : m ≤ D) :
    ∃ N : Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ),
      N.card ≤ (2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / η⌉₊ + 1) ^ (2 * (q * D) ^ 2) ∧
      ∀ Y : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ,
        rectangularTraceNorm Y ≤ 1 → ∃ X ∈ N, rectangularTraceNorm (Y - X) ≤ η := by
  classical
  exact ⟨rectangularTraceNormNet (CutSite L q k × Fin m) η,
    card_boundary_rectangularTraceNormNet_le hq hη hm,
    fun Y hY ↦ exists_mem_rectangularTraceNormNet hη Y hY⟩

end TNLean.MPS.AreaLaw
