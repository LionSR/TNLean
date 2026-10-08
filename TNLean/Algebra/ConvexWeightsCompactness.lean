/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.Complex.Basic
/-!
# Compactness of finite convex weights

A sequence of uniformly bounded nonnegative weights whose total mass tends
to one has a subsequence converging to normalized convex weights. A single
such subsequence identifies all test evaluations simultaneously; the test
family need not be countable. These are general finite-dimensional
compactness statements, with no tensor-network hypotheses.
-/

open Filter
open scoped Topology

variable {ι : Type*} [Fintype ι]

/-- Eventually bounded nonnegative weights with asymptotic total mass one
have a subsequence converging to normalized convex weights. -/
theorem exists_convex_weights_subsequence
    (w : ℕ → ι → ℝ)
    (hw : ∀ᶠ n in atTop, ∀ j, 0 ≤ w n j ∧ w n j ≤ 1)
    (hsum : Tendsto (fun n => ∑ j, w n j) atTop (𝓝 1)) :
    ∃ p : ι → ℝ, (∀ j, 0 ≤ p j) ∧ (∑ j, p j = 1) ∧
      ∃ s : ℕ → ℕ, StrictMono s ∧ Tendsto (w ∘ s) atTop (𝓝 p) := by
  obtain ⟨p, hp, s, hs, hlim⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ι → ℝ) 1)).tendsto_subseq'
      (hw.mono (fun n hn => ⟨fun j => (hn j).1, fun j => (hn j).2⟩)).frequently
  refine ⟨p, hp.1, ?_, s, hs, hlim⟩
  have hsumlim : Tendsto (fun n => ∑ j, w (s n) j) atTop (𝓝 (∑ j, p j)) :=
    tendsto_finsetSum _ (fun j _ => (continuous_apply j).tendsto p |>.comp hlim)
  exact tendsto_nhds_unique hsumlim (hsum.comp hs.tendsto_atTop)

/-- Approximation of every test evaluation by the same finite sequence of
weights yields one exact convex representation for all tests. -/
theorem exists_convex_weights_of_approximate_evaluations
    {α : Type*} (f : α → ℂ) (g : ι → α → ℂ) (w : ℕ → ι → ℝ)
    (hw : ∀ᶠ n in atTop, ∀ j, 0 ≤ w n j ∧ w n j ≤ 1)
    (hsum : Tendsto (fun n => ∑ j, w n j) atTop (𝓝 1))
    (heval : ∀ x, Tendsto (fun n => f x - ∑ j, (w n j : ℂ) * g j x)
      atTop (𝓝 0)) :
    ∃ p : ι → ℝ, (∀ j, 0 ≤ p j) ∧ (∑ j, p j = 1) ∧
      ∀ x, f x = ∑ j, (p j : ℂ) * g j x := by
  obtain ⟨p, hp, hpsum, s, hs, hlim⟩ := exists_convex_weights_subsequence w hw hsum
  refine ⟨p, hp, hpsum, ?_⟩
  intro x
  have hsumlim : Tendsto (fun n => ∑ j, (w (s n) j : ℂ) * g j x) atTop
      (𝓝 (∑ j, (p j : ℂ) * g j x)) :=
    tendsto_finsetSum _ (fun j _ =>
      (Complex.continuous_ofReal.tendsto (p j) |>.comp
        ((continuous_apply j).tendsto p |>.comp hlim)).mul_const (g j x))
  exact sub_eq_zero.mp (tendsto_nhds_unique
    (tendsto_const_nhds.sub hsumlim) ((heval x).comp hs.tendsto_atTop))
