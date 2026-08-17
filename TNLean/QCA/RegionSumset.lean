/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.Translation

/-!
# Sumsets of finite spin-chain regions

For finite regions \(\Lambda, \mathcal N \subset \mathbb Z\), this file records the finite
sumset \(\Lambda + \mathcal N\) used to state the propagation condition for a quantum cellular
automaton. The construction is Mathlib's pointwise addition on finite sets.

This file concerns only finite regions. It does not define propagation predicates, maps on local
observable algebras, or quantum cellular automata.

## Main definitions

* `SpinChain.regionSumset` — the pointwise sum \(\Lambda + \mathcal N\) of finite regions.

## Main results

* `SpinChain.mem_regionSumset` — membership in a finite-region sumset.
* `SpinChain.disjoint_regionSumset_neg_iff` — reflected sumsets exchange disjointness.
* `SpinChain.regionSumset_singleton_right` — addition by a singleton is `translateRegion`.
* `SpinChain.regionSumset_mono` — the sumset is monotone in both regions.
* `SpinChain.regionSumset_assoc` — finite-region sumsets are associative.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2292--2298.
* Schumacher--Werner, quant-ph/0405174, Definition 1.
-/

open scoped Pointwise

namespace SpinChain

/-- The finite-region sumset \(\Lambda + \mathcal N\), formed using pointwise addition on
`Finset ℤ`.

This is the region appearing in the finite-propagation condition
\(\omega(\mathcal A_\Lambda) \subseteq \mathcal A_{\Lambda + \mathcal N}\).
Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
abbrev regionSumset (Λ 𝓝 : Finset ℤ) : Finset ℤ :=
  Λ + 𝓝

/-- A site belongs to \(\Lambda + \mathcal N\) exactly when it is the sum of a site in
\(\Lambda\) and a displacement in \(\mathcal N\).

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
lemma mem_regionSumset (i : ℤ) (Λ 𝓝 : Finset ℤ) :
    i ∈ regionSumset Λ 𝓝 ↔ ∃ j ∈ Λ, ∃ a ∈ 𝓝, j + a = i :=
  Finset.mem_add

/-- A region \(\Gamma\) is disjoint from \(\Lambda+(-\mathcal N)\) if and only if
\(\Gamma+\mathcal N\) is disjoint from \(\Lambda\).

This is elementary finite-region arithmetic for reflected neighborhoods. -/
lemma disjoint_regionSumset_neg_iff {Γ Λ 𝓝 : Finset ℤ} :
    Disjoint Γ (regionSumset Λ (-𝓝)) ↔ Disjoint (regionSumset Γ 𝓝) Λ := by
  constructor
  · intro h
    rw [Finset.disjoint_left] at h ⊢
    intro z hz hzΛ
    obtain ⟨g, hg, n, hn, hgn⟩ := (mem_regionSumset z Γ 𝓝).mp hz
    apply h hg
    rw [mem_regionSumset]
    refine ⟨z, hzΛ, -n, Finset.neg_mem_neg hn, ?_⟩
    rw [← hgn]
    simp
  · intro h
    rw [Finset.disjoint_left] at h ⊢
    intro g hg hgsum
    obtain ⟨z, hz, n, hn, hzng⟩ := (mem_regionSumset g Λ (-𝓝)).mp hgsum
    obtain ⟨m, hm, rfl⟩ := Finset.mem_neg.mp hn
    apply h ((mem_regionSumset z Γ 𝓝).mpr ⟨g, hg, m, hm, ?_⟩) hz
    rw [← hzng]
    simp

/-- Adding the singleton displacement region \(\{a\}\) agrees with translation by \(a\).

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
@[simp]
lemma regionSumset_singleton_right (Λ : Finset ℤ) (a : ℤ) :
    regionSumset Λ {a} = translateRegion a Λ := by
  ext i
  constructor
  · rw [mem_regionSumset]
    rintro ⟨j, hj, b, hb, rfl⟩
    rw [Finset.mem_singleton] at hb
    subst b
    simpa using hj
  · rw [mem_translateRegion]
    intro hi
    rw [mem_regionSumset]
    exact ⟨i - a, hi, a, Finset.mem_singleton_self a, by simp⟩

/-- The finite-region sumset is monotone in both arguments.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
lemma regionSumset_mono {Λ Γ 𝓝 𝓜 : Finset ℤ} (hΛ : Λ ⊆ Γ) (h𝓝 : 𝓝 ⊆ 𝓜) :
    regionSumset Λ 𝓝 ⊆ regionSumset Γ 𝓜 :=
  Finset.add_subset_add hΛ h𝓝

/-- Enlarging the first region enlarges its sumset with a fixed displacement region.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
lemma regionSumset_mono_left {Λ Γ : Finset ℤ} (𝓝 : Finset ℤ) (h : Λ ⊆ Γ) :
    regionSumset Λ 𝓝 ⊆ regionSumset Γ 𝓝 :=
  Finset.add_subset_add_right h

/-- Enlarging the displacement region enlarges the sumset with a fixed first region.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
lemma regionSumset_mono_right (Λ : Finset ℤ) {𝓝 𝓜 : Finset ℤ} (h : 𝓝 ⊆ 𝓜) :
    regionSumset Λ 𝓝 ⊆ regionSumset Λ 𝓜 :=
  Finset.add_subset_add_left h

/-- The sumset with an empty first region is empty.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
lemma regionSumset_empty_left (𝓝 : Finset ℤ) : regionSumset ∅ 𝓝 = ∅ :=
  Finset.empty_add 𝓝

/-- The sumset with an empty displacement region is empty.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
lemma regionSumset_empty_right (Λ : Finset ℤ) : regionSumset Λ ∅ = ∅ :=
  Finset.add_empty Λ

/-- The singleton zero region is a left identity for finite-region sumsets.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
@[simp]
lemma regionSumset_zero_left (𝓝 : Finset ℤ) : regionSumset {0} 𝓝 = 𝓝 := by
  change (0 : Finset ℤ) + 𝓝 = 𝓝
  exact zero_add 𝓝

/-- The singleton zero region is a right identity for finite-region sumsets.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
@[simp]
lemma regionSumset_zero_right (Λ : Finset ℤ) : regionSumset Λ {0} = Λ := by
  change Λ + (0 : Finset ℤ) = Λ
  exact add_zero Λ

/-- Translating the first region translates its sumset by the same displacement.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
lemma regionSumset_translateRegion_left (a : ℤ) (Λ 𝓝 : Finset ℤ) :
    regionSumset (translateRegion a Λ) 𝓝 = translateRegion a (regionSumset Λ 𝓝) := by
  rw [← regionSumset_singleton_right, ← regionSumset_singleton_right]
  change (Λ + {a}) + 𝓝 = (Λ + 𝓝) + {a}
  ac_rfl

/-- Translating the displacement region translates the sumset by the same displacement.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
lemma regionSumset_translateRegion_right (a : ℤ) (Λ 𝓝 : Finset ℤ) :
    regionSumset Λ (translateRegion a 𝓝) = translateRegion a (regionSumset Λ 𝓝) := by
  rw [← regionSumset_singleton_right, ← regionSumset_singleton_right]
  change Λ + (𝓝 + {a}) = (Λ + 𝓝) + {a}
  ac_rfl

/-- Finite-region sumsets are associative.

This law supports composition of finite-propagation bounds.
Source: arXiv:1703.09188, Appendix, line 2298. -/
lemma regionSumset_assoc (Λ 𝓝 𝓜 : Finset ℤ) :
    regionSumset (regionSumset Λ 𝓝) 𝓜 = regionSumset Λ (regionSumset 𝓝 𝓜) :=
  add_assoc Λ 𝓝 𝓜

end SpinChain
