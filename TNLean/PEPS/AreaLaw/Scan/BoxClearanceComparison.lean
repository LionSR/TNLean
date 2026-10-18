/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BoxEntropySupremum

/-!
# Reducing the clearance in a safe-box entropy bound

For an integer clearance at least three, split each rectangle of size at least
two into at most four smaller rectangles. Each smaller rectangle has the next
integer clearance. Subadditivity therefore transfers a uniform entropy power
bound to the original clearance without changing its exponent. The volume
entropy bound covers the remaining sizes.

This is the clearance comparison used to pass from integer safe-box estimates
to real template clearances in the collar argument.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`02-initial.tex`, lines 220–228 and 590–594; `08-scanner.tex`, Proposition 9.6,
lines 808–827, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The comparison is a derived auxiliary result.
-/

open scoped BigOperators
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

private theorem half_size_clearance {D s : ℕ} (hD : 3 ≤ D) (hs : 2 ≤ s) :
    (D + 1) * ((s + 1) / 2) ≤ D * s := by
  have hr : (s + 1) / 2 ≤ 3 * (s - (s + 1) / 2) := by omega
  have hDr : (s + 1) / 2 ≤ D * (s - (s + 1) / 2) :=
    hr.trans (Nat.mul_le_mul_right _ hD)
  have hrle : (s + 1) / 2 ≤ s := by omega
  calc
    (D + 1) * ((s + 1) / 2) = D * ((s + 1) / 2) + (s + 1) / 2 := by ring
    _ ≤ D * ((s + 1) / 2) + D * (s - (s + 1) / 2) := Nat.add_le_add_left hDr _
    _ = D * s := by rw [← Nat.mul_add, Nat.add_sub_of_le hrle]

/-- A uniform box-entropy power bound at clearance D+1 gives a bound with
that same exponent at clearance D≥3. The existing rectangle children split
each large rectangle into at most four pieces; the volume bound covers the
remaining sizes. This derived comparison is used to pass from integer-clearance box estimates
to the real clearances in area-law Proposition 9.6, `08-scanner.tex`, lines 808–827,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem boxEntropy_power_le_of_succ_clearance
    {q R D : ℕ} (hq : 1 ≤ q) (hD : 3 ≤ D)
    {J Δ C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hbox : ∀ r : ℕ, 1 ≤ r →
      boxEntropy q R J Δ (D + 1) r ≤ C * (r : ℝ) ^ p) :
    ∀ r : ℕ, 1 ≤ r →
      boxEntropy q R J Δ D r ≤
        (4 * C + 4 * Real.log q + 1) * (r : ℝ) ^ p := by
  convert boxEntropy_power_le_of_large_rectangles (R := R) (D₀ := D) (J := J) (Δ := Δ)
    hq (show 0 ≤ 4 * C by positivity) hp 2 ?_ using 1
  · norm_num
  · intro Λ h E₀ Ω hgs A Q hsafe hQ
    let r := (Q.size + 1) / 2
    have hr : 1 ≤ r := by omega
    have hQtwo : Q.size ≤ 2 * r := by omega
    have hcount : Q.numChunksX r * Q.numChunksY r ≤ 4 :=
      Nat.mul_le_mul (Q.numChunksX_le r hr hQtwo) (Q.numChunksY_le r hr hQtwo)
    let ι := Fin (Q.numChunksX r) × Fin (Q.numChunksY r)
    let ch : ι → IntRect := fun i ↦ Q.child r i.1 i.2
    let Xs : ι → Finset (Site Λ) := fun i ↦ rectRegion A (ch i)
    have hsub : ∀ i : ι, (ch i).toFinset ⊆ Q.toFinset := fun i ↦
      IntRect.child_subset hr i.1.isLt i.2.isLt
    have hclear : (D + 1) * r ≤ D * Q.size := half_size_clearance hD hQ
    have hsafe_child : ∀ i : ι, IsSafe Λ A (D + 1) (ch i) := fun i e he z hz p hp ↦
      lt_of_le_of_lt
        ((Nat.mul_le_mul_left (D + 1) (IntRect.size_child_le (Q := Q) i.1 i.2 hr)).trans
          hclear) (hsafe e he z hz p (hsub i hp))
    have hbound : ∀ i : ι, regionalEntropy Λ q Ω (Xs i) ≤ C * (Q.size : ℝ) ^ p := fun i ↦
      (regionalEntropy_le_boxEntropy hq h hgs (hsafe_child i)
        (IntRect.size_le_of_subset (hsub i))).trans (hbox Q.size Q.one_le_size)
    have hunion : Finset.univ.biUnion Xs = rectRegion A Q := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Xs, mem_rectRegion]
      constructor
      · rintro ⟨i, hxA, hx⟩; exact ⟨hxA, hsub i hx⟩
      · rintro ⟨hxA, hx⟩
        obtain ⟨a, ha, b, hb, hab⟩ := IntRect.exists_mem_child hr hx
        exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hxA, hab⟩
    have hdisj : Pairwise fun i j ↦ Disjoint (Xs i) (Xs j) := by
      intro i j hij
      refine Finset.disjoint_left.mpr fun x hxi hxj ↦ hij ?_
      rw [mem_rectRegion] at hxi hxj
      obtain ⟨h1, h2⟩ := IntRect.eq_of_mem_child hr i.1.isLt i.2.isLt j.1.isLt j.2.isLt hxi.2 hxj.2
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    have hsumEntropy : regionalEntropy Λ q Ω (rectRegion A Q) ≤
        ∑ i : ι, regionalEntropy Λ q Ω (Xs i) := by
      simp only [regionalEntropy_eq_finiteProduct]
      have hu := Entropy.OrderedSetFunction.union_biUnion_le_sum
        (FiniteProduct.entropy (fun _ : Site Λ ↦ Fin q) Ω)
        (FiniteProduct.entropy_union_le _ Ω hgs.1) ∅ Xs Finset.univ
        (by intros; simp) (fun i _ j _ hij ↦ hdisj hij)
      simpa only [Finset.empty_union, FiniteProduct.entropy_empty _ Ω hgs.1,
        zero_add, hunion] using hu
    have hcard : Fintype.card ι ≤ 4 := by
      simpa only [ι, Fintype.card_prod, Fintype.card_fin] using hcount
    calc
      regionalEntropy Λ q Ω (rectRegion A Q) ≤
          ∑ i : ι, regionalEntropy Λ q Ω (Xs i) := hsumEntropy
      _ ≤ ∑ _ : ι, C * (Q.size : ℝ) ^ p := Finset.sum_le_sum fun i _ ↦ hbound i
      _ = (Fintype.card ι : ℝ) * (C * (Q.size : ℝ) ^ p) := by simp
      _ ≤ 4 * (C * (Q.size : ℝ) ^ p) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
          (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      _ = 4 * C * (Q.size : ℝ) ^ p := by ring


end TNLean.PEPS.AreaLaw
