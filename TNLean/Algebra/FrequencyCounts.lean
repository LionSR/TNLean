/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Sym.Card
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Frequency vectors with two prescribed coordinates

For an alphabet of `s + 3` labels, prescribing two distinct coordinates
leaves `s + 1` free coordinates. At residual total `m`, their number is
`(m + s).choose s`. At total `r` and prescribed values `i`, `j`, the count
is zero when `r < i + j`; otherwise it is `(r - i - j + s).choose s`.

These statements count all frequency vectors on the original alphabet.
They are supporting counting for ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821, and `prop:Cheby-AGSP-eff`, lines 1324–1332.
The grouped alphabet there has two windows of `2 * ℓ` labels and three
bulk labels, hence `4 * ℓ + 3` labels. Relating those labels to a chain
Hamiltonian and bounding ranks of selected coefficients are separate results.
-/

open scoped BigOperators

/-- Counting natural frequency vectors with two prescribed coordinates.
Supporting counting for ALVV, arXiv:1602.08828v2, eq:H-mid-cut, lines 810–821,
and prop:Cheby-AGSP-eff, lines 1324–1332. -/
theorem Nat.card_fun_sum_eq_and_two_eq
    {I : Type*} [Fintype I] {s : ℕ} (hcard : Fintype.card I = s + 3)
    (u v : I) (huv : u ≠ v) (m i j : ℕ) :
    Nat.card {α : I → ℕ // (∑ a, α a) = m + i + j ∧ α u = i ∧ α v = j} =
      (m + s).choose s := by
  classical
  let S : Finset I := (Finset.univ.erase u).erase v
  have hsum (α : I → ℕ) :
      (∑ a, α a) = (∑ a : S, α a) + α u + α v := by
    have h₁ := Finset.sum_erase_add (a := u) (Finset.univ : Finset I) α (by simp)
    have h₂ := Finset.sum_erase_add (a := v) (Finset.univ.erase u) α (by simp [huv.symm])
    rw [Finset.sum_coe_sort]
    dsimp only [S]
    omega
  let extend (β : S → ℕ) (a : I) : ℕ :=
    if hau : a = u then i else if hav : a = v then j
      else β ⟨a, by simp [S, hau, hav]⟩
  have hextu (β : S → ℕ) : extend β u = i := by simp [extend]
  have hextv (β : S → ℕ) : extend β v = j := by simp [extend, huv.symm]
  have hextS (β : S → ℕ) (a : S) : extend β a = β a := by
    simp only [extend,
      dite_eq_right (Finset.mem_erase.mp (Finset.mem_erase.mp a.property).2).1,
      dite_eq_right (Finset.mem_erase.mp a.property).1]
  let restrict : {α : I → ℕ // (∑ a, α a) = m + i + j ∧ α u = i ∧ α v = j} →
      {β : S → ℕ // (∑ a, β a) = m} := fun α ↦ ⟨fun a ↦ α.val a, by
    have hα := hsum α.val
    have hp := α.property
    change (∑ a : S, α.val a) = m
    omega⟩
  let reinsert : {β : S → ℕ // (∑ a, β a) = m} →
      {α : I → ℕ // (∑ a, α a) = m + i + j ∧ α u = i ∧ α v = j} :=
    fun β ↦ ⟨extend β.val, by
      refine ⟨?_, hextu β.val, hextv β.val⟩
      simpa only [hextS, hextu, hextv, β.property] using hsum (extend β.val)⟩
  let e : {α : I → ℕ // (∑ a, α a) = m + i + j ∧ α u = i ∧ α v = j} ≃
      {β : S → ℕ // (∑ a, β a) = m} :=
    { toFun := restrict
      invFun := reinsert
      left_inv := by
        intro α
        apply Subtype.ext
        funext a
        change extend (fun b : S ↦ α.val b) a = α.val a
        by_cases hau : a = u
        · simpa only [hau, hextu] using α.property.2.1.symm
        · by_cases hav : a = v
          · simpa only [hav, hextv] using α.property.2.2.symm
          · simp only [extend, dite_eq_right hau, dite_eq_right hav]
      right_inv := by
        intro β
        exact Subtype.ext (funext fun a ↦ hextS β.val a) }
  have hcardS : Fintype.card S = s + 1 := by
    rw [Fintype.card_coe, (show S = ((Finset.univ : Finset I).erase u).erase v from rfl),
      Finset.card_erase_of_mem (by simp [huv.symm] : v ∈ (Finset.univ : Finset I).erase u),
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, hcard]
    omega
  rw [Nat.card_congr e]
  rw [Nat.card_congr (Sym.equivNatSumOfFintype S m).symm]
  rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, hcardS]
  have hbase : s + 1 + m - 1 = m + s := by omega
  simpa only [hbase] using (Nat.choose_symm_add (a := m) (b := s))

/-- No natural frequency vector has total smaller than two prescribed
coordinates. This is the empty case of the counting used in ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and
`prop:Cheby-AGSP-eff`, lines 1324–1332. -/
theorem Nat.card_fun_sum_eq_and_two_eq_of_lt
    {I : Type*} [Fintype I]
    (u v : I) (huv : u ≠ v) (r i j : ℕ) (hr : r < i + j) :
    Nat.card {α : I → ℕ // (∑ a, α a) = r ∧ α u = i ∧ α v = j} = 0 := by
  let : IsEmpty {α : I → ℕ // (∑ a, α a) = r ∧ α u = i ∧ α v = j} :=
    ⟨fun α ↦ by
      have hpair := Finset.add_le_sum (s := Finset.univ) (f := α.val)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ u) (Finset.mem_univ v) huv
      have hle : i + j ≤ r := by
        simpa only [α.property.1, α.property.2.1, α.property.2.2] using hpair
      exact (not_le_of_gt hr) hle⟩
  exact Nat.card_of_isEmpty

/-- The number of natural frequency vectors of a fixed total with two fixed
coordinates. This auxiliary count applies to the grouped alphabet in ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and
`prop:Cheby-AGSP-eff`, lines 1324–1332. It counts all frequency vectors,
without a further selection condition. -/
theorem Nat.card_fun_sum_eq_and_two_eq_of_total
    {I : Type*} [Fintype I] {s : ℕ} (hcard : Fintype.card I = s + 3)
    (u v : I) (huv : u ≠ v) (r i j : ℕ) :
    Nat.card {α : I → ℕ // (∑ a, α a) = r ∧ α u = i ∧ α v = j} =
      if i + j ≤ r then (r - i - j + s).choose s else 0 := by
  split_ifs with hle
  · have hres : (r - i - j) + i + j = r := by omega
    simpa only [hres] using
      Nat.card_fun_sum_eq_and_two_eq hcard u v huv (r - i - j) i j
  · exact Nat.card_fun_sum_eq_and_two_eq_of_lt u v huv r i j (by omega)

/-- The number of frequency vectors with two prescribed coordinates is
bounded by a finite box. This is a full-alphabet counting bound for ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and
`prop:Cheby-AGSP-eff`, lines 1324–1332. For the two-window alphabet,
s = 4ℓ. No selection condition is imposed on the counted vectors. -/
theorem Nat.card_fun_sum_eq_and_two_eq_le
    {I : Type*} [Fintype I] {s : ℕ} (hcard : Fintype.card I = s + 3)
    (u v : I) (huv : u ≠ v) (r i j : ℕ) :
    Nat.card {α : I → ℕ // (∑ a, α a) = r ∧ α u = i ∧ α v = j} ≤
      (r + 1) ^ s := by
  rw [Nat.card_fun_sum_eq_and_two_eq_of_total hcard u v huv r i j]
  split_ifs
  · exact (Nat.choose_add_le_add_one_pow (r - i - j) s).trans
      (Nat.pow_le_pow_left
        (Nat.add_le_add_right ((Nat.sub_le (r - i) j).trans (Nat.sub_le r i)) 1) s)
  · exact Nat.zero_le _

/-- The complete frequency slices up to degree k, with two prescribed
coordinates, have total cardinality at most (k+1)^(s+1). This is the
full-alphabet degree summation in the rank argument of ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem Nat.sum_card_fun_sum_eq_and_two_eq_le
    {I : Type*} [Fintype I] {s : ℕ} (hcard : Fintype.card I = s + 3)
    (u v : I) (huv : u ≠ v) (k i j : ℕ) :
    (∑ r ∈ Finset.range (k + 1),
      Nat.card {α : I → ℕ // (∑ a, α a) = r ∧ α u = i ∧ α v = j}) ≤
        (k + 1) ^ (s + 1) := by
  calc
    _ ≤ ∑ r ∈ Finset.range (k + 1), (r + 1) ^ s :=
      Finset.sum_le_sum fun r _ ↦ Nat.card_fun_sum_eq_and_two_eq_le hcard u v huv r i j
    _ ≤ (k + 1) ^ (s + 1) := by
      simpa only [Finset.card_range, nsmul_eq_mul, Nat.cast_id, pow_succ, Nat.mul_comm] using
        Finset.sum_le_card_nsmul (Finset.range (k + 1))
          (fun r : ℕ ↦ (r + 1) ^ s) ((k + 1) ^ s)
          (fun r hr ↦ Nat.pow_le_pow_left (Nat.succ_le_of_lt (Finset.mem_range.mp hr)) s)
