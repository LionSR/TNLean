/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalParityProductSupport
import TNLean.MPS.AreaLaw.OpenMPS
import QICLean.Algebra.OperatorSchmidtProducts
import QICLean.Entropy.SupportedOperatorSchmidtWords

/-!
# Cut ranks of the actual physical parity products

Only one nearest-neighbour factor can cross a site cut, and only one
parity contains that factor. The two actual parity products therefore
have total operator Schmidt rank at most `q²+1`. All ranks are derived
from the actual local supports. No projection or positivity is required.

Source: ALVV, arXiv:1602.08828v2, `thm:FF-tH`, lines 1543--1568.
-/

open Matrix

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

local notation "T" => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
local notation "C" => fun k ↦ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k)

private noncomputable abbrev parityPrefix
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (p n : ℕ) :=
  ContinuousLinearMap.complementProd
    (fun j ↦ if hj : j < L - 1 then if j % 2 = p then T (h ⟨j, hj⟩) else 0 else 0) n

private noncomputable def parityFactor
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (p n : ℕ) :=
  if hn : n < L - 1 then if n % 2 = p then 1 - h ⟨n, hn⟩ else 1 else 1

private theorem parityPrefix_succ
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (p n : ℕ) :
    (T).symm (parityPrefix h p (n + 1)) =
      parityFactor h p n * (T).symm (parityPrefix h p n) := by
  simp only [parityPrefix, ContinuousLinearMap.complementProd_succ, map_mul, map_sub, map_one]
  congr 1
  unfold parityFactor
  split_ifs <;> simp

private theorem operatorSchmidtRank_cut_one_le (k : ℕ) :
    operatorSchmidtRank (C k (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) ≤ 1 := by
  classical
  change operatorSchmidtRank
    (Matrix.reindexAlgEquiv ℂ ℂ (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)) 1) ≤ 1
  rw [map_one]
  exact
    (operatorSchmidtRank_one_le (a := Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k))
      (b := ((v : {v : Fin L // v ∉ leftBlock L k}) → Fin q)))

private theorem interval_one_sided_of_not_crossing (i : Fin (L - 1)) (k : ℕ)
    (hcross : i.val + 1 ≠ k) :
    interval L i.val (i.val + 2) ⊆ leftBlock L k ∨
      Disjoint (interval L i.val (i.val + 2)) (leftBlock L k) := by
  by_cases hleft : i.val + 1 < k
  · left
    intro v hv
    simp only [mem_interval, mem_leftBlock] at *
    omega
  · right
    apply Finset.disjoint_left.mpr
    intro v hv hk
    simp only [mem_interval, mem_leftBlock] at *
    omega

private theorem isSupportedOn_bond_complement
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (i : Fin (L - 1)) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (1 - h i) (interval L i.val (i.val + 2)) := by
  classical
  apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators (q := q)
    (S := interval L i.val (i.val + 2))
  exact (QuantumCircuit.supportedOperators q
    ((interval L i.val (i.val + 2)) : Set (Fin L))).sub_mem
    (QuantumCircuit.one_mem_supportedOperators _)
    (QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hs i))

private theorem parityFactor_rank_le_one
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (p n k : ℕ)
    (hno : n + 1 ≠ k ∨ n % 2 ≠ p) :
    operatorSchmidtRank (C k (parityFactor h p n)) ≤ 1 := by
  classical
  unfold parityFactor
  split_ifs with hn hp
  · exact (isSupportedOn_bond_complement h hs ⟨n, hn⟩).operatorSchmidtRank_cutOperator_le_one
      (interval_one_sided_of_not_crossing ⟨n, hn⟩ k
        (hno.elim id (fun hne ↦ False.elim (hne hp))))
  · exact operatorSchmidtRank_cut_one_le k
  · exact operatorSchmidtRank_cut_one_le k

private theorem parityFactor_rank_le_sq (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (p n k : ℕ) :
    operatorSchmidtRank (C k (parityFactor h p n)) ≤ q ^ 2 := by
  classical
  unfold parityFactor
  split_ifs with hn hp
  · exact (isSupportedOn_bond_complement h hs ⟨n, hn⟩).operatorSchmidtRank_cutOperator_le_pow_card
      hq |>.trans (Nat.pow_le_pow_right hq ((card_interval_le _ _).trans (by omega)))
  · exact (operatorSchmidtRank_cut_one_le k).trans (one_le_pow₀ hq)
  · exact (operatorSchmidtRank_cut_one_le k).trans (one_le_pow₀ hq)

private theorem parityPrefix_rank_le_one
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (p n k : ℕ)
    (hno : ∀ j < n, j + 1 ≠ k ∨ j % 2 ≠ p) :
    operatorSchmidtRank (C k ((T).symm (parityPrefix h p n))) ≤ 1 := by
  classical
  induction n with
  | zero =>
    simpa only [parityPrefix, ContinuousLinearMap.complementProd_zero, map_one] using
      operatorSchmidtRank_cut_one_le k
  | succ n ih =>
    rw [parityPrefix_succ]
    dsimp only
    rw [Entropy.cutOperator_mul]
    exact (operatorSchmidtRank_mul_le _ _).trans
      ((Nat.mul_le_mul (parityFactor_rank_le_one h hs p n k
        (hno n (Nat.lt_succ_self n)))
        (ih fun j hj ↦ hno j (Nat.lt_succ_of_lt hj))).trans_eq (by norm_num))

private theorem parityPrefix_rank_le_sq (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (p n k : ℕ) :
    operatorSchmidtRank (C k ((T).symm (parityPrefix h p n))) ≤ q ^ 2 := by
  classical
  induction n with
  | zero =>
    simpa only [parityPrefix, ContinuousLinearMap.complementProd_zero, map_one] using
      (operatorSchmidtRank_cut_one_le k).trans (one_le_pow₀ hq)
  | succ n ih =>
    rw [parityPrefix_succ]
    dsimp only
    rw [Entropy.cutOperator_mul]
    by_cases hcross : n + 1 = k
    · have hbefore := parityPrefix_rank_le_one h hs p n k
        (fun j hj ↦ Or.inl (by omega))
      exact (operatorSchmidtRank_mul_le _ _).trans
        ((Nat.mul_le_mul (parityFactor_rank_le_sq hq h hs p n k) hbefore).trans_eq
          (Nat.mul_one _))
    · exact (operatorSchmidtRank_mul_le _ _).trans
        ((Nat.mul_le_mul (parityFactor_rank_le_one h hs p n k (Or.inl hcross)) ih).trans_eq
          (Nat.one_mul _))

/-- The actual parity product has cut rank at most the local dimension
squared. The unique possible crossing factor is derived from its support. -/
theorem operatorSchmidtRank_physicalParityProduct_le_sq (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (p k : ℕ) :
    operatorSchmidtRank (C k ((T).symm (physicalParityProduct h p))) ≤ q ^ 2 := by
  exact parityPrefix_rank_le_sq hq h hs p (L - 1) k

/-- The parity not containing the possible crossing bond has rank at most
one. This also includes cuts beyond the chain and empty configuration spaces. -/
theorem operatorSchmidtRank_physicalParityProduct_le_one
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (p k : ℕ) (hp : (k - 1) % 2 ≠ p) :
    operatorSchmidtRank (C k ((T).symm (physicalParityProduct h p))) ≤ 1 := by
  apply parityPrefix_rank_le_one h hs p (L - 1) k
  intro j _
  by_cases hj : j + 1 = k
  · have heq : j = k - 1 := by omega
    exact Or.inr (by simpa only [heq] using hp)
  · exact Or.inl hj

/-- The sum of the two actual parity-product ranks is at most `q²+1`.
No decomposition, rank, commutation or projection hypothesis is supplied. -/
theorem sum_operatorSchmidtRank_physicalParityProduct_le (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (k : ℕ) :
    operatorSchmidtRank (C k ((T).symm (physicalParityProduct h 0))) +
      operatorSchmidtRank (C k ((T).symm (physicalParityProduct h 1))) ≤ q ^ 2 + 1 := by
  by_cases hp : (k - 1) % 2 = 0
  · exact Nat.add_le_add (operatorSchmidtRank_physicalParityProduct_le_sq hq h hs 0 k)
      (operatorSchmidtRank_physicalParityProduct_le_one h hs 1 k (by omega))
  · have h0 := operatorSchmidtRank_physicalParityProduct_le_one h hs 0 k hp
    have h1 := operatorSchmidtRank_physicalParityProduct_le_sq hq h hs 1 k
    omega

end TNLean.MPS.AreaLaw
