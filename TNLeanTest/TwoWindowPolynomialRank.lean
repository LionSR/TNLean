/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.TwoWindowPolynomialRank
import TNLean.Circuit.PairProduct

/-!
# Applications of the polynomial operator Schmidt rank bound

Constant polynomials test the degree-zero term at both cuts and every local
dimension. A second application uses four actual adjacent SWAP operators on
five qubits. No commutation or scalar-valuedness assumption is supplied.
-/

open Matrix QuantumCircuit
open TNLean.MPS.AreaLaw

noncomputable section

local instance configurationDecidableEq {ι : Type*} (q : ℕ) :
    DecidableEq (ι → Fin q) := Classical.decEq _

local instance alphabetDecidableEq (ℓ : ℕ) :
    DecidableEq ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) := Classical.decEq _

-- This includes q=0 and q=1, and P=1 retains a nonzero constant term.
private noncomputable abbrev constantPolynomialEveryDimension (q : ℕ) (δ : Fin 2) :=
  operatorSchmidtRank_aeval_two_window_le_pow
    (L := 5) (q := q) (ℓ := 1) (a := 0) (b := 2)
    (fun _ ↦ (0 : Matrix (Fin 5 → Fin q) (Fin 5 → Fin q) ℂ))
    (fun _ ↦ Submodule.zero_mem _) (fun _ ↦ Submodule.zero_mem _)
    (Submodule.zero_mem _) (Submodule.zero_mem _) (Submodule.zero_mem _)
    (by decide) (by decide) (by decide) 1 (by decide)
    (Polynomial.C 1) (by simp) δ

/-- The left endpoint of an actual bond. -/
private def edgeFirst {L : ℕ} (r : Fin (L - 1)) : Fin L :=
  ⟨r.val, by omega⟩

/-- The right endpoint of an actual bond. -/
private def edgeSecond {L : ℕ} (r : Fin (L - 1)) : Fin L :=
  ⟨r.val + 1, by omega⟩

/-- The two actual endpoints are exactly the existing interval support. -/
private theorem edgePair_range {L : ℕ} (r : Fin (L - 1)) :
    Set.range (pairSites (edgeFirst r) (edgeSecond r)) =
      (interval L r.val (r.val + 2) : Set (Fin L)) := by
  rw [range_pairSites]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
    mem_interval, Fin.ext_iff]
  change (x.val = r.val ∨ x.val = r.val + 1) ↔
    r.val ≤ x.val ∧ x.val < r.val + 2
  omega

/-- The actual adjacent SWAP at every bond of a chain. -/
private noncomputable abbrev adjacentSwapFamily (L q : ℕ) :
    Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  fun r ↦ embedOp (pairSites (edgeFirst r) (edgeSecond r)) (swapTwo (d := q))

/-- Each embedded SWAP has its actual two-site interval support. -/
private theorem adjacentSwapFamily_supported (L q : ℕ) (r : Fin (L - 1)) :
    adjacentSwapFamily L q r ∈ supportedOperators q
      (interval L r.val (r.val + 2) : Set (Fin L)) := by
  have hne : edgeFirst r ≠ edgeSecond r := by
    intro h
    have hval := congrArg Fin.val h
    change r.val = r.val + 1 at hval
    omega
  rw [← edgePair_range r]
  exact embedOp_mem_supportedOperators (pairSites_injective hne) (swapTwo (d := q))

/-- Four adjacent SWAP terms, with the three bulk terms equal to zero. -/
private noncomputable def swapWindows :
    ((Fin 2 ⊕ Fin 2) ⊕ Fin 3) → Matrix (Fin 5 → Fin 2) (Fin 5 → Fin 2) ℂ
  | Sum.inl (Sum.inl r) => adjacentSwapFamily 5 2 ⟨r.val, by omega⟩
  | Sum.inl (Sum.inr r) => adjacentSwapFamily 5 2 ⟨2 + r.val, by omega⟩
  | Sum.inr _ => 0

-- The same noncommuting physical family is admissible at either source cut.
private noncomputable abbrev adjacentSwapsPolynomial (δ : Fin 2) :=
  operatorSchmidtRank_aeval_two_window_le_pow
    (L := 5) (q := 2) (ℓ := 1) (a := 0) (b := 2) swapWindows
    (by
      intro r
      simpa only [swapWindows, Nat.zero_add] using
        adjacentSwapFamily_supported 5 2 (⟨r.val, by omega⟩ : Fin 4))
    (by
      intro r
      simpa only [swapWindows] using
        adjacentSwapFamily_supported 5 2 (⟨2 + r.val, by omega⟩ : Fin 4))
    (Submodule.zero_mem _) (Submodule.zero_mem _) (Submodule.zero_mem _)
    (by decide) (by decide) (by decide) 1 (by decide)
    Polynomial.X (by simp) δ

-- A physical crossing term is nonzero: its all-zero diagonal entry is one.
example : swapWindows (Sum.inl (Sum.inl 0)) ≠ 0 := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 5 → Fin 2) (Fin 5 → Fin 2) ℂ ↦
    M (fun _ ↦ 0) (fun _ ↦ 0)) h
  simp [swapWindows, adjacentSwapFamily, embedOp_apply, AgreeOff, swapTwo, permOp,
    Function.comp_def] at hentry

-- Both conclusions are statements about the original five-site operator.
example : ((2 * 1) ^ (17 * (1 + 1 / (2 * 1))) : ℕ) = 131072 := by decide

/-- info:
'TNLean.MPS.AreaLaw.operatorSchmidtRank_aeval_two_window_le_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.operatorSchmidtRank_aeval_two_window_le_pow
