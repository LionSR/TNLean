/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.GridLocalization

/-!
# The original positive nearest-neighbor chain as a finite-range Hamiltonian

The original interaction on each adjacent pair is assigned to that exact range-one
support; every other support receives zero. The resulting chain Hamiltonian has range
one and norm bound one, and its operator is exactly the original interaction sum.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, the nearest-neighbor
Hamiltonian and local positive-contraction assumptions preceding the viable-set algorithm;
Huang, arXiv:1406.6355v6, Section 5.4, Lemmas 18--19. This identification changes neither
the physical operator nor the spectral hypotheses used by the two constructions.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- Distinct original edges have distinct designated supports. This is the support
identification for the nearest-neighbor Hamiltonian of LVV13, `algo53.tex`. -/
theorem nearestNeighborChainSupport_injective {L : ℕ} :
    Function.Injective (nearestNeighborChainSupport (L := L)) := by
  intro i j hij
  have hsets := congrArg Subtype.val hij
  let x : Fin L := ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le L 1)⟩
  let y : Fin L := ⟨j.val, lt_of_lt_of_le j.isLt (Nat.sub_le L 1)⟩
  have hx : x ∈ (nearestNeighborChainSupport i).val :=
    mem_interval.mpr ⟨le_rfl, by dsimp only [x]; omega⟩
  have hy : y ∈ (nearestNeighborChainSupport j).val :=
    mem_interval.mpr ⟨le_rfl, by dsimp only [y]; omega⟩
  have hxj := (mem_interval.mp ((Finset.ext_iff.mp hsets x).mp hx)).1
  have hyi := (mem_interval.mp ((Finset.ext_iff.mp hsets y).mpr hy)).1
  apply Fin.ext
  dsimp only [x, y] at hxj hyi
  omega

/-- Every designated original edge contains exactly two sites. This is the adjacent-pair
support convention of LVV13, `algo53.tex`, used in Huang, Section 5.4. -/
theorem card_nearestNeighborChainSupport {L : ℕ} (i : Fin (L - 1)) :
    (nearestNeighborChainSupport i).val.card = 2 := by
  let x : Fin L := ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le L 1)⟩
  let y : Fin L := ⟨i.val + 1, by omega⟩
  have hset : (nearestNeighborChainSupport i).val = {x, y} := by
    ext v
    simp only [nearestNeighborChainSupport, mem_interval, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff, x, y]
    omega
  rw [hset, Finset.card_pair]
  exact fun h ↦ by have := congrArg Fin.val h; dsimp only [x, y] at this; omega

private theorem forall_nearestNeighborExtension {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (P : ChainSupport L 1 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ → Prop)
    (hzero : ∀ X, P X 0) (hterm : ∀ i, P (nearestNeighborChainSupport i) (h i)) :
    ∀ X, P X (Function.extend nearestNeighborChainSupport h (fun _ ↦ 0) X) := by
  intro X
  by_cases hX : ∃ i, nearestNeighborChainSupport i = X
  · obtain ⟨i, rfl⟩ := hX
    simpa only [nearestNeighborChainSupport_injective.extend_apply] using hterm i
  · simpa only [Function.extend_apply' _ _ _ hX] using hzero X

/-- The original positive nearest-neighbor contractions, as a range-one chain Hamiltonian
with norm bound one. Original pair terms are retained and all other terms are zero.
LVV13, `algo53.tex`, the local Hamiltonian assumptions; Huang, Section 5.4, Lemmas 18--19. -/
noncomputable def ChainHamiltonian.ofNearestNeighborPositive {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    ChainHamiltonian L q 1 1 where
  term := Function.extend nearestNeighborChainSupport h (fun _ ↦ 0)
  supported := forall_nearestNeighborExtension h
    (fun X M ↦ Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) M X.val)
    (fun _ ↦ isSupportedOn_of_mem_supportedOperators (Submodule.zero_mem _)) hs
  hermitian := forall_nearestNeighborExtension h (fun _ M ↦ M.IsHermitian)
    (fun _ ↦ isHermitian_zero)
    (fun i ↦ (IsSelfAdjoint.of_nonneg (h0 i)).isHermitian)
  norm_le := forall_nearestNeighborExtension h (fun _ M ↦ ‖M‖ ≤ 1) (fun _ ↦ by simp)
    (fun i ↦ (CStarAlgebra.norm_le_one_iff_of_nonneg _ (h0 i)).mpr (h1 i))

variable {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)

/-- The constructed Hamiltonian keeps the actual original term at each adjacent pair.
LVV13, `algo53.tex`, the nearest-neighbor Hamiltonian convention. -/
theorem ChainHamiltonian.ofNearestNeighborPositive_term (i : Fin (L - 1)) :
    (ofNearestNeighborPositive h hs h0 h1).term (nearestNeighborChainSupport i) = h i := by
  change Function.extend nearestNeighborChainSupport h (fun _ ↦ 0)
    (nearestNeighborChainSupport i) = h i
  exact nearestNeighborChainSupport_injective.extend_apply h (fun _ ↦ 0) i

/-- A support not assigned to an original edge receives zero. In particular this
does not add interactions to the original model of LVV13, `algo53.tex`. -/
theorem ChainHamiltonian.ofNearestNeighborPositive_term_eq_zero (X : ChainSupport L 1)
    (hX : ¬∃ i, nearestNeighborChainSupport i = X) :
    (ofNearestNeighborPositive h hs h0 h1).term X = 0 := by
  change Function.extend nearestNeighborChainSupport h (fun _ ↦ 0) X = 0
  exact Function.extend_apply' h (fun _ ↦ 0) X hX

/-- All singleton terms of the constructed Hamiltonian are zero. This preserves the
original adjacent-pair model of LVV13, `algo53.tex`. -/
theorem ChainHamiltonian.ofNearestNeighborPositive_term_eq_zero_of_card_one
    (X : ChainSupport L 1) (hX : X.val.card = 1) :
    (ofNearestNeighborPositive h hs h0 h1).term X = 0 := by
  apply ofNearestNeighborPositive_term_eq_zero
  rintro ⟨i, rfl⟩
  have := card_nearestNeighborChainSupport i
  omega

/-- Every term remains positive in the constructed representation of the original
positive Hamiltonian of LVV13, `algo53.tex`. -/
theorem ChainHamiltonian.ofNearestNeighborPositive_term_nonneg (X : ChainSupport L 1) :
    0 ≤ (ofNearestNeighborPositive h hs h0 h1).term X := by
  change 0 ≤ Function.extend nearestNeighborChainSupport h (fun _ ↦ 0) X
  exact forall_nearestNeighborExtension h (fun _ M ↦ 0 ≤ M) (fun _ ↦ le_rfl) h0 X

/-- Every term remains bounded above by the identity in the constructed representation.
LVV13, `algo53.tex`, the local positive-contraction assumptions. -/
theorem ChainHamiltonian.ofNearestNeighborPositive_term_le_one (X : ChainSupport L 1) :
    (ofNearestNeighborPositive h hs h0 h1).term X ≤ 1 := by
  change Function.extend nearestNeighborChainSupport h (fun _ ↦ 0) X ≤ 1
  exact forall_nearestNeighborExtension h (fun _ M ↦ M ≤ 1) (fun _ ↦ zero_le_one) h1 X

/-- Summing the constructed range-one interaction family gives exactly the original
operator. LVV13, `algo53.tex`, the nearest-neighbor Hamiltonian; Huang, Section 5.4. -/
theorem ChainHamiltonian.ofNearestNeighborPositive_operator :
    (ofNearestNeighborPositive h hs h0 h1).operator = ∑ i, h i := by
  classical
  let f := nearestNeighborChainSupport (L := L)
  let H := ofNearestNeighborPositive h hs h0 h1
  have hsub : Finset.univ.image f ⊆ (Finset.univ : Finset (ChainSupport L 1)) :=
    Finset.subset_univ _
  calc
    _ = ∑ X ∈ Finset.univ.image f, H.term X := by
      symm
      apply Finset.sum_subset hsub
      intro X _ hX
      apply ofNearestNeighborPositive_term_eq_zero
      simpa only [Finset.mem_image, Finset.mem_univ, true_and, f] using hX
    _ = ∑ i, H.term (f i) := Finset.sum_image (fun _ _ _ _ hij ↦
      nearestNeighborChainSupport_injective hij)
    _ = _ := Finset.sum_congr rfl fun i _ ↦ ofNearestNeighborPositive_term h hs h0 h1 i

end TNLean.MPS.AreaLaw
