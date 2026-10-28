/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Finset.Union
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import QICLean.Algebra.MatrixAux
import QICLean.Analysis.EnergyTruncation
import QICLean.Analysis.GroundEnergyBounds
import TNLean.Algebra.KroneckerLeastEigenvalue
import TNLean.Circuit.EntropySupport
import TNLean.Lattice.RegionSplit

/-!
# Common ground vectors on disjoint regions

Hamiltonians on pairwise disjoint site sets have a common unit ground vector. Their original
regional minima remain fixed while any subfamily is clipped. The centered sums retain
positivity, commutation, high-energy lower bounds and explicit norm budgets.

These results support ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, and Theorem `t:ais`, lines 1010–1024.
-/

section

section

section

section

section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A sum acting on separate tensor factors has a unit product ground vector and
ground energy equal to the sum of the factor minima. Auxiliary to ALVV's
hard-truncation construction, `def:hard-trunc`, checked source lines 873–886.
No simplicity or gap assumption is imposed on either ground space. -/
private theorem exists_unit_product_ground_of_kronecker_sum
    [Nonempty α] [Nonempty β] (A : Matrix α α ℂ) (B : Matrix β β ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ (eA eB : ℝ) (u : α → ℂ) (v : β → ℂ),
      A *ᵥ u = (eA : ℂ) • u ∧ star u ⬝ᵥ u = 1 ∧
      (A - (eA : ℂ) • 1).PosSemidef ∧
      B *ᵥ v = (eB : ℂ) • v ∧ star v ⬝ᵥ v = 1 ∧
      (B - (eB : ℂ) • 1).PosSemidef ∧
      star (fun p : α × β ↦ u p.1 * v p.2) ⬝ᵥ
        (fun p : α × β ↦ u p.1 * v p.2) = 1 ∧
      (A ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ B) *ᵥ
        (fun p : α × β ↦ u p.1 * v p.2) =
          ((eA + eB : ℝ) : ℂ) • (fun p : α × β ↦ u p.1 * v p.2) ∧
      (A ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ B -
        ((eA + eB : ℝ) : ℂ) • 1).PosSemidef := by
  obtain ⟨eA, u, hu, hu1, huA⟩ := hA.exists_unit_eigenvector_le
  obtain ⟨eB, v, hv, hv1, hvB⟩ := hB.exists_unit_eigenvector_le
  refine ⟨eA, eB, u, v, hu, hu1, huA, hv, hv1, hvB, ?_, ?_, ?_⟩
  · rw [star_mul_dotProduct_mul, hu1, hv1, one_mul]
  · rw [add_mulVec, kronecker_mulVec_mul, kronecker_mulVec_mul,
      one_mulVec, one_mulVec, hu, hv]
    funext p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  · have hsplit :
        A ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ B -
            ((eA + eB : ℝ) : ℂ) • 1 =
          (A - (eA : ℂ) • 1) ⊗ₖ (1 : Matrix β β ℂ) +
            (1 : Matrix α α ℂ) ⊗ₖ (B - (eB : ℂ) • 1) := by
      have e1 : (A - (eA : ℂ) • 1) ⊗ₖ (1 : Matrix β β ℂ) =
          A ⊗ₖ (1 : Matrix β β ℂ) - (eA : ℂ) • 1 := by
        ext ⟨i, j⟩ ⟨k, l⟩
        by_cases hik : i = k <;> by_cases hjl : j = l <;>
          simp [hik, hjl]
      have e2 : (1 : Matrix α α ℂ) ⊗ₖ (B - (eB : ℂ) • 1) =
          (1 : Matrix α α ℂ) ⊗ₖ B - (eB : ℂ) • 1 := by
        ext ⟨i, j⟩ ⟨k, l⟩
        by_cases hik : i = k <;> by_cases hjl : j = l <;>
          simp [hik, hjl]
      rw [e1, e2]
      push_cast
      rw [add_smul]
      abel
    rw [hsplit]
    exact (huA.kronecker PosSemidef.one).add (PosSemidef.one.kronecker hvB)
end Matrix

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace Matrix

/-- Complementary supported operators have a product ground vector in the
canonical region coordinates. Auxiliary to ALVV's hard truncation,
arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886. Taking the region to be
`leftBlock L k` gives the two sides of a chain cut, including empty sides. -/
private theorem exists_product_ground_of_complementary_support
    {L q : ℕ} (S : Finset (Fin L)) (hq : 0 < q)
    (A B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) A S)
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B Sᶜ) :
    ∃ (A₀ : Matrix (S → Fin q) (S → Fin q) ℂ)
      (B₀ : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ)
      (eA eB : ℝ) (u : (S → Fin q) → ℂ) (v : (↥Sᶜ → Fin q) → ℂ),
      A.submatrix (TNLean.Lattice.sheetSplit q S).symm
          (TNLean.Lattice.sheetSplit q S).symm = A₀ ⊗ₖ 1 ∧
      B.submatrix (TNLean.Lattice.sheetSplit q S).symm
          (TNLean.Lattice.sheetSplit q S).symm = 1 ⊗ₖ B₀ ∧
      A₀ *ᵥ u = (eA : ℂ) • u ∧ star u ⬝ᵥ u = 1 ∧
      (A₀ - (eA : ℂ) • 1).PosSemidef ∧
      B₀ *ᵥ v = (eB : ℂ) • v ∧ star v ⬝ᵥ v = 1 ∧
      (B₀ - (eB : ℂ) • 1).PosSemidef ∧
      star (fun p : (S → Fin q) × (↥Sᶜ → Fin q) ↦ u p.1 * v p.2) ⬝ᵥ
        (fun p : (S → Fin q) × (↥Sᶜ → Fin q) ↦ u p.1 * v p.2) = 1 ∧
      (A + B).submatrix (TNLean.Lattice.sheetSplit q S).symm
          (TNLean.Lattice.sheetSplit q S).symm *ᵥ
            (fun p : (S → Fin q) × (↥Sᶜ → Fin q) ↦ u p.1 * v p.2) =
        ((eA + eB : ℝ) : ℂ) •
          (fun p : (S → Fin q) × (↥Sᶜ → Fin q) ↦ u p.1 * v p.2) ∧
      ((A + B).submatrix (TNLean.Lattice.sheetSplit q S).symm
          (TNLean.Lattice.sheetSplit q S).symm -
        ((eA + eB : ℝ) : ℂ) • 1).PosSemidef := by
  let a₀ : S → Fin q := fun _ ↦ ⟨0, hq⟩
  let b₀ : ↥Sᶜ → Fin q := fun _ ↦ ⟨0, hq⟩
  have : Nonempty (S → Fin q) := ⟨a₀⟩
  have : Nonempty (↥Sᶜ → Fin q) := ⟨b₀⟩
  obtain ⟨A₀, hAe⟩ := TNLean.Lattice.exists_kronecker_one_of_mem_supportedOperators
    (QuantumCircuit.mem_supportedOperators_of_isSupportedOn hAS)
  have hdisj : Disjoint (↑Sᶜ : Set (Fin L)) (↑S : Set (Fin L)) := by
    exact Set.disjoint_left.mpr fun _ hv hvS ↦ (Finset.mem_compl.mp hv) hvS
  obtain ⟨B₀, hBe⟩ := TNLean.Lattice.exists_one_kronecker_of_mem_supportedOperators hdisj
    (QuantumCircuit.mem_supportedOperators_of_isSupportedOn hBS)
  have hA₀ : A₀.IsHermitian := by
    refine IsHermitian.ext fun i j ↦ ?_
    have h := (hA.submatrix (TNLean.Lattice.sheetSplit q S).symm).apply (i, b₀) (j, b₀)
    rw [hAe] at h
    simpa only [kroneckerMap_apply, one_apply_eq, mul_one] using h
  have hB₀ : B₀.IsHermitian := by
    refine IsHermitian.ext fun i j ↦ ?_
    have h := (hB.submatrix (TNLean.Lattice.sheetSplit q S).symm).apply (a₀, i) (a₀, j)
    rw [hBe] at h
    simpa only [kroneckerMap_apply, one_apply_eq, one_mul] using h
  obtain ⟨eA, eB, u, v, hu, hu1, huA, hv, hv1, hvB, hunit, hev, hlow⟩ :=
    exists_unit_product_ground_of_kronecker_sum A₀ B₀ hA₀ hB₀
  have hsum : (A + B).submatrix (TNLean.Lattice.sheetSplit q S).symm
      (TNLean.Lattice.sheetSplit q S).symm = A₀ ⊗ₖ 1 + 1 ⊗ₖ B₀ := by
    change A.submatrix (TNLean.Lattice.sheetSplit q S).symm
        (TNLean.Lattice.sheetSplit q S).symm +
      B.submatrix (TNLean.Lattice.sheetSplit q S).symm
        (TNLean.Lattice.sheetSplit q S).symm = _
    rw [hAe, hBe]
  refine ⟨A₀, B₀, eA, eB, u, v, hAe, hBe,
    hu, hu1, huA, hv, hv1, hvB, hunit, ?_, ?_⟩
  · rw [hsum]
    exact hev
  · rw [hsum]
    exact hlow
end Matrix

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace Matrix

/-- Complementary supported Hermitian operators admit a common unit ground
vector on the actual chain. Auxiliary to ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886. Both minima and the vector are constructed;
no common-vector, simplicity, gap, or commutation hypothesis is imposed. -/
private theorem exists_common_unit_ground_of_complementary_support
    {L q : ℕ} (S : Finset (Fin L)) (hq : 0 < q)
    (A B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) A S)
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B Sᶜ) :
    ∃ (eA eB : ℝ) (x : (Fin L → Fin q) → ℂ),
      star x ⬝ᵥ x = 1 ∧ A *ᵥ x = (eA : ℂ) • x ∧ B *ᵥ x = (eB : ℂ) • x ∧
      (A - (eA : ℂ) • 1).PosSemidef ∧ (B - (eB : ℂ) • 1).PosSemidef := by
  obtain ⟨A₀, B₀, eA, eB, u, v, hAe, hBe, hu, _hu1, huA, hv, _hv1, hvB,
    hunit, _hev, _hlow⟩ :=
    exists_product_ground_of_complementary_support S hq A B hA hB hAS hBS
  let e := TNLean.Lattice.sheetSplit q S
  let φ : (S → Fin q) × (↥Sᶜ → Fin q) → ℂ := fun p ↦ u p.1 * v p.2
  let x : (Fin L → Fin q) → ℂ := φ ∘ e
  have hx1 : star x ⬝ᵥ x = 1 := by
    change ((star φ) ∘ e) ⬝ᵥ (φ ∘ e) = 1
    rw [comp_equiv_dotProduct_comp_equiv]
    exact hunit
  have htransport (M : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (lam : ℝ)
      (hM : M.submatrix e.symm e.symm *ᵥ φ = (lam : ℂ) • φ) :
      M *ᵥ x = (lam : ℂ) • x := by
    rw [submatrix_mulVec_equiv] at hM
    funext σ
    have hσ := congrFun hM (e σ)
    simpa only [x, Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply,
      Pi.smul_apply] using hσ
  have hAx : A *ᵥ x = (eA : ℂ) • x := by
    apply htransport A eA
    dsimp only [φ]
    rw [hAe, kronecker_mulVec_mul, one_mulVec, hu]
    funext p
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hBx : B *ᵥ x = (eB : ℂ) • x := by
    apply htransport B eB
    dsimp only [φ]
    rw [hBe, kronecker_mulVec_mul, one_mulVec, hv]
    funext p
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have htransportPSD (M : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (lam : ℝ)
      (hM : (M.submatrix e.symm e.symm - (lam : ℂ) • 1).PosSemidef) :
      (M - (lam : ℂ) • 1).PosSemidef := by
    convert hM.submatrix e using 1
    ext σ τ
    simp only [submatrix_apply, sub_apply, smul_apply, smul_eq_mul, one_apply,
      Equiv.symm_apply_apply, e.apply_eq_iff_eq]
  have hAlow : (A - (eA : ℂ) • 1).PosSemidef := by
    apply htransportPSD A eA
    rw [hAe]
    convert huA.kronecker (PosSemidef.one (n := ↥Sᶜ → Fin q)) using 1
    ext ⟨i, j⟩ ⟨k, l⟩
    by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl]
  have hBlow : (B - (eB : ℂ) • 1).PosSemidef := by
    apply htransportPSD B eB
    rw [hBe]
    convert (PosSemidef.one (n := S → Fin q)).kronecker hvB using 1
    ext ⟨i, j⟩ ⟨k, l⟩
    by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl]
  exact ⟨eA, eB, x, hx1, hAx, hBx, hAlow, hBlow⟩
end Matrix

open scoped ComplexOrder

namespace Matrix

/-- Hermitian operators on disjoint regions have a common unit vector realizing
their specified attained lower bounds. The common vector is constructed from
the two regions; no simplicity or spectral gap is required. Auxiliary to ALVV,
arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886, and
Corollary `c:goodagsphardtrunc`, lines 979–1005. -/
private theorem exists_common_unit_fixed_ground_of_disjoint_support
    {L q : ℕ} (S T : Finset (Fin L)) (hST : Disjoint S T) (hq : 0 < q)
    (A B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) A S)
    (hBT : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B T)
    (a b : ℝ) (xA xB : (Fin L → Fin q) → ℂ)
    (hAxA : A *ᵥ xA = (a : ℂ) • xA) (hxA : star xA ⬝ᵥ xA = 1)
    (hBxB : B *ᵥ xB = (b : ℂ) • xB) (hxB : star xB ⬝ᵥ xB = 1)
    (hAlow : (A - (a : ℂ) • 1).PosSemidef)
    (hBlow : (B - (b : ℂ) • 1).PosSemidef) :
    ∃ x : (Fin L → Fin q) → ℂ,
      star x ⬝ᵥ x = 1 ∧ A *ᵥ x = (a : ℂ) • x ∧ B *ᵥ x = (b : ℂ) • x := by
  have hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B Sᶜ :=
    hBT.mono (Finset.subset_compl_iff_disjoint_left.mpr hST)
  obtain ⟨a', b', x, hx, hAx, hBx, hAlow', hBlow'⟩ :=
    exists_common_unit_ground_of_complementary_support S hq A B hA hB hAS hBS
  have ha : a' = a := groundEnergy_eq_of_normalized_eigenvectors A a' a x xA
    hAx hx hAxA hxA hAlow' hAlow
  have hb : b' = b := groundEnergy_eq_of_normalized_eigenvectors B b' b x xB
    hBx hx hBxB hxB hBlow' hBlow
  exact ⟨x, hx, by simpa only [ha] using hAx, by simpa only [hb] using hBx⟩
end Matrix

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

/-- Original regional operators with pairwise disjoint supports admit a
common unit vector attaining their supplied genuine ground energies.
Auxiliary to the three successive truncations in ALVV,
arXiv:1602.08828v2, Corollary c:goodagsphardtrunc, lines 979–1005.
The vector is constructed from the spatial supports and individual ground
data; no simultaneous-ground, simplicity or gap hypothesis is imposed. -/
private theorem exists_common_unit_fixed_ground_of_disjoint_family
    {ι : Type*} {L q : ℕ} (hq : 0 < q)
    (s : Finset ι) (R : ι → Finset (Fin L))
    (A : ι → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (e : ι → ℝ)
    (hdisj : (s : Set ι).Pairwise fun i j ↦ Disjoint (R i) (R j))
    (hsupp : ∀ i ∈ s, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (A i) (R i))
    (hlow : ∀ i ∈ s, (A i - (e i : ℂ) • 1).PosSemidef)
    (hattain : ∀ i ∈ s, ∃ x : (Fin L → Fin q) → ℂ,
      star x ⬝ᵥ x = 1 ∧ A i *ᵥ x = (e i : ℂ) • x) :
    ∃ x : (Fin L → Fin q) → ℂ,
      star x ⬝ᵥ x = 1 ∧ ∀ i ∈ s, A i *ᵥ x = (e i : ℂ) • x := by
  classical
  revert hdisj hsupp hlow hattain
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ _ _
    let σ₀ : Fin L → Fin q := fun _ ↦ ⟨0, hq⟩
    refine ⟨Pi.single σ₀ (1 : ℂ), ?_, ?_⟩
    · rw [dotProduct_single]
      simp
    · intro i hi
      simp at hi
  | @insert a s ha ih =>
    intro hdisj hsupp hlow hattain
    have hdisjs : (s : Set ι).Pairwise fun i j ↦ Disjoint (R i) (R j) := by
      intro i hi j hj hij
      exact hdisj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
    obtain ⟨v, hvunit, hv⟩ := ih hdisjs
      (fun i hi ↦ hsupp i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hlow i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hattain i (Finset.mem_insert_of_mem hi))
    let S : Finset (Fin L) := s.biUnion R
    let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      ∑ i ∈ s, (A i - (e i : ℂ) • 1)
    have hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B S := by
      apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
      apply (QuantumCircuit.supportedOperators q (S : Set (Fin L))).sum_mem
      intro i hi
      apply Submodule.sub_mem
      · apply QuantumCircuit.mem_supportedOperators_of_isSupportedOn
        apply (hsupp i (Finset.mem_insert_of_mem hi)).mono
        intro z hz
        exact Finset.mem_biUnion.mpr ⟨i, hi, hz⟩
      · exact Submodule.smul_mem _ _ (QuantumCircuit.one_mem_supportedOperators _)
    have hBpos : B.PosSemidef :=
      posSemidef_sum s (fun i hi ↦ hlow i (Finset.mem_insert_of_mem hi))
    have hvB : B *ᵥ v = (0 : ℂ) • v := by
      change (∑ i ∈ s, (A i - (e i : ℂ) • 1)) *ᵥ v = (0 : ℂ) • v
      rw [sum_mulVec, zero_smul]
      exact Finset.sum_eq_zero fun i hi ↦ by
        rw [sub_mulVec, smul_mulVec, one_mulVec, hv i hi, sub_self]
    have hST : Disjoint S (R a) := by
      apply (Finset.disjoint_biUnion_left s R (R a)).2
      intro i hi
      apply hdisj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self a s)
      intro hieq
      exact ha (hieq ▸ hi)
    have hAa : (A a).IsHermitian := by
      have hscalar : ((e a : ℂ) • (1 : Matrix (Fin L → Fin q)
          (Fin L → Fin q) ℂ)).IsHermitian := by
        rw [Complex.coe_smul]
        exact (IsSelfAdjoint.smul (IsSelfAdjoint.all (e a))
          (IsSelfAdjoint.one _)).isHermitian
      simpa only [sub_add_cancel] using
        (hlow a (Finset.mem_insert_self a s)).isHermitian.add hscalar
    obtain ⟨xA, hxAunit, hxA⟩ := hattain a (Finset.mem_insert_self a s)
    obtain ⟨w, hwunit, hwB, hwA⟩ := exists_common_unit_fixed_ground_of_disjoint_support
      S (R a) hST hq B (A a) hBpos.isHermitian hAa hBS
      (hsupp a (Finset.mem_insert_self a s)) 0 (e a) v xA hvB hvunit hxA hxAunit
      (by simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using hBpos)
      (hlow a (Finset.mem_insert_self a s))
    refine ⟨w, hwunit, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hwA
    · have hwBzero : B *ᵥ w = 0 := by simpa only [Complex.ofReal_zero, zero_smul] using hwB
      have hwi : (A i - (e i : ℂ) • 1) *ᵥ w = 0 :=
        PosSemidef.mulVec_eq_zero_of_sum_mulVec_eq_zero_of_mem
          (s := s) (B := fun j ↦ A j - (e j : ℂ) • 1)
          (fun j hj ↦ hlow j (Finset.mem_insert_of_mem hj)) hwBzero hi
      exact sub_eq_zero.mp (by
        simpa only [sub_mulVec, smul_mulVec, one_mulVec] using hwi)
end Matrix

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

/-- Hermitian operators with pairwise disjoint actual supports have a common
unit vector attaining their genuine ground energies. The individual minima
and their attainment are constructed, not supplied. Auxiliary to ALVV,
arXiv:1602.08828v2, Corollary c:goodagsphardtrunc, lines 979–1005. -/
private theorem exists_common_unit_ground_of_disjoint_family
    {ι : Type*} {L q : ℕ} (hq : 0 < q)
    (s : Finset ι) (R : ι → Finset (Fin L))
    (A : ι → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hA : ∀ i ∈ s, (A i).IsHermitian)
    (hdisj : (s : Set ι).Pairwise fun i j ↦ Disjoint (R i) (R j))
    (hsupp : ∀ i ∈ s, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (A i) (R i)) :
    ∃ (e : ι → ℝ) (x : (Fin L → Fin q) → ℂ),
      star x ⬝ᵥ x = 1 ∧
        (∀ i ∈ s, A i *ᵥ x = (e i : ℂ) • x) ∧
        ∀ i ∈ s, (A i - (e i : ℂ) • 1).PosSemidef := by
  classical
  have : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  have hmin (i : ↥s) :
      ∃ (ei : ℝ) (v : (Fin L → Fin q) → ℂ),
        A i.val *ᵥ v = (ei : ℂ) • v ∧ star v ⬝ᵥ v = 1 ∧
          (A i.val - (ei : ℂ) • 1).PosSemidef :=
    (hA i.val i.property).exists_unit_eigenvector_le
  let e : ι → ℝ := fun i ↦
    if hi : i ∈ s then Classical.choose (hmin ⟨i, hi⟩) else 0
  have hdata (i : ι) (hi : i ∈ s) :
      ∃ v : (Fin L → Fin q) → ℂ,
        A i *ᵥ v = (e i : ℂ) • v ∧ star v ⬝ᵥ v = 1 ∧
          (A i - (e i : ℂ) • 1).PosSemidef := by
    simpa [e, hi] using Classical.choose_spec (hmin ⟨i, hi⟩)
  have hlow : ∀ i ∈ s, (A i - (e i : ℂ) • 1).PosSemidef := by
    intro i hi
    obtain ⟨v, _hv, _hunit, hvlow⟩ := hdata i hi
    exact hvlow
  have hattain : ∀ i ∈ s, ∃ v : (Fin L → Fin q) → ℂ,
      star v ⬝ᵥ v = 1 ∧ A i *ᵥ v = (e i : ℂ) • v := by
    intro i hi
    obtain ⟨v, hv, hunit, _hvlow⟩ := hdata i hi
    exact ⟨v, hunit, hv⟩
  obtain ⟨x, hxunit, hx⟩ := exists_common_unit_fixed_ground_of_disjoint_family
    hq s R A e hdisj hsupp hlow hattain
  exact ⟨e, x, hxunit, hx, hlow⟩
end Matrix
end

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

/-- Disjoint positive regional Hamiltonians determine one set of original
ground energies and one common unit vector for every subsequent clipping.
For each clipping subset the centered regional sum is positive, annihilates
that vector, commutes with every original region, and dominates its original
high-energy projections. Adding a bounded positive connecting interaction
gives both an operator-norm budget and an attained relative ground energy
between zero and the connecting-interaction budget.

This is auxiliary to ALVV, arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886,
Corollary `c:goodagsphardtrunc`, lines 979–1005, and Theorem `t:ais`,
lines 1010–1024. The regional minima, common vector and current bounds are
constructed from the original supported operators. -/
theorem exists_disjoint_regional_clipping_structure
    {ι : Type*} [Fintype ι] [DecidableEq ι] {L q : ℕ} (hq : 0 < q)
    (R : ι → Finset (Fin L))
    (A : ι → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (c : ι → ℕ)
    (hdisj : Pairwise fun i j ↦ Disjoint (R i) (R j))
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (A i) (R i))
    (hpos : ∀ i, (A i).PosSemidef)
    (hcap : ∀ i, A i ≤ (c i : ℝ) • (1 : Matrix (Fin L → Fin q)
      (Fin L → Fin q) ℂ))
    (Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (C : ℕ)
    (hY : Y.PosSemidef) (hYC : Y ≤ (C : ℝ) • 1) :
    ∃ (e : ι → ℝ) (x : (Fin L → Fin q) → ℂ),
      star x ⬝ᵥ x = 1 ∧
      (∀ i, A i *ᵥ x = (e i : ℂ) • x) ∧
      (∀ i, (A i - (e i : ℂ) • 1).PosSemidef) ∧
      ∀ (t : ℝ), 0 ≤ t → ∀ T : Finset ι,
        let X := ∑ i, ((if i ∈ T then
          cfc (fun r : ℝ ↦ min r (e i + t)) (A i) else A i) -
            (e i : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
        X.PosSemidef ∧ X *ᵥ x = 0 ∧
        (∀ j, Commute X (A j)) ∧
        (∀ (j : ι) (u : ℝ), 0 ≤ u → u ≤ t →
          u • spectralProjectionGE (A j) (e j + u) ≤ X) ∧
        (X + Y ≤ ((∑ i, if i ∈ T then t else (c i : ℝ)) + (C : ℝ)) • 1) ∧
        (‖X + Y‖ ≤ (∑ i, if i ∈ T then t else (c i : ℝ)) + (C : ℝ)) ∧
        ∃ (E : ℝ) (z : (Fin L → Fin q) → ℂ),
          star z ⬝ᵥ z = 1 ∧ (X + Y) *ᵥ z = (E : ℂ) • z ∧
          (X + Y - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ (C : ℝ) := by
  have : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  obtain ⟨e, x, hxunit, hx, helow⟩ := exists_common_unit_ground_of_disjoint_family
    hq Finset.univ R A (fun i _ ↦ (hpos i).isHermitian)
    (by intro i _ j _ hij; exact hdisj hij) (fun i _ ↦ hsupp i)
  have hxall (i : ι) : A i *ᵥ x = (e i : ℂ) • x := hx i (Finset.mem_univ i)
  have helowall (i : ι) : (A i - (e i : ℂ) • 1).PosSemidef :=
    helow i (Finset.mem_univ i)
  have he (i : ι) : (e i : ℂ) • (1 : Matrix (Fin L → Fin q)
      (Fin L → Fin q) ℂ) ≤ A i := le_iff.mpr (helowall i)
  have hcomm : Pairwise fun i j ↦ Commute (A i) (A j) := by
    intro i j hij
    exact QuantumCircuit.commute_of_mem_supportedOperators
      (Finset.disjoint_coe.mpr (hdisj hij))
      (QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hsupp i))
      (QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hsupp j))
  refine ⟨e, x, hxunit, hxall, helowall, ?_⟩
  intro t ht T X
  obtain ⟨hXpos, hXzero⟩ :=
    centered_partially_clipped_sum_posSemidef_and_mulVec_eq_zero
      A e t T (fun i ↦ (hpos i).isHermitian) he x hxall ht
  obtain ⟨hTotalpos, hTotalcap, hTotalnorm⟩ :=
    centered_partially_clipped_sum_norm_le_budget A e c t T hpos he hcap
      (fun _ ↦ x) hxall (fun _ ↦ hxunit) ht Y C hY hYC
  obtain ⟨E, z, hz, hzunit, hElow⟩ := hTotalpos.isHermitian.exists_unit_eigenvector_le
  have hEb := groundEnergy_bounds_of_positive_boundary_and_zero_test
    X Y (C : ℝ) E hXpos hY
    (by simpa only [Complex.coe_smul] using hYC) x z hXzero hxunit hz hzunit hElow
  refine ⟨hXpos, hXzero, ?_, ?_, hTotalcap, hTotalnorm,
    E, z, hzunit, hz, hElow, hEb.1, hEb.2⟩
  · exact fun j ↦ commute_centered_partially_clipped_sum A e t T hcomm j
  · exact fun j u hu hut ↦ spectralProjectionGE_le_centered_partially_clipped_sum
      A e t u T (fun i ↦ (hpos i).isHermitian) he hu hut j
end Matrix
end
end
end
end
