/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Module.Projective
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Word values of a functional under two spanning letter families

Let `φ` be a linear functional on a complex algebra that is nondegenerate on the
left, `φ (M * N) = 0` for all `N` forcing `M = 0`, and let `x` and `y` be two
spanning families of letters. If the values of `φ` on the words of lengths one,
two and three in `y` are constant multiples of the values on the same words in
`x`, then the value on every word in `y` is the length-th power of the
one-letter constant times the value on the word in `x`.

This comparison makes the phase of a symmetry of a matrix product vector
multiplicative in the length (arXiv:1010.3732, lines 655--657 and 2590--2593).
The statement concerns an arbitrary algebra and functional, so it lives here
rather than with its parent-Hamiltonian consumer.
-/

open scoped BigOperators

namespace LinearMap

/-- Let \(\phi\) be a functional on an algebra with \(\phi(1)\neq0\) such that
\(\phi(MN)=0\) for every \(N\) forces \(M=0\), and let \((x_i)\) and \((y_i)\) be two
spanning families of letters. If \(\phi(y_w)=c_n\phi(x_w)\) for every word \(w\) of length
\(n\in\{1,2,3\}\), then \(\phi(y_w)=c_1^{|w|}\phi(x_w)\) for every word \(w\).

This is the comparison of words of length \(N\) with their one-letter extensions that makes
the phase \(\lambda_{g,N}\) of a symmetry of the matrix product vectors multiplicative in
the length; the source does not spell out this step. Source context: arXiv:1010.3732,
lines 655--657 (a symmetry \(U_g^{\otimes N}\) of the MPS) and lines 2590--2593 (such an
MPS is invariant under \(U_g\) up to a phase). -/
theorem map_list_prod_eq_pow_mul_of_length_three
    {𝔄 : Type*} [Ring 𝔄] [Algebra ℂ 𝔄] (φ : 𝔄 →ₗ[ℂ] ℂ)
    (hφ : ∀ M : 𝔄, (∀ N, φ (M * N) = 0) → M = 0) (hφ1 : φ 1 ≠ 0)
    {ι : Type*} [Finite ι] (x y : ι → 𝔄)
    (hx : Submodule.span ℂ (Set.range x) = ⊤) (hy : Submodule.span ℂ (Set.range y) = ⊤)
    (c₁ c₂ c₃ : ℂ)
    (h₁ : ∀ i, φ (y i) = c₁ * φ (x i))
    (h₂ : ∀ i j, φ (y i * y j) = c₂ * φ (x i * x j))
    (h₃ : ∀ i j k, φ (y i * y j * y k) = c₃ * φ (x i * x j * x k)) :
    ∀ w : List ι, φ (w.map y).prod = c₁ ^ w.length * φ (w.map x).prod := by
  classical
  have := Fintype.ofFinite ι
  -- the linear map sending each letter \(x_i\) to \(y_i\)
  set a := Fintype.linearCombination ℂ x
  set b := Fintype.linearCombination ℂ y
  have ha : LinearMap.range a = ⊤ := by rw [Fintype.range_linearCombination, hx]
  -- vanishing of \(N\mapsto\phi(MN)\) on the letters \(y_i\) forces \(M=0\)
  have hzero_y : ∀ M : 𝔄, (∀ j, φ (M * y j) = 0) → M = 0 := by
    intro M hM
    refine hφ M fun N => ?_
    have h := LinearMap.ext_on_range hy (f := φ ∘ₗ LinearMap.mulLeft ℂ M) (g := 0)
      (fun j => by simpa using hM j)
    simpa using LinearMap.congr_fun h N
  have hexp : ∀ (v : ι → 𝔄) (c : ι → ℂ) (z : 𝔄),
      φ (Fintype.linearCombination ℂ v c * z) = ∑ i, c i * φ (v i * z) := by
    intro v c z
    simp [Fintype.linearCombination_apply, Finset.sum_mul]
  have hker : ∀ c, a c = 0 → b c = 0 := by
    intro c hc
    refine hzero_y _ fun j => ?_
    have hc' : φ (a c * x j) = 0 := by rw [hc, zero_mul, map_zero]
    rw [hexp] at hc'
    rw [hexp]
    simp only [h₂]
    calc _ = c₂ * ∑ i, c i * φ (x i * x j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [hc', mul_zero]
  obtain ⟨s, hs⟩ := a.exists_rightInverse_of_surjective ha
  set L := b ∘ₗ s
  have hLa : ∀ c, L (a c) = b c := by
    intro c
    have h : a (s (a c) - c) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hs, LinearMap.id_apply, sub_self]
    have := hker _ h
    rw [map_sub, sub_eq_zero] at this
    simpa [L] using this
  have hLx : ∀ i, L (x i) = y i := by
    intro i
    have := hLa (Pi.single i 1)
    simpa [a, b, Fintype.linearCombination_apply, Pi.single_apply] using this
  have hLsurj : ∀ N : 𝔄, ∃ Z, L Z = N := by
    have hle : Submodule.span ℂ (Set.range y) ≤ LinearMap.range L := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨x i, hLx i⟩
    rw [hy, top_le_iff] at hle
    intro N
    exact LinearMap.range_eq_top.mp hle N
  have hzero_L : ∀ M : 𝔄, (∀ Z, φ (M * L Z) = 0) → M = 0 := by
    intro M hM
    refine hφ M fun N => ?_
    obtain ⟨Z, rfl⟩ := hLsurj N
    exact hM Z
  -- multilinear forms of the three trace relations
  have m₁ : ∀ X, φ (L X) = c₁ * φ X := by
    intro X
    have h := LinearMap.ext_on_range hx (f := φ ∘ₗ L) (g := c₁ • φ)
      (fun i => by simp [hLx, h₁])
    simpa using LinearMap.congr_fun h X
  have m₂ : ∀ X Y, φ (L X * L Y) = c₂ * φ (X * Y) := by
    have hi : ∀ i Y, φ (y i * L Y) = c₂ * φ (x i * Y) := by
      intro i Y
      have h := LinearMap.ext_on_range hx (f := φ ∘ₗ LinearMap.mulLeft ℂ (y i) ∘ₗ L)
        (g := c₂ • (φ ∘ₗ LinearMap.mulLeft ℂ (x i))) (fun j => by simp [hLx, h₂])
      simpa using LinearMap.congr_fun h Y
    intro X Y
    have h := LinearMap.ext_on_range hx (f := φ ∘ₗ LinearMap.mulRight ℂ (L Y) ∘ₗ L)
      (g := c₂ • (φ ∘ₗ LinearMap.mulRight ℂ Y)) (fun i => by simp [hLx, hi])
    simpa using LinearMap.congr_fun h X
  have m₃ : ∀ X Y Z, φ (L X * L Y * L Z) = c₃ * φ (X * Y * Z) := by
    have hij : ∀ i j Z, φ (y i * y j * L Z) = c₃ * φ (x i * x j * Z) := by
      intro i j Z
      have h := LinearMap.ext_on_range hx
        (f := φ ∘ₗ LinearMap.mulLeft ℂ (y i * y j) ∘ₗ L)
        (g := c₃ • (φ ∘ₗ LinearMap.mulLeft ℂ (x i * x j))) (fun k => by
          simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply,
            smul_eq_mul, hLx]
          exact h₃ i j k)
      simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply,
        smul_eq_mul] using LinearMap.congr_fun h Z
    have hi : ∀ i Y Z, φ (y i * L Y * L Z) = c₃ * φ (x i * Y * Z) := by
      intro i Y Z
      have h := LinearMap.ext_on_range hx
        (f := φ ∘ₗ LinearMap.mulRight ℂ (L Z) ∘ₗ LinearMap.mulLeft ℂ (y i) ∘ₗ L)
        (g := c₃ • (φ ∘ₗ LinearMap.mulRight ℂ Z ∘ₗ LinearMap.mulLeft ℂ (x i)))
        (fun j => by
          simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
            LinearMap.smul_apply, smul_eq_mul, hLx]
          exact hij i j Z)
      simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        LinearMap.smul_apply, smul_eq_mul] using LinearMap.congr_fun h Y
    intro X Y Z
    have h := LinearMap.ext_on_range hx
      (f := φ ∘ₗ LinearMap.mulRight ℂ (L Y * L Z) ∘ₗ L)
      (g := c₃ • (φ ∘ₗ LinearMap.mulRight ℂ (Y * Z)))
      (fun i => by
        simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.smul_apply,
          smul_eq_mul, hLx, ← mul_assoc]
        exact hi i Y Z)
    simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.smul_apply,
      smul_eq_mul, mul_assoc] using LinearMap.congr_fun h X
  -- the image of the identity is the scalar \(c_1\)
  have hc₁ : c₁ ≠ 0 := by
    obtain ⟨Z, hZ⟩ := hLsurj 1
    intro h0
    apply hφ1
    rw [← hZ, m₁, h0, zero_mul]
  have hu₂ : c₁ • L 1 = c₂ • (1 : 𝔄) := by
    rw [← sub_eq_zero]
    refine hzero_L _ fun Z => ?_
    rw [sub_mul, map_sub, smul_mul_assoc, smul_mul_assoc, one_mul, map_smul, map_smul,
      m₂, one_mul, m₁, smul_eq_mul, smul_eq_mul]
    ring
  have hc₂ : c₂ = c₁ ^ 2 := by
    have h := congrArg φ hu₂
    rw [map_smul, map_smul, m₁, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h
    have := mul_right_cancel₀ hφ1 h
    rw [← this]; ring
  have hu : L 1 = c₁ • (1 : 𝔄) := by
    rw [hc₂, pow_two, mul_smul] at hu₂
    exact smul_right_injective 𝔄 hc₁ hu₂
  have hmul : ∀ X Y, L X * L Y = c₁ • L (X * Y) := by
    intro X Y
    rw [← sub_eq_zero]
    refine hzero_L _ fun Z => ?_
    have h := m₃ (X * Y) 1 Z
    rw [hu, mul_smul_comm, mul_one, smul_mul_assoc, map_smul, smul_eq_mul, mul_one] at h
    rw [sub_mul, map_sub, m₃, smul_mul_assoc, map_smul, smul_eq_mul, h, sub_self]
  -- induction along the word
  have hword : ∀ (w : List ι) Z,
      (w.map y).prod * L Z = c₁ ^ w.length • L ((w.map x).prod * Z) := by
    intro w
    induction w with
    | nil => intro Z; simp
    | cons i w ih =>
      intro Z
      rw [List.map_cons, List.prod_cons, mul_assoc, ih, mul_smul_comm, ← hLx i, hmul,
        smul_smul, List.map_cons, List.prod_cons, mul_assoc, List.length_cons, pow_succ]
  intro w
  have h := congrArg φ (hword w 1)
  rw [hu, mul_smul_comm, mul_one, mul_one, map_smul, map_smul, m₁, smul_eq_mul,
    smul_eq_mul] at h
  apply mul_left_cancel₀ hc₁
  rw [h]; ring

end LinearMap
