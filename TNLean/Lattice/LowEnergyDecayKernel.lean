/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyCommutatorSum

/-!
# Decay kernels under successive spectral splits

The cross-block estimate in the basis argument of Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708, takes the square root of
the preceding commutator decay. Iterating square roots retains positivity, symmetry,
and the triangle inequality in multiplicative form. Graph kernels vanish at infinite
distance, so disconnected graphs require no artificial finite distance convention.
-/

namespace TNLean.Lattice

variable {ι : Type*}

/-- Successive square roots of a decay kernel. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1695–1708, with the cross terms retained. -/
noncomputable def sqrtKernel (k : ι → ι → ℝ) : ℕ → ι → ι → ℝ
  | 0 => k
  | n + 1 => fun i j => Real.sqrt (sqrtKernel k n i j)

@[simp]
theorem sqrtKernel_zero (k : ι → ι → ℝ) (i j : ι) : sqrtKernel k 0 i j = k i j := rfl

@[simp]
theorem sqrtKernel_succ (k : ι → ι → ℝ) (n : ℕ) (i j : ι) :
    sqrtKernel k (n + 1) i j = Real.sqrt (sqrtKernel k n i j) := rfl

theorem sqrtKernel_nonneg {k : ι → ι → ℝ} (hk : ∀ i j, 0 ≤ k i j) :
    ∀ n i j, 0 ≤ sqrtKernel k n i j
  | 0, i, j => hk i j
  | _ + 1, _, _ => Real.sqrt_nonneg _

theorem sqrtKernel_le_one {k : ι → ι → ℝ} (hk : ∀ i j, k i j ≤ 1) :
    ∀ n i j, sqrtKernel k n i j ≤ 1
  | 0, i, j => hk i j
  | n + 1, i, j => Real.sqrt_le_one.mpr (sqrtKernel_le_one hk n i j)

theorem sqrtKernel_symm {k : ι → ι → ℝ} (hk : ∀ i j, k i j = k j i) :
    ∀ n i j, sqrtKernel k n i j = sqrtKernel k n j i
  | 0, i, j => hk i j
  | n + 1, i, j => congrArg Real.sqrt (sqrtKernel_symm hk n i j)

theorem sqrtKernel_succ_sq {k : ι → ι → ℝ} (hk : ∀ i j, 0 ≤ k i j) (n : ℕ) (i j : ι) :
    sqrtKernel k (n + 1) i j ^ 2 = sqrtKernel k n i j :=
  Real.sq_sqrt (sqrtKernel_nonneg hk n i j)

theorem sqrtKernel_mono {k : ι → ι → ℝ} (hk0 : ∀ i j, 0 ≤ k i j)
    (hk1 : ∀ i j, k i j ≤ 1) (i j : ι) : Monotone fun n => sqrtKernel k n i j := by
  apply monotone_nat_of_le_succ
  intro n
  rw [sqrtKernel_succ]
  apply Real.le_sqrt_of_sq_le
  have h0 := sqrtKernel_nonneg hk0 n i j
  have h1 := sqrtKernel_le_one hk1 n i j
  nlinarith

/-- The multiplicative triangle inequality persists under taking square roots. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem sqrtKernel_mul_le {k : ι → ι → ℝ} (hk0 : ∀ i j, 0 ≤ k i j)
    (hmul : ∀ i j l, k i j * k j l ≤ k i l) :
    ∀ n i j l, sqrtKernel k n i j * sqrtKernel k n j l ≤ sqrtKernel k n i l
  | 0, i, j, l => hmul i j l
  | n + 1, i, j, l => by
      rw [sqrtKernel_succ, sqrtKernel_succ, sqrtKernel_succ,
        ← Real.sqrt_mul (sqrtKernel_nonneg hk0 n i j)]
      exact Real.sqrt_le_sqrt (sqrtKernel_mul_le hk0 hmul n i j l)

/-- The sum of a kernel over a finite list of selected terms, allowing repeated selections
at different spectral splits. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1695–1708. -/
def listKernelSum (k : ι → ι → ℝ) (s : List ι) (i : ι) : ℝ := (s.map (k i)).sum

@[simp]
theorem listKernelSum_nil (k : ι → ι → ℝ) (i : ι) : listKernelSum k [] i = 0 := rfl

@[simp]
theorem listKernelSum_cons (k : ι → ι → ℝ) (j : ι) (s : List ι) (i : ι) :
    listKernelSum k (j :: s) i = k i j + listKernelSum k s i := rfl

@[simp]
theorem listKernelSum_append (k : ι → ι → ℝ) (s t : List ι) (i : ι) :
    listKernelSum k (s ++ t) i = listKernelSum k s i + listKernelSum k t i := by
  simp only [listKernelSum, List.map_append, List.sum_append]

theorem listKernelSum_nonneg {k : ι → ι → ℝ} (hk : ∀ i j, 0 ≤ k i j)
    (s : List ι) (i : ι) : 0 ≤ listKernelSum k s i := by
  induction s with
  | nil => exact le_rfl
  | cons j s hs => exact add_nonneg (hk i j) hs

/-- Exponential graph decay, set to zero between disconnected components. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `blecm` and lines 1689–1708. -/
noncomputable def graphDecayKernel (G : SimpleGraph ι) (γ : ℝ) (i j : ι) : ℝ :=
  if G.edist i j = ⊤ then 0 else Real.exp (-(γ * ((G.edist i j).toNat : ℝ)))

theorem graphDecayKernel_nonneg (G : SimpleGraph ι) (γ : ℝ) (i j : ι) :
    0 ≤ graphDecayKernel G γ i j := by
  unfold graphDecayKernel
  split_ifs <;> positivity

theorem graphDecayKernel_le_one (G : SimpleGraph ι) {γ : ℝ} (hγ : 0 ≤ γ) (i j : ι) :
    graphDecayKernel G γ i j ≤ 1 := by
  unfold graphDecayKernel
  split_ifs
  · norm_num
  · exact Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hγ (Nat.cast_nonneg _)))

theorem graphDecayKernel_symm (G : SimpleGraph ι) (γ : ℝ) (i j : ι) :
    graphDecayKernel G γ i j = graphDecayKernel G γ j i := by
  simp only [graphDecayKernel, G.edist_comm (u := i) (v := j)]

/-- The graph triangle inequality in multiplicative form, including infinite distances.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem graphDecayKernel_mul_le (G : SimpleGraph ι) {γ : ℝ} (hγ : 0 ≤ γ) (i j l : ι) :
    graphDecayKernel G γ i j * graphDecayKernel G γ j l ≤ graphDecayKernel G γ i l := by
  classical
  by_cases hij : G.edist i j = ⊤
  · simpa only [graphDecayKernel, hij, ↓reduceIte, zero_mul] using
      graphDecayKernel_nonneg G γ i l
  by_cases hjl : G.edist j l = ⊤
  · simpa only [graphDecayKernel, hjl, ↓reduceIte, mul_zero] using
      graphDecayKernel_nonneg G γ i l
  have hsum : G.edist i j + G.edist j l ≠ ⊤ := by simp [hij, hjl]
  have htri := G.edist_triangle (u := i) (v := j) (w := l)
  have hil : G.edist i l ≠ ⊤ := fun h => hsum (top_le_iff.mp (h ▸ htri))
  have hnat := ENat.toNat_le_toNat htri hsum
  rw [ENat.toNat_add hij hjl] at hnat
  have hreal : ((G.edist i l).toNat : ℝ) ≤
      ((G.edist i j).toNat : ℝ) + ((G.edist j l).toNat : ℝ) := by exact_mod_cast hnat
  simp only [graphDecayKernel, hij, hjl, hil, ↓reduceIte]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hreal hγ]

/-- Taking square roots `n` times divides the graph exponential rate by `2^n`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708, with the
cross terms of each spectral refinement retained. -/
theorem sqrtKernel_graphDecayKernel (G : SimpleGraph ι) (γ : ℝ) (n : ℕ) (i j : ι) :
    sqrtKernel (graphDecayKernel G γ) n i j = graphDecayKernel G (γ / 2 ^ n) i j := by
  induction n with
  | zero => simp only [sqrtKernel_zero, pow_zero, div_one]
  | succ n ih =>
    rw [sqrtKernel_succ, ih]
    unfold graphDecayKernel
    split_ifs
    · simp
    · rw [← Real.exp_half]
      congr 1
      rw [pow_succ]
      ring

end TNLean.Lattice
