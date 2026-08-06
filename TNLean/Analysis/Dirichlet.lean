/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dirichlet's simultaneous approximation theorem

**Wolf Lemma 6.1**: Given $m$ real numbers $x_1,\dots,x_m$ and an integer $q>1$,
there exist integers $n,p_1,\dots,p_m$ such that
$$
1 \le n \le q^m \quad\text{and}\quad |x_k n - p_k| \le \frac{1}{q}\quad \forall k.
$$

The proof uses the pigeonhole principle.

Applied to the arguments of finitely many unit-modulus complex numbers, the
theorem yields exponents simultaneously bringing every phase close to one; the
good exponents can be taken arbitrarily large, and a diagonal recursion turns
them into a strictly monotone **recurrent subsequence** along which every phase
tends to one.  This is the Diophantine input to Wolf's Proposition 6.3(i).

## Main results

* `exists_int_near_mul_simultaneous`: the full Wolf Lemma 6.1 statement.
* `exists_ge_pow_sub_one_norm_le`: simultaneous approximate recurrence of
  finitely many unit phases, with arbitrarily large exponents.
* `exists_strictMono_pow_tendsto_one`: the recurrent (Dirichlet) subsequence
  for finitely many unit phases.
-/

namespace Dirichlet

variable {m : ℕ}

private lemma int_toNat_lt_of_nonneg_lt {z : ℤ} {q : ℕ} (hz_nonneg : 0 ≤ z) (hz_lt : z < (q : ℤ)) :
    z.toNat < q := by
  rw [Int.toNat_lt hz_nonneg]
  exact hz_lt

/-- Key lemma: from equal floors of `q * fract(xₖ·n_lo)` and `q * fract(xₖ·n_hi)`,
construct the simultaneous approximation with `n = n_hi - n_lo`. -/
private lemma dirichlet_case (x : Fin m → ℝ) (q : ℕ) (hqpos : q > 0)
    (n_lo n_hi : Fin (q ^ m + 1)) (hlt : n_lo.val < n_hi.val)
    (h_floor_eq_real : ∀ k : Fin m,
      (⌊(q : ℝ) * Int.fract ((x k) * (n_lo.val : ℝ))⌋ : ℝ) =
      (⌊(q : ℝ) * Int.fract ((x k) * (n_hi.val : ℝ))⌋ : ℝ)) :
    ∃ (n : ℕ) (p : Fin m → ℤ), 1 ≤ n ∧ n ≤ q ^ m ∧
      ∀ k : Fin m, |(x k) * (n : ℝ) - (p k : ℝ)| ≤ 1 / (q : ℝ) := by
  have hqpos' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  -- Lemma: equal floors => fractional parts differ by ≤ 1/q
  have fract_bound_lemma (a b : ℝ) (hab : (⌊(q : ℝ) * a⌋ : ℝ) = (⌊(q : ℝ) * b⌋ : ℝ)) :
      |a - b| ≤ 1 / (q : ℝ) := by
    have h_floor_a : (⌊(q : ℝ) * a⌋ : ℝ) ≤ (q : ℝ) * a := Int.floor_le _
    have h_floor_b : (⌊(q : ℝ) * b⌋ : ℝ) ≤ (q : ℝ) * b := Int.floor_le _
    have h_add_a : (q : ℝ) * a < (⌊(q : ℝ) * a⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have h_add_b : (q : ℝ) * b < (⌊(q : ℝ) * b⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have ha_lt : (q : ℝ) * a - (q : ℝ) * b < 1 := by linarith
    have hb_lt : (q : ℝ) * b - (q : ℝ) * a < 1 := by linarith
    have habs_lt_one : |(q : ℝ) * a - (q : ℝ) * b| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    have habs_factor : |(q : ℝ) * a - (q : ℝ) * b| = (q : ℝ) * |a - b| := by
      have h_eq : (q : ℝ) * a - (q : ℝ) * b = (q : ℝ) * (a - b) := by ring
      rw [h_eq, abs_mul, abs_of_nonneg (by exact_mod_cast hqpos.le)]
    rw [habs_factor] at habs_lt_one
    have h_bound : |a - b| < 1 / (q : ℝ) := by
      calc
        |a - b| = ((q : ℝ) * |a - b|) / (q : ℝ) := by field_simp [hqpos'.ne']
        _ < 1 / (q : ℝ) := div_lt_div_of_pos_right habs_lt_one hqpos'
    exact h_bound.le
  set n := n_hi.val - n_lo.val with hn_def
  have hn_pos : 1 ≤ n := by
    have hpos : 0 < n := Nat.sub_pos_of_lt hlt
    omega
  have hmax_hi : n_hi.val ≤ q ^ m := by
    have h := Fin.is_lt n_hi; exact Nat.le_of_lt_succ h
  have hn_le : n ≤ q ^ m := Nat.le_trans (Nat.sub_le _ _) hmax_hi
  have hn_eq_real : (n : ℝ) = (n_hi.val : ℝ) - (n_lo.val : ℝ) := by
    rw [hn_def, Nat.cast_sub (Nat.le_of_lt hlt)]
  -- For each coordinate k, relate (x k)*(n_hi - n_lo) to floor differences and fract differences
  have htarget (k : Fin m) :
      |(x k) * (n : ℝ) - (↑(⌊(x k) * (n_hi.val : ℝ)⌋ - ⌊(x k) * (n_lo.val : ℝ)⌋) : ℝ)| ≤ 1 / (q : ℝ) := by
    have hb := fract_bound_lemma (Int.fract ((x k) * (n_lo.val : ℝ)))
      (Int.fract ((x k) * (n_hi.val : ℝ))) (h_floor_eq_real k)
    have hcalc : (x k) * ((n_hi.val : ℝ) - (n_lo.val : ℝ)) =
        ((⌊(x k) * (n_hi.val : ℝ)⌋ : ℝ) - (⌊(x k) * (n_lo.val : ℝ)⌋ : ℝ)) +
        (Int.fract ((x k) * (n_hi.val : ℝ)) - Int.fract ((x k) * (n_lo.val : ℝ))) := by
      calc
        (x k) * ((n_hi.val : ℝ) - (n_lo.val : ℝ))
            = ((x k) * (n_hi.val : ℝ)) - ((x k) * (n_lo.val : ℝ)) := by ring
        _ = (((⌊(x k) * (n_hi.val : ℝ)⌋ : ℝ) + Int.fract ((x k) * (n_hi.val : ℝ))) -
             ((⌊(x k) * (n_lo.val : ℝ)⌋ : ℝ) + Int.fract ((x k) * (n_lo.val : ℝ)))) := by
          simp [Int.floor_add_fract]
        _ = ((⌊(x k) * (n_hi.val : ℝ)⌋ : ℝ) - (⌊(x k) * (n_lo.val : ℝ)⌋ : ℝ)) +
            (Int.fract ((x k) * (n_hi.val : ℝ)) - Int.fract ((x k) * (n_lo.val : ℝ))) := by ring
    rw [hn_eq_real]
    calc
      |(x k) * ((n_hi.val : ℝ) - (n_lo.val : ℝ)) -
        (↑(⌊(x k) * (n_hi.val : ℝ)⌋ - ⌊(x k) * (n_lo.val : ℝ)⌋) : ℝ)|
          = |(x k) * ((n_hi.val : ℝ) - (n_lo.val : ℝ)) -
            ((⌊(x k) * (n_hi.val : ℝ)⌋ : ℝ) - (⌊(x k) * (n_lo.val : ℝ)⌋ : ℝ))| := by simp
      _ = |Int.fract ((x k) * (n_hi.val : ℝ)) - Int.fract ((x k) * (n_lo.val : ℝ))| := by
        rw [hcalc]; simp
      _ ≤ 1 / (q : ℝ) := by rw [abs_sub_comm]; exact hb
  refine ⟨n, fun k => ⌊(x k) * (n_hi.val : ℝ)⌋ - ⌊(x k) * (n_lo.val : ℝ)⌋,
    hn_pos, hn_le, htarget⟩

/-- **Wolf Lemma 6.1** (Dirichlet's simultaneous approximation theorem). -/
theorem exists_int_near_mul_simultaneous (x : Fin m → ℝ) (q : ℕ) (hq1 : 1 < q) :
    ∃ (n : ℕ) (p : Fin m → ℤ), 1 ≤ n ∧ n ≤ q ^ m ∧
      ∀ k : Fin m, |(x k) * (n : ℝ) - (p k : ℝ)| ≤ 1 / (q : ℝ) := by
  have hqpos : q > 0 := by omega
  -- Floor cell index: ⌊q·{n·xₖ}⌋
  let z (n : ℕ) (k : Fin m) : ℤ := ⌊(q : ℝ) * Int.fract ((x k) * (n : ℝ))⌋
  have hz_nonneg (n : ℕ) (k : Fin m) : 0 ≤ z n k :=
    Int.floor_nonneg.mpr (by nlinarith [Int.fract_nonneg ((x k) * (n : ℝ))])
  have hz_lt (n : ℕ) (k : Fin m) : z n k < (q : ℤ) := by
    dsimp [z]
    have h : (⌊(q : ℝ) * Int.fract ((x k) * (n : ℝ))⌋ : ℝ) < (q : ℝ) := by
      calc
        _ ≤ (q : ℝ) * Int.fract ((x k) * (n : ℝ)) := Int.floor_le _
        _ < (q : ℝ) * 1 := by gcongr; exact Int.fract_lt_one _
        _ = (q : ℝ) := by simp
    exact_mod_cast h
  let cellIdx (n : ℕ) (k : Fin m) : Fin q :=
    ⟨(z n k).toNat, int_toNat_lt_of_nonneg_lt (hz_nonneg n k) (hz_lt n k)⟩
  let f : Fin (q ^ m + 1) → Fin m → Fin q := fun i => cellIdx i.val
  -- Pigeonhole
  have card_lt : Fintype.card (Fin m → Fin q) < Fintype.card (Fin (q ^ m + 1)) := by simp
  obtain ⟨n₁, n₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f card_lt
  -- heq gives cell equality
  have hcell (k : Fin m) : cellIdx n₁.val k = cellIdx n₂.val k := by
    simpa [f] using congrFun heq k
  have h_toNat_eq (k : Fin m) : (z n₁.val k).toNat = (z n₂.val k).toNat := by
    simpa [cellIdx] using congrArg Fin.val (hcell k)
  have h_floor_eq (k : Fin m) : z n₁.val k = z n₂.val k := by
    calc
      z n₁.val k = ((z n₁.val k).toNat : ℤ) := (Int.toNat_of_nonneg (hz_nonneg _ _)).symm
      _ = ((z n₂.val k).toNat : ℤ) := by simp [h_toNat_eq k]
      _ = z n₂.val k := Int.toNat_of_nonneg (hz_nonneg _ _)
  have h_floor_eq_real (k : Fin m) :
      (⌊(q : ℝ) * Int.fract ((x k) * (n₁.val : ℝ))⌋ : ℝ) =
      (⌊(q : ℝ) * Int.fract ((x k) * (n₂.val : ℝ))⌋ : ℝ) := by exact_mod_cast h_floor_eq k
  -- Determine ordering and apply the helper
  have h_vals_ne : (n₁ : ℕ) ≠ (n₂ : ℕ) := by
    intro h_eq; apply hne; exact Fin.ext h_eq
  rcases Nat.lt_or_gt_of_ne h_vals_ne with (hlt | hgt)
  · -- n₁.val < n₂.val
    exact dirichlet_case x q hqpos n₁ n₂ hlt h_floor_eq_real
  · -- n₂.val < n₁.val
    -- The floor equality is symmetric, so we flip the arguments
    refine dirichlet_case x q hqpos n₂ n₁ hgt (fun k => (h_floor_eq_real k).symm)

/-! ## Recurrence of unit phases -/

/-- For a unit-modulus complex number, the distance of `z ^ j` to `1` grows at
most linearly in `j`.  This is the approximate additivity of the set of
recurrence exponents used to reach arbitrarily large exponents. -/
private theorem norm_pow_sub_one_le_mul {z : ℂ} (hz : ‖z‖ = 1) (j : ℕ) :
    ‖z ^ j - 1‖ ≤ j * ‖z - 1‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h : z ^ (j + 1) - 1 = z * (z ^ j - 1) + (z - 1) := by ring
      calc
        ‖z ^ (j + 1) - 1‖ = ‖z * (z ^ j - 1) + (z - 1)‖ := by rw [h]
        _ ≤ ‖z * (z ^ j - 1)‖ + ‖z - 1‖ := norm_add_le _ _
        _ = ‖z ^ j - 1‖ + ‖z - 1‖ := by rw [norm_mul, hz, one_mul]
        _ ≤ j * ‖z - 1‖ + ‖z - 1‖ := by gcongr
        _ = ((j + 1 : ℕ) : ℝ) * ‖z - 1‖ := by push_cast; ring

/-- **Simultaneous approximate recurrence of unit phases, with arbitrarily large
exponents.**  For finitely many complex numbers of norm one, every `ε > 0` and
every threshold `B`, there is an exponent `n ≥ B` simultaneously satisfying
`‖θ_k ^ n - 1‖ ≤ ε`.

Applied to the rescaled arguments `t_k / (2π)` of the phases, Dirichlet's
theorem (`exists_int_near_mul_simultaneous`, Wolf Lemma 6.1) with denominator
`q` yields an exponent `n₀ ∈ [1, q ^ m]` with `‖θ_k ^ n₀ - 1‖ ≤ 4π / q`;
the multiple `n = B * n₀` reaches the prescribed size while inflating the
error by at most the factor `B`.

Source: Wolf, Proposition 6.3(i) proof; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--256. -/
theorem exists_ge_pow_sub_one_norm_le {ι : Type*} [Finite ι] (θ : ι → ℂ)
    (hθ : ∀ k, ‖θ k‖ = 1) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ n : ℕ, B ≤ n ∧ ∀ k, ‖θ k ^ n - 1‖ ≤ ε := by
  classical
  letI := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨B, le_rfl, fun k ↦ isEmptyElim k⟩
  -- Choose arguments for the phases.
  have hphase : ∀ k, ∃ t : ℝ, Complex.exp (t * Complex.I) = θ k :=
    fun k ↦ (Complex.norm_eq_one_iff (θ k)).mp (hθ k)
  choose t ht using hphase
  set e := Fintype.equivFin ι with he_def
  set m := Fintype.card ι with hm_def
  -- Choose the Dirichlet denominator `q`.
  have hπ : 2 * Real.pi < 7 := by linarith [Real.pi_lt_d2]
  obtain ⟨q, hq1, hq7, hqε⟩ :
      ∃ q : ℕ, 1 < q ∧ 7 ≤ q ∧ 4 * Real.pi * B / ε ≤ q := by
    refine ⟨max 7 ⌈4 * Real.pi * B / ε⌉₊ + 1, by omega, by omega, ?_⟩
    calc
      4 * Real.pi * B / ε ≤ (⌈4 * Real.pi * B / ε⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (max 7 ⌈4 * Real.pi * B / ε⌉₊ + 1 : ℕ) := by
        exact_mod_cast (le_max_right 7 _).trans (Nat.le_succ _)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have h2πq : 2 * Real.pi / q ≤ 1 := by
    rw [div_le_one hq0]
    exact hπ.le.trans (by exact_mod_cast hq7)
  -- Dirichlet's theorem applied to the rescaled arguments.
  set x : Fin m → ℝ := fun j ↦ t (e.symm j) / (2 * Real.pi) with hx_def
  obtain ⟨n₀, p, hn₀1, -, hp⟩ := exists_int_near_mul_simultaneous x q hq1
  -- The Dirichlet exponent approximately kills every phase.
  have hper : ∀ k : ι, ‖θ k ^ n₀ - 1‖ ≤ 4 * Real.pi / q := by
    intro k
    have hsymm : e.symm (e k) = k := Equiv.symm_apply_apply e k
    have h2π : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    have htk : t k = 2 * Real.pi * x (e k) := by
      have hx : x (e k) = t k / (2 * Real.pi) := by simp only [hx_def, hsymm]
      rw [hx, mul_div_cancel₀ (t k) h2π]
    have habs : |t k * n₀ - 2 * Real.pi * p (e k)| ≤ 2 * Real.pi / q := by
      have hrew : t k * n₀ - 2 * Real.pi * p (e k) =
          2 * Real.pi * (x (e k) * n₀ - p (e k)) := by
        rw [htk]; ring
      rw [hrew, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      calc
        2 * Real.pi * |x (e k) * n₀ - p (e k)| ≤ 2 * Real.pi * (1 / q) :=
          mul_le_mul_of_nonneg_left (hp (e k)) (by positivity)
        _ = 2 * Real.pi / q := by ring
    have hu_norm : ‖(t k * n₀ - 2 * Real.pi * p (e k) : ℝ) * Complex.I‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact habs.trans h2πq
    have hu : (n₀ : ℂ) * (t k * Complex.I) =
        ((t k * n₀ - 2 * Real.pi * p (e k) : ℝ) * Complex.I) +
          (p (e k) : ℤ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    have hexp : θ k ^ n₀ =
        Complex.exp ((t k * n₀ - 2 * Real.pi * p (e k) : ℝ) * Complex.I) := by
      calc
        θ k ^ n₀ = Complex.exp (t k * Complex.I) ^ n₀ := by rw [ht k]
        _ = Complex.exp ((n₀ : ℂ) * (t k * Complex.I)) := by
          rw [← Complex.exp_nat_mul]
        _ = _ := by
          rw [hu, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    calc
      ‖θ k ^ n₀ - 1‖ =
          ‖Complex.exp ((t k * n₀ - 2 * Real.pi * p (e k) : ℝ) * Complex.I) - 1‖ := by
        rw [hexp]
      _ ≤ 2 * ‖(t k * n₀ - 2 * Real.pi * p (e k) : ℝ) * Complex.I‖ :=
          Complex.norm_exp_sub_one_le hu_norm
      _ = 2 * |t k * n₀ - 2 * Real.pi * p (e k)| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 * (2 * Real.pi / q) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ = 4 * Real.pi / q := by ring
  -- Boosting to a multiple of the Dirichlet exponent reaches size `B`.
  refine ⟨B * n₀, Nat.le_mul_of_pos_right B hn₀1, fun k ↦ ?_⟩
  have hθn : ‖θ k ^ n₀‖ = 1 := by rw [norm_pow, hθ k, one_pow]
  calc
    ‖θ k ^ (B * n₀) - 1‖ = ‖(θ k ^ n₀) ^ B - 1‖ := by rw [pow_mul']
    _ ≤ B * ‖θ k ^ n₀ - 1‖ := norm_pow_sub_one_le_mul hθn B
    _ ≤ B * (4 * Real.pi / q) := mul_le_mul_of_nonneg_left (hper k) (by positivity)
    _ = 4 * Real.pi * B / q := by ring
    _ ≤ ε := by
      rw [div_le_iff₀ hq0, mul_comm ε]
      rw [div_le_iff₀ hε] at hqε
      exact hqε

/-- **Dirichlet's recurrent subsequence for unit phases.**  For finitely many
complex numbers of norm one there is a strictly monotone sequence of positive
integers `n : ℕ → ℕ` with `θ_k ^ (n i) → 1` for every `k`.

The exponents are chosen recursively: `n (i + 1)` is an exponent exceeding
`n i` that simultaneously brings every phase within `1 / (i + 2)` of one,
appealing to `exists_ge_pow_sub_one_norm_le` (Wolf Lemma 6.1) at each step.

Source: Wolf, Proposition 6.3(i); local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--256. -/
theorem exists_strictMono_pow_tendsto_one {ι : Type*} [Finite ι] (θ : ι → ℂ)
    (hθ : ∀ k, ‖θ k‖ = 1) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ 0 < n 0 ∧
      ∀ k, Filter.Tendsto (fun i ↦ θ k ^ n i) Filter.atTop (nhds 1) := by
  classical
  have key : ∀ (i b : ℕ), ∃ n ≥ b, ∀ k, ‖θ k ^ n - 1‖ ≤ ((i : ℝ) + 1)⁻¹ :=
    fun i b ↦ exists_ge_pow_sub_one_norm_le θ hθ (by positivity) b
  choose gn hgn using key
  let n : ℕ → ℕ := fun i ↦ Nat.rec (motive := fun _ ↦ ℕ) (gn 0 1)
    (fun i r ↦ gn (i + 1) (r + 1)) i
  have hn0 : n 0 = gn 0 1 := rfl
  have hns : ∀ i, n (i + 1) = gn (i + 1) (n i + 1) := fun i ↦ rfl
  have hmono : StrictMono n :=
    strictMono_nat_of_lt_succ fun i ↦
      (Nat.lt_succ_self _).trans_le (hns i ▸ (hgn (i + 1) (n i + 1)).1)
  have hpos : 0 < n 0 := hn0 ▸ (hgn 0 1).1
  have hbound : ∀ k, ∀ i, ‖θ k ^ n i - 1‖ ≤ ((i : ℝ) + 1)⁻¹ := by
    intro k i
    cases i with
    | zero => simpa [hn0] using (hgn 0 1).2 k
    | succ i => rw [hns i]; exact (hgn (i + 1) (n i + 1)).2 k
  refine ⟨n, hmono, hpos, fun k ↦ ?_⟩
  have htol : Filter.Tendsto (fun i : ℕ ↦ ((i : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h0 : Filter.Tendsto (fun i ↦ θ k ^ n i - 1) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun i ↦ hbound k i) htol
  have h1 := h0.add_const (1 : ℂ)
  simpa [sub_add_cancel] using h1

end Dirichlet
