/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SampledProjector

/-!
# Polynomial bounds for the sampled power projector

For fixed local dimension, positive gap and positive inverse-polynomial precision, the
sample count and simultaneous cut ranks have polynomial bounds whenever the ratio
of ground energy to gap is bounded. The constants are chosen before the chain length
and ground energy.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, Corollary
`c:agsp`, lines 626–649. The normalization dependence is retained explicitly.
-/

namespace TNLean.MPS.AreaLaw

/-- A bound on the ground-energy-to-gap ratio gives a uniform polynomial bound for
 the number of sampled words. LVV13, Corollary `c:agsp`, lines 626–649. -/
theorem exists_sampledProjectorWordCount_polynomial {q : ℕ} (hq : 1 ≤ q) (s : ℕ)
    {c Δ B : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hΔ : 0 < Δ) :
    ∃ (C : ℝ) (p : ℕ), 1 ≤ C ∧ ∀ (L : ℕ) (E₀ : ℝ), 1 ≤ L →
      0 ≤ E₀ → E₀ + 1 ≤ L → E₀ / Δ ≤ B →
      (sampledProjectorWordCount q L E₀ (c / (L : ℝ) ^ s)
        ⌈((L - E₀) / Δ) * Real.log (1 / (c / (L : ℝ) ^ s))⌉₊ : ℝ) ≤ C * (L : ℝ) ^ p := by
  let r := ⌈B⌉₊
  let A := (1 / c) ^ r + 1
  let b := Real.log 8 + Real.log q + 3
  let C := 3 * A ^ 2 / c ^ 2 * b
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hb : 0 ≤ b := by
    dsimp only [b]
    positivity
  have hA : 1 ≤ A := by
    dsimp only [A]
    exact le_add_of_nonneg_left (pow_nonneg (by positivity) _)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C + 2, 2 * (s * r + 1) + (2 * s + 1), by linarith, ?_⟩
  intro L E₀ hL hE₀ hE₀L hEB
  let : NeZero L := ⟨by omega⟩
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLp : (0 : ℝ) < L := by linarith
  have hη : 0 < c / (L : ℝ) ^ s := div_pos hc (pow_pos hLp s)
  have hη1 : c / (L : ℝ) ^ s ≤ 1 := (div_le_one (pow_pos hLp s)).mpr (hc1.trans (one_le_pow₀ hL'))
  let m := ⌈((L - E₀) / Δ) * Real.log (1 / (c / (L : ℝ) ^ s))⌉₊
  let R := powerNormalization L E₀ ^ m + 1
  have hpow : powerNormalization L E₀ ^ m ≤ (1 / c) ^ r * (L : ℝ) ^ (s * r + 1) := by
    calc
      _ ≤ L * (1 / (c / (L : ℝ) ^ s)) ^ (E₀ / Δ) :=
        powerNormalization_pow_ceil_le hE₀ hE₀L hΔ hη hη1
      _ ≤ L * (1 / (c / (L : ℝ) ^ s)) ^ (r : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (one_le_one_div hη hη1)
          (hEB.trans (Nat.le_ceil B))) hLp.le
      _ = _ := by rw [Real.rpow_natCast, one_div_div, div_pow, ← pow_mul, pow_succ]; ring
  have hR : R ≤ A * (L : ℝ) ^ (s * r + 1) := by
    have hpow1 : (1 : ℝ) ≤ (L : ℝ) ^ (s * r + 1) := one_le_pow₀ hL'
    dsimp only [R, A]
    nlinarith only [hpow, hpow1]
  have hR1 : 1 ≤ R := by
    dsimp only [R]
    have := one_le_powerNormalization hE₀ (by linarith : E₀ < L)
    exact le_add_of_nonneg_left (pow_nonneg (by linarith) _)
  have hlog : Real.log (8 * (q : ℝ) ^ L * L ^ 3) ≤ b * L := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
    have h8 : Real.log 8 ≤ Real.log 8 * L :=
      le_mul_of_one_le_right (Real.log_nonneg (by norm_num)) hL'
    have hlogL := Real.log_le_self hLp.le
    dsimp only [b]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [h8, hlogL]
  have hlog0 : 0 ≤ Real.log (8 * (q : ℝ) ^ L * L ^ 3) :=
    Real.log_nonneg (by
      have := one_le_pow₀ (n := L) hq'
      have := one_le_pow₀ (n := 3) hL'
      nlinarith)
  have hquad : 2 * R ^ 2 + 2 * R * (c / (L : ℝ) ^ s) / 3 ≤ 3 * R ^ 2 := by
    have := mul_le_mul_of_nonneg_left hη1 (by linarith : 0 ≤ R)
    nlinarith only [this, hR1, sq_nonneg (R - 1)]
  have hbound : (2 * R ^ 2 + 2 * R * (c / (L : ℝ) ^ s) / 3) / (c / (L : ℝ) ^ s) ^ 2 *
      Real.log (8 * (q : ℝ) ^ L * L ^ 3) ≤ C * (L : ℝ) ^ (2 * (s * r + 1) + (2 * s + 1)) := by
    calc
      _ ≤ (3 * (A * (L : ℝ) ^ (s * r + 1)) ^ 2) / (c / (L : ℝ) ^ s) ^ 2 * (b * L) := by
        apply mul_le_mul _ hlog hlog0 (by positivity)
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact hquad.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith : 0 ≤ R) hR 2) (by norm_num))
      _ = _ := by
        have heq : (L : ℝ) ^ (2 * (s * r + 1) + (2 * s + 1)) =
            ((L : ℝ) ^ (s * r + 1)) ^ 2 * ((L : ℝ) ^ s) ^ 2 * L := by
          rw [pow_add (L : ℝ) (2 * (s * r + 1)) (2 * s + 1),
            pow_add (L : ℝ) (2 * s) 1, Nat.mul_comm 2 (s * r + 1), Nat.mul_comm 2 s]
          simp only [pow_mul, pow_one]
          ring
        dsimp only [C]
        rw [div_pow, heq]
        field_simp
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ (2 * R ^ 2 + 2 * R * (c / (L : ℝ) ^ s) / 3) / (c / (L : ℝ) ^ s) ^ 2 *
      Real.log (8 * (q : ℝ) ^ L * L ^ 3) by positivity)
  have hLpown : (1 : ℝ) ≤ (L : ℝ) ^ (2 * (s * r + 1) + (2 * s + 1)) := one_le_pow₀ hL'
  change ((⌈(2 * R ^ 2 + 2 * R * (c / (L : ℝ) ^ s) / 3) / (c / (L : ℝ) ^ s) ^ 2 *
    Real.log (8 * (q : ℝ) ^ L * L ^ 3)⌉₊ + 1 : ℕ) : ℝ) ≤ _
  push_cast
  nlinarith only [hceil, hbound, hLpown]


/-- The simultaneous letter bound grows logarithmically in the length, uniformly
under a fixed ground-energy-to-gap bound. LVV13, Corollary `c:agsp`, lines 626–649. -/
theorem exists_sampledProjectorLetterBound_logarithmic {q : ℕ} (hq : 1 ≤ q) (s : ℕ)
    {c Δ B : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hΔ : 0 < Δ) :
    ∃ A b : ℝ, 0 ≤ A ∧ 0 ≤ b ∧ ∀ (L : ℕ) (E₀ : ℝ), 1 ≤ L →
      0 ≤ E₀ → E₀ + 1 ≤ L → E₀ / Δ ≤ B →
      let m := ⌈((L - E₀) / Δ) * Real.log (1 / (c / (L : ℝ) ^ s))⌉₊
      let ℓ := sampledProjectorWordCount q L E₀ (c / (L : ℝ) ^ s) m
      (sampledProjectorLetterBound L ℓ m : ℝ) ≤ A * Real.log L + b := by
  obtain ⟨C, p, hC, hcount⟩ :=
    exists_sampledProjectorWordCount_polynomial (B := B) hq s hc hc1 hΔ
  let Q := Real.log (1 / c)
  have hQ : 0 ≤ Q := Real.log_nonneg (one_le_one_div hc hc1)
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  let A := 2 * s / Δ + 2 * ((p : ℝ) + 4)
  let b := 2 * Q / Δ + 3 + 2 * Real.log (4 * C)
  have h4C : 0 < 4 * C := by positivity
  have hlog4C : 0 ≤ Real.log (4 * C) := Real.log_nonneg (by linarith)
  refine ⟨A, b, by dsimp only [A]; positivity, by dsimp only [b]; positivity, ?_⟩
  intro L E₀ hL hE₀ hE₀L hEB m ℓ
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLp : (0 : ℝ) < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL'
  have hη : 0 < c / (L : ℝ) ^ s := div_pos hc (pow_pos hLp s)
  have hη1 : c / (L : ℝ) ^ s ≤ 1 := (div_le_one (pow_pos hLp s)).mpr (hc1.trans (one_le_pow₀ hL'))
  have hlog : Real.log (1 / (c / (L : ℝ) ^ s)) = Q + s * Real.log L := by
    rw [one_div_div, Real.log_div (pow_pos hLp s).ne' hc.ne', Real.log_pow]
    dsimp only [Q]
    rw [Real.log_div (by norm_num) hc.ne', Real.log_one]
    ring
  have hx : 0 ≤ ((L - E₀) / Δ) * Real.log (1 / (c / (L : ℝ) ^ s)) := by
    rw [hlog]
    exact mul_nonneg (div_nonneg (by linarith) hΔ.le)
      (add_nonneg hQ (mul_nonneg (Nat.cast_nonneg s) hlogL))
  have hm : (m : ℝ) ≤ (L / Δ) * (Q + s * Real.log L) + 1 := by
    refine (Nat.ceil_lt_add_one hx).le.trans ?_
    rw [hlog]
    gcongr
    linarith
  have hmdiv : (m : ℝ) / L ≤ (Q + s * Real.log L) / Δ + 1 := by
    apply (div_le_iff₀ hLp).mpr
    calc
      _ ≤ (L / Δ) * (Q + s * Real.log L) + 1 := hm
      _ ≤ (L / Δ) * (Q + s * Real.log L) + L := add_le_add_right hL' _
      _ = _ := by ring
  have hℓ : (ℓ : ℝ) ≤ C * (L : ℝ) ^ p := hcount L E₀ hL hE₀ hE₀L hEB
  have hℓ1 : (1 : ℝ) ≤ ℓ := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne ℓ)
  have hlogℓ : Real.log ℓ ≤ Real.log C + (p : ℝ) * Real.log L := by
    calc
      _ ≤ Real.log (C * (L : ℝ) ^ p) := Real.log_le_log (by linarith) hℓ
      _ = _ := by rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hlogprod : Real.log (4 * (ℓ : ℝ) * L ^ 4) ≤
      Real.log (4 * C) + ((p : ℝ) + 4) * Real.log L := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      Real.log_mul (by norm_num) (by positivity : C ≠ 0)]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hlogℓ]
  have hlogprod0 : 0 ≤ Real.log (4 * (ℓ : ℝ) * L ^ 4) :=
    Real.log_nonneg (by
      have hpow : (1 : ℝ) ≤ (L : ℝ) ^ 4 := one_le_pow₀ hL'
      nlinarith)
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ 2 * (m : ℝ) / L + 2 * Real.log (4 * (ℓ : ℝ) * L ^ 4) by positivity)
  change (⌈2 * (m : ℝ) / L + 2 * Real.log (4 * (ℓ : ℝ) * L ^ 4)⌉₊ : ℝ) ≤ _
  dsimp only [A, b]
  have hmdiv' : 2 * (m : ℝ) / L ≤ 2 * Q / Δ + (2 * s / Δ) * Real.log L + 2 := by
    calc
      _ = 2 * ((m : ℝ) / L) := by ring
      _ ≤ 2 * ((Q + s * Real.log L) / Δ + 1) := mul_le_mul_of_nonneg_left hmdiv (by norm_num)
      _ = _ := by ring
  nlinarith only [hceil, hmdiv', hlogprod]


/-- One polynomial bounds the number of sampled factors and their simultaneous
operator Schmidt ranks. Its constants precede length and ground energy.
LVV13, Claim `c:errorreduction`, lines 584–591, and Corollary `c:agsp`, lines 626–649. -/
theorem exists_sampledProjector_uniform_polynomial {q : ℕ} (hq : 1 ≤ q) (s : ℕ)
    {c Δ B : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hΔ : 0 < Δ) :
    ∃ C p : ℕ, 1 ≤ C ∧ ∀ (L : ℕ) (E₀ : ℝ), 1 ≤ L →
      0 ≤ E₀ → E₀ + 1 ≤ L → E₀ / Δ ≤ B →
      let m := ⌈((L - E₀) / Δ) * Real.log (1 / (c / (L : ℝ) ^ s))⌉₊
      let ℓ := sampledProjectorWordCount q L E₀ (c / (L : ℝ) ^ s) m
      let D := q ^ (2 * sampledProjectorLetterBound L ℓ m)
      ℓ * D ≤ C * L ^ p ∧ D ≤ C * L ^ p := by
  obtain ⟨C, p, hC, hcount⟩ :=
    exists_sampledProjectorWordCount_polynomial (B := B) hq s hc hc1 hΔ
  obtain ⟨A, b, hA, hb, hletters⟩ :=
    exists_sampledProjectorLetterBound_logarithmic (B := B) hq s hc hc1 hΔ
  let d := ⌈2 * A * Real.log q⌉₊
  let K := Real.exp (2 * b * Real.log q)
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0 : ℝ) < q := by linarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq'
  have hK : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  refine ⟨⌈C * K⌉₊, p + d, ?_, ?_⟩
  · exact_mod_cast (show (1 : ℝ) ≤ (⌈C * K⌉₊ : ℝ) from
      (one_le_mul_of_one_le_of_one_le hC hK).trans (Nat.le_ceil _))
  · intro L E₀ hL hE₀ hE₀L hEB m ℓ D
    have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hLp : (0 : ℝ) < L := by linarith
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL'
    have hκ : (sampledProjectorLetterBound L ℓ m : ℝ) ≤ A * Real.log L + b :=
      hletters L E₀ hL hE₀ hE₀L hEB
    have hexponent : (2 * (sampledProjectorLetterBound L ℓ m : ℝ)) * Real.log q ≤
        (d : ℝ) * Real.log L + 2 * b * Real.log q := by
      have hfirst := mul_le_mul_of_nonneg_right hκ (by positivity : 0 ≤ 2 * Real.log q)
      have hd : 2 * A * Real.log q ≤ (d : ℝ) := Nat.le_ceil _
      have hsecond := mul_le_mul_of_nonneg_right hd hlogL
      nlinarith only [hfirst, hsecond]
    have hD : (D : ℝ) ≤ K * (L : ℝ) ^ d := by
      calc
        _ = Real.exp ((2 * (sampledProjectorLetterBound L ℓ m : ℝ)) * Real.log q) := by
          have he : Real.exp (((2 * sampledProjectorLetterBound L ℓ m : ℕ) : ℝ) *
              Real.log q) = (q : ℝ) ^ (2 * sampledProjectorLetterBound L ℓ m) := by
            rw [Real.exp_nat_mul, Real.exp_log hqp]
          simpa only [D, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using he.symm
        _ ≤ Real.exp ((d : ℝ) * Real.log L + 2 * b * Real.log q) :=
          Real.exp_le_exp.mpr hexponent
        _ = K * (L : ℝ) ^ d := by
          rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hLp]
          exact mul_comm _ _
    have hboth : ℓ * D ≤ ⌈C * K⌉₊ * L ^ (p + d) := by
      have hreal := mul_le_mul (hcount L E₀ hL hE₀ hE₀L hEB) hD
        (Nat.cast_nonneg D) (by positivity : 0 ≤ C * (L : ℝ) ^ p)
      have hreal' : (ℓ : ℝ) * D ≤ (⌈C * K⌉₊ : ℝ) * (L : ℝ) ^ (p + d) := by
        calc
          _ ≤ (C * (L : ℝ) ^ p) * (K * (L : ℝ) ^ d) := hreal
          _ = (C * K) * (L : ℝ) ^ (p + d) := by rw [pow_add]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
      exact_mod_cast hreal'
    exact ⟨hboth, (Nat.le_mul_of_pos_left D (Nat.pos_of_neZero ℓ)).trans hboth⟩

end TNLean.MPS.AreaLaw
