/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Gates.Controlled

/-!
# Low-energy commutators need not vanish without translation invariance

Hastings, *Solving Gapped Hamiltonians Locally*, arXiv:cond-mat/0508554v3, `proj3new.tex`,
Appendix B, lines 1655–1676. On a chain of `m + 3` spin-1/2 sites, take `H_i = S^z_i` for
`i ≥ 3`, `H_0 = S^x_0 + S^y_0`, `H_1 = −S^x_0 − S^z_1` and `H_2 = −S^y_0 + S^z_2`. The terms
acting on site `0` cancel, so `H = ∑_i H_i = −S^z_1 + ∑_{i ≥ 2} S^z_i`, whose ground space is
two-dimensional: spin `1` up, every spin `i ≥ 2` down, and spin `0` free. With `P` the
projection onto the ground space, the compressions `P H_0 P`, `P H_1 P` and `P H_2 P` pairwise
fail to commute, while `P H_0 P` commutes with `P H_i P` for every `i ≥ 3`. So the
compressions of local terms to a degenerate ground space need not commute without
translation invariance, and the failure is localized near site `0`.

**Scope restriction (the terms `H_i`, not their filtered versions):** the source's claim
(line 1656) is that the filtered local approximations `M_i` need not commute in the low-energy
sector. It reaches this from the `H_i` by the unargued remark that for large `q` and `l_proj`
the low-energy commutators of the `M_i` are close to those of the `H_i` (lines 1665–1667).
The theorems here concern the compressions of the `H_i` themselves; that step to the `M_i` is
not formalized. The source's chain is not specified beyond site `0`; sites left of `0`, with
`H_i = S^z_i`, would only add scalars on the ground space, so the chain starts at site `0`.
Documented in `docs/paper-gaps/hastings05_low_energy_example.tex`.

**Local fix (source slips):** the source writes `H = ∑_{i ≠ 0} S^z_i` (line 1660); the sum of
the printed terms is `−S^z_1 + ∑_{i ≥ 2} S^z_i`. The ground space is still two-dimensional,
with spin `1` up, and the commutator claims are unchanged. The source also says `H_0` commutes
in the low-energy sector with `H_i` for `i ≥ 2` (line 1670), while listing the pair `(0, 2)`
as non-commuting just before; the correct range is `i ≥ 3`. Documented in
`docs/paper-gaps/hastings05_low_energy_example.tex`.

Spins are encoded by `Fin 2`, with `0` for up and `1` for down.

## Main results

* `hamiltonian_eq_diagonal`: `H = diagonal E` with `E σ = −s(σ 1) + ∑_{i ≥ 2} s(σ i)`.
* `groundEnergy_le`, `energy_eq_groundEnergy_iff`: `E₀ ≤ E σ`, with equality exactly on the
  ground configurations.
* `hamiltonian_mulVec_eq_iff`: `H v = E₀ v` exactly when `P v = v`.
* `not_commute_compress_term_zero_one`, `not_commute_compress_term_one_two`,
  `not_commute_compress_term_zero_two`: the three compressions pairwise fail to commute.
* `commute_compress_term_zero_of_three_le`: `P H_0 P` commutes with `P H_i P` for `i ≥ 3`.
-/

open Matrix Complex
open QuantumCircuit (siteOp siteOp_apply siteOp_add siteOp_neg siteOp_sub siteOp_diagonal)

namespace TNLean.Lattice.LowEnergyExample

variable {L : ℕ}

/-- The spin-1/2 matrix `S^x`, with `0` for up and `1` for down. -/
noncomputable def spinX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1 / 2; 1 / 2, 0]

/-- The spin-1/2 matrix `S^y`. -/
noncomputable def spinY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I / 2; I / 2, 0]

/-- The spin-1/2 matrix `S^z`, diagonal with `1/2` on up and `-1/2` on down. -/
noncomputable def spinZ : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 0; 0, -1 / 2]

/-- The value of `S^z` on a spin: `1/2` for up and `-1/2` for down. -/
noncomputable def spinValue (a : Fin 2) : ℝ := if a = 0 then 1 / 2 else -1 / 2

/-- `S^z` is diagonal, with the value of the spin on the diagonal. -/
theorem spinZ_eq_diagonal : spinZ = diagonal fun a ↦ (spinValue a : ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [spinZ, spinValue]

/-- `S^z` at the site `i` is diagonal on configurations. -/
theorem siteOp_spinZ (i : Fin L) :
    siteOp i spinZ = diagonal fun σ ↦ (spinValue (σ i) : ℂ) := by
  rw [spinZ_eq_diagonal, siteOp_diagonal]

variable (m : ℕ)

/-- The terms `H_i` of the example on the chain of `m + 3` sites:
`H_0 = S^x_0 + S^y_0`, `H_1 = −S^x_0 − S^z_1`, `H_2 = −S^y_0 + S^z_2`, and `H_i = S^z_i` for
`i ≥ 3`. Hastings, arXiv:cond-mat/0508554v3, lines 1657–1659. -/
noncomputable def term (i : Fin (m + 3)) : Matrix (Fin (m + 3) → Fin 2) (Fin (m + 3) → Fin 2) ℂ :=
  if i = 0 then siteOp 0 spinX + siteOp 0 spinY
  else if i = 1 then -siteOp 0 spinX - siteOp 1 spinZ
  else if i = 2 then -siteOp 0 spinY + siteOp 2 spinZ
  else siteOp i spinZ

/-- The Hamiltonian `H = ∑_i H_i`. -/
noncomputable def hamiltonian : Matrix (Fin (m + 3) → Fin 2) (Fin (m + 3) → Fin 2) ℂ :=
  ∑ i, term m i

/-- The diagonal of `H`: `E σ = −s(σ 1) + ∑_{i ≥ 2} s(σ i)`, the sites `i ≥ 2` being the
`j.succ.succ` for `j : Fin (m + 1)`. -/
noncomputable def energy (σ : Fin (m + 3) → Fin 2) : ℝ :=
  -spinValue (σ 1) + ∑ j : Fin (m + 1), spinValue (σ j.succ.succ)

theorem term_zero : term m 0 = siteOp 0 spinX + siteOp 0 spinY := by simp [term]

theorem term_one : term m 1 = -siteOp 0 spinX - siteOp 1 spinZ := by simp [term]

theorem term_two : term m 2 = -siteOp 0 spinY + siteOp 2 spinZ := by
  have h0 : (2 : Fin (m + 3)) ≠ 0 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m + 3 by omega)]
  have h1 : (2 : Fin (m + 3)) ≠ 1 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m + 3 by omega),
      Nat.mod_eq_of_lt (show 1 < m + 3 by omega)]
  simp [term, h0, h1]

theorem term_succ_succ_succ (j : Fin m) :
    term m j.succ.succ.succ = siteOp j.succ.succ.succ spinZ := by
  have h1 : j.succ.succ.succ ≠ (1 : Fin (m + 3)) := by
    intro h; have := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_one'] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  have h2 : j.succ.succ.succ ≠ (2 : Fin (m + 3)) := by
    intro h; have := congrArg Fin.val h
    simp only [Fin.val_succ] at this
    rw [Fin.val_two] at this; omega
  simp [term, Fin.succ_ne_zero, h1, h2]

/-- **The terms on site `0` cancel.** `H = −S^z_1 + ∑_{i ≥ 2} S^z_i` is diagonal, with diagonal
`energy`. -/
theorem hamiltonian_eq_diagonal :
    hamiltonian m = diagonal fun σ ↦ (energy m σ : ℂ) := by
  unfold hamiltonian
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, term_zero, term_one, term_two,
    term_succ_succ_succ]
  ext σ τ
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.sum_apply,
    siteOp_spinZ, diagonal_apply, energy, Fin.sum_univ_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  split_ifs with h
  · push_cast; ring
  · simp only [Finset.sum_const_zero]; ring

/-! ### The ground space -/

theorem spinValue_bounds (a : Fin 2) : -1 / 2 ≤ spinValue a ∧ spinValue a ≤ 1 / 2 := by
  fin_cases a <;> norm_num [spinValue]

theorem spinValue_eq_neg_half_iff (a : Fin 2) : spinValue a = -1 / 2 ↔ a = 1 := by
  fin_cases a <;> norm_num [spinValue]

theorem spinValue_eq_half_iff (a : Fin 2) : spinValue a = 1 / 2 ↔ a = 0 := by
  fin_cases a <;> norm_num [spinValue]

/-- The ground spin of site `i ≠ 0`: up on site `1` and down elsewhere. -/
def groundSpin (i : Fin (m + 3)) : Fin 2 := if i = 1 then 0 else 1

/-- A ground configuration: spin `1` up, every spin `i ≥ 2` down, spin `0` free. -/
def IsGround (σ : Fin (m + 3) → Fin 2) : Prop := ∀ i, i ≠ 0 → σ i = groundSpin m i

instance : DecidablePred (IsGround m) := fun _ ↦ by unfold IsGround; infer_instance

/-- The ground energy `E₀ = −(m + 2)/2`. -/
noncomputable def groundEnergy : ℝ := -((m : ℝ) + 2) / 2

theorem energy_sub_groundEnergy (σ : Fin (m + 3) → Fin 2) :
    energy m σ - groundEnergy m =
      (1 / 2 - spinValue (σ 1)) + ∑ j : Fin (m + 1), (spinValue (σ j.succ.succ) + 1 / 2) := by
  rw [energy, groundEnergy, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- `E₀ ≤ E σ` for every configuration `σ`. -/
theorem groundEnergy_le (σ : Fin (m + 3) → Fin 2) : groundEnergy m ≤ energy m σ := by
  have h := energy_sub_groundEnergy m σ
  have h1 := (spinValue_bounds (σ 1)).2
  have h2 : 0 ≤ ∑ j : Fin (m + 1), (spinValue (σ j.succ.succ) + 1 / 2) :=
    Finset.sum_nonneg fun j _ ↦ by linarith [(spinValue_bounds (σ j.succ.succ)).1]
  linarith

/-- `E σ = E₀` exactly on the ground configurations. -/
theorem energy_eq_groundEnergy_iff (σ : Fin (m + 3) → Fin 2) :
    energy m σ = groundEnergy m ↔ IsGround m σ := by
  have h := energy_sub_groundEnergy m σ
  have h1 := (spinValue_bounds (σ 1)).2
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))), 0 ≤ spinValue (σ j.succ.succ) + 1 / 2 :=
    fun j _ ↦ by linarith [(spinValue_bounds (σ j.succ.succ)).1]
  have h2 := Finset.sum_nonneg hnn
  constructor
  · intro hE
    have hs1 : spinValue (σ 1) = 1 / 2 := by linarith
    have hsum : ∑ j : Fin (m + 1), (spinValue (σ j.succ.succ) + 1 / 2) = 0 := by linarith
    have hj := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
    intro i hi
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hi
    by_cases hi1 : i = 0
    · subst hi1
      simp only [groundSpin, Fin.succ_zero_eq_one, ↓reduceIte]
      exact (spinValue_eq_half_iff _).1 hs1
    · obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi1
      have hk := hj k (Finset.mem_univ _)
      have hne : k.succ.succ ≠ (1 : Fin (m + 3)) := by
        rw [← Fin.succ_zero_eq_one, Ne, Fin.succ_inj]; exact Fin.succ_ne_zero k
      simp only [groundSpin, hne, ↓reduceIte]
      exact (spinValue_eq_neg_half_iff _).1 (by linarith)
  · intro hg
    have hs1 : σ 1 = 0 := by
      have := hg 1 (by simp); simpa [groundSpin] using this
    have hsum : ∑ j : Fin (m + 1), (spinValue (σ j.succ.succ) + 1 / 2) = 0 :=
      Finset.sum_eq_zero fun k _ ↦ by
        have hne : k.succ.succ ≠ (1 : Fin (m + 3)) := by
          rw [← Fin.succ_zero_eq_one, Ne, Fin.succ_inj]; exact Fin.succ_ne_zero k
        have := hg k.succ.succ (Fin.succ_ne_zero _)
        simp only [groundSpin, hne, ↓reduceIte] at this
        rw [this]; norm_num [spinValue]
    rw [hs1, hsum] at h; norm_num [spinValue] at h; linarith

/-- The projection onto the ground space. -/
noncomputable def groundProj : Matrix (Fin (m + 3) → Fin 2) (Fin (m + 3) → Fin 2) ℂ :=
  diagonal fun σ ↦ if IsGround m σ then 1 else 0

/-- **The ground projection.** `H v = E₀ v` exactly when `P v = v`, so `P` is the projection
onto the eigenspace of `H` for its least eigenvalue `E₀`. -/
theorem hamiltonian_mulVec_eq_iff (v : (Fin (m + 3) → Fin 2) → ℂ) :
    hamiltonian m *ᵥ v = (groundEnergy m : ℂ) • v ↔ groundProj m *ᵥ v = v := by
  rw [hamiltonian_eq_diagonal, groundProj]
  simp only [funext_iff, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  refine forall_congr' fun σ ↦ ?_
  by_cases hg : IsGround m σ
  · simp [hg, (energy_eq_groundEnergy_iff m σ).2 hg]
  · have hne : (energy m σ : ℂ) ≠ groundEnergy m := by
      exact_mod_cast (energy_eq_groundEnergy_iff m σ).not.2 hg
    simp only [hg, ↓reduceIte, zero_mul]
    constructor
    · intro h
      have : ((energy m σ : ℂ) - groundEnergy m) * v σ = 0 := by rw [sub_mul, h, sub_self]
      exact ((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)).symm
    · intro h; rw [← h]; ring

/-! ### Compressions to the ground space -/

/-- The ground configuration with spin `a` on site `0`. -/
def groundConfig (a : Fin 2) : Fin (m + 3) → Fin 2 := fun i ↦ if i = 0 then a else groundSpin m i

theorem isGround_groundConfig (a : Fin 2) : IsGround m (groundConfig m a) := fun i hi ↦ by
  simp [groundConfig, hi]

theorem groundConfig_zero (a : Fin 2) : groundConfig m a 0 = a := by simp [groundConfig]

theorem eq_groundConfig_of_isGround {ρ : Fin (m + 3) → Fin 2} (hρ : IsGround m ρ) :
    ρ = groundConfig m (ρ 0) := by
  funext i
  by_cases hi : i = 0
  · subst hi; simp [groundConfig]
  · simp [groundConfig, hi, hρ i hi]

/-- Summing over the ground configurations is summing over the spin of site `0`. -/
theorem sum_isGround (f : Fin 2 → ℂ) :
    ∑ ρ : Fin (m + 3) → Fin 2, (if IsGround m ρ then f (ρ 0) else 0) = ∑ a, f a := by
  have h : ∀ ρ : Fin (m + 3) → Fin 2,
      (if IsGround m ρ then f (ρ 0) else 0) = ∑ a, if ρ = groundConfig m a then f a else 0 := by
    intro ρ
    by_cases hρ : IsGround m ρ
    · simp only [hρ, ↓reduceIte]
      rw [Finset.sum_eq_single (ρ 0)]
      · simp only [← eq_groundConfig_of_isGround m hρ, ↓reduceIte]
      · intro b _ hb
        have : ρ ≠ groundConfig m b := fun h ↦ hb (by rw [h, groundConfig_zero])
        simp only [this, ↓reduceIte]
      · simp
    · simp only [hρ, ↓reduceIte]
      refine (Finset.sum_eq_zero fun a _ ↦ ?_).symm
      have : ρ ≠ groundConfig m a := by rintro rfl; exact hρ (isGround_groundConfig m a)
      simp only [this, ↓reduceIte]
  simp only [h]
  rw [Finset.sum_comm]
  simp

/-- The compression `P X P` of a matrix to the ground space. -/
noncomputable def compress (X : Matrix (Fin (m + 3) → Fin 2) (Fin (m + 3) → Fin 2) ℂ) :
    Matrix (Fin (m + 3) → Fin 2) (Fin (m + 3) → Fin 2) ℂ :=
  groundProj m * X * groundProj m

theorem compress_apply (X : Matrix (Fin (m + 3) → Fin 2) (Fin (m + 3) → Fin 2) ℂ)
    (σ τ : Fin (m + 3) → Fin 2) :
    compress m X σ τ = if IsGround m σ ∧ IsGround m τ then X σ τ else 0 := by
  simp only [compress, groundProj, mul_diagonal, diagonal_mul]
  by_cases hσ : IsGround m σ <;> by_cases hτ : IsGround m τ <;> simp [hσ, hτ]

/-- On the ground space, an operator on site `0` acts through its `2 × 2` matrix. -/
theorem compress_siteOp_zero_apply (X : Matrix (Fin 2) (Fin 2) ℂ) (σ τ : Fin (m + 3) → Fin 2) :
    compress m (siteOp 0 X) σ τ =
      if IsGround m σ ∧ IsGround m τ then X (σ 0) (τ 0) else 0 := by
  rw [compress_apply]
  split_ifs with h
  · have hag : ∀ j, j ≠ 0 → σ j = τ j := fun j hj ↦ by rw [h.1 j hj, h.2 j hj]
    rw [siteOp_apply, ite_eq_left_of_eq_true _ _ (eq_true hag)]
  · rfl

theorem compress_siteOp_zero_mul (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    compress m (siteOp 0 X) * compress m (siteOp 0 Y) = compress m (siteOp 0 (X * Y)) := by
  ext σ τ
  rw [mul_apply, compress_siteOp_zero_apply]
  simp only [compress_siteOp_zero_apply]
  by_cases hσ : IsGround m σ <;> by_cases hτ : IsGround m τ <;> simp only [hσ, hτ, and_true,
    true_and, and_false, false_and, ↓reduceIte, zero_mul, mul_zero, Finset.sum_const_zero]
  have : ∀ ρ : Fin (m + 3) → Fin 2,
      ((if IsGround m ρ then X (σ 0) (ρ 0) else 0) * if IsGround m ρ then Y (ρ 0) (τ 0) else 0) =
        if IsGround m ρ then X (σ 0) (ρ 0) * Y (ρ 0) (τ 0) else 0 := by
    intro ρ; split_ifs <;> simp
  simp only [this]
  rw [sum_isGround m (fun a ↦ X (σ 0) a * Y a (τ 0)), mul_apply]

/-- On the ground space, the operator `S^z_k` on a site `k ≠ 0` is a scalar. -/
theorem compress_siteOp_spinZ {k : Fin (m + 3)} (hk : k ≠ 0) :
    compress m (siteOp k spinZ) = (spinValue (groundSpin m k) : ℂ) • groundProj m := by
  ext σ τ
  rw [compress_apply, siteOp_spinZ, Matrix.smul_apply, groundProj, diagonal_apply,
    diagonal_apply]
  by_cases hστ : σ = τ
  · subst hστ
    by_cases hσ : IsGround m σ
    · simp [hσ, hσ k hk]
    · simp [hσ]
  · simp [hστ]

theorem compress_add (X Y : Matrix (Fin (m + 3) → Fin 2) (Fin (m + 3) → Fin 2) ℂ) :
    compress m (X + Y) = compress m X + compress m Y := by
  simp [compress, mul_add, add_mul]

theorem compress_neg (X : Matrix (Fin (m + 3) → Fin 2) (Fin (m + 3) → Fin 2) ℂ) :
    compress m (-X) = -compress m X := by
  simp [compress]

theorem compress_sub (X Y : Matrix (Fin (m + 3) → Fin 2) (Fin (m + 3) → Fin 2) ℂ) :
    compress m (X - Y) = compress m X - compress m Y := by
  rw [sub_eq_add_neg, compress_add, compress_neg, ← sub_eq_add_neg]

theorem groundProj_mul_compress (X : Matrix (Fin (m + 3) → Fin 2) (Fin (m + 3) → Fin 2) ℂ) :
    groundProj m * compress m X = compress m X := by
  ext σ τ
  rw [groundProj, diagonal_mul, compress_apply]
  by_cases hσ : IsGround m σ <;> simp [hσ]

theorem compress_mul_groundProj (X : Matrix (Fin (m + 3) → Fin 2) (Fin (m + 3) → Fin 2) ℂ) :
    compress m X * groundProj m = compress m X := by
  ext σ τ
  rw [groundProj, mul_diagonal, compress_apply]
  by_cases hτ : IsGround m τ <;> simp [hτ]

/-- A compression commutes with every scalar multiple of the ground projection. -/
theorem commute_compress_smul_groundProj
    (X : Matrix (Fin (m + 3) → Fin 2) (Fin (m + 3) → Fin 2) ℂ) (c : ℂ) :
    Commute (compress m X) (c • groundProj m) := by
  rw [Commute, SemiconjBy, mul_smul_comm, smul_mul_assoc, compress_mul_groundProj,
    groundProj_mul_compress]

/-- A nonzero `2 × 2` matrix on site `0` has a nonzero compression. -/
theorem compress_siteOp_zero_ne_zero {X : Matrix (Fin 2) (Fin 2) ℂ} {a b : Fin 2}
    (hX : X a b ≠ 0) : compress m (siteOp 0 X) ≠ 0 := by
  intro h
  have := congrFun (congrFun h (groundConfig m a)) (groundConfig m b)
  simp only [compress_siteOp_zero_apply, isGround_groundConfig, and_self, ↓reduceIte,
    groundConfig_zero, Matrix.zero_apply] at this
  exact hX this

/-- Two compressions `P A P + c P` and `P B P + d P` of operators on site `0` plus scalars fail
to commute when `A` and `B` do not commute. -/
theorem not_commute_of_siteOp_zero {A B : Matrix (Fin 2) (Fin 2) ℂ} {a b : Fin 2}
    (hAB : (A * B - B * A) a b ≠ 0) (c d : ℂ) :
    ¬Commute (compress m (siteOp 0 A) + c • groundProj m)
      (compress m (siteOp 0 B) + d • groundProj m) := by
  intro h
  have hPP : ∀ c d : ℂ, Commute (c • groundProj m) (d • groundProj m) := fun c d ↦
    ((Commute.refl _).smul_left c).smul_right d
  have hcD : Commute (c • groundProj m) (compress m (siteOp 0 B) + d • groundProj m) :=
    ((commute_compress_smul_groundProj m _ c).symm).add_right (hPP c d)
  have hA : Commute (compress m (siteOp 0 A)) (compress m (siteOp 0 B) + d • groundProj m) := by
    simpa using h.sub_left hcD
  have hAB' : Commute (compress m (siteOp 0 A)) (compress m (siteOp 0 B)) := by
    simpa using hA.sub_right (commute_compress_smul_groundProj m _ d)
  have hzero : compress m (siteOp 0 (A * B - B * A)) = 0 := by
    rw [siteOp_sub, compress_sub, ← compress_siteOp_zero_mul, ← compress_siteOp_zero_mul,
      hAB'.eq, sub_self]
  exact compress_siteOp_zero_ne_zero m hAB hzero

theorem compress_term_zero :
    compress m (term m 0) = compress m (siteOp 0 (spinX + spinY)) + (0 : ℂ) • groundProj m := by
  rw [term_zero, siteOp_add, zero_smul, add_zero]

theorem compress_term_one :
    compress m (term m 1) = compress m (siteOp 0 (-spinX)) +
      (-(spinValue (groundSpin m 1) : ℂ)) • groundProj m := by
  rw [term_one, sub_eq_add_neg, compress_add, compress_neg, compress_neg,
    compress_siteOp_spinZ m (by simp), siteOp_neg, compress_neg, neg_smul]

theorem compress_term_two :
    compress m (term m 2) = compress m (siteOp 0 (-spinY)) +
      (spinValue (groundSpin m 2) : ℂ) • groundProj m := by
  have h2 : (2 : Fin (m + 3)) ≠ 0 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m + 3 by omega)]
  rw [term_two, compress_add, compress_neg, compress_siteOp_spinZ m h2, siteOp_neg, compress_neg]

/-- **`P H_0 P` and `P H_1 P` do not commute.** Hastings, arXiv:cond-mat/0508554v3,
lines 1665–1667. -/
theorem not_commute_compress_term_zero_one :
    ¬Commute (compress m (term m 0)) (compress m (term m 1)) := by
  rw [compress_term_zero, compress_term_one]
  refine not_commute_of_siteOp_zero m (a := 0) (b := 0) ?_ _ _
  simp [spinX, spinY]
  ring_nf; simp

/-- **`P H_1 P` and `P H_2 P` do not commute.** Hastings, arXiv:cond-mat/0508554v3,
lines 1667–1668. -/
theorem not_commute_compress_term_one_two :
    ¬Commute (compress m (term m 1)) (compress m (term m 2)) := by
  rw [compress_term_one, compress_term_two]
  refine not_commute_of_siteOp_zero m (a := 0) (b := 0) ?_ _ _
  simp [spinX, spinY]
  ring_nf; simp

/-- **`P H_0 P` and `P H_2 P` do not commute.** Hastings, arXiv:cond-mat/0508554v3,
line 1668. -/
theorem not_commute_compress_term_zero_two :
    ¬Commute (compress m (term m 0)) (compress m (term m 2)) := by
  rw [compress_term_zero, compress_term_two]
  refine not_commute_of_siteOp_zero m (a := 0) (b := 0) ?_ _ _
  simp [spinX, spinY]
  ring_nf; simp

/-- **`P H_0 P` commutes with `P H_i P` for `i ≥ 3`**, since `H_i = S^z_i` is a scalar on the
ground space. Hastings, arXiv:cond-mat/0508554v3, line 1669, where the printed range `i ≥ 2`
is corrected to `i ≥ 3` as in the module docstring. -/
theorem commute_compress_term_zero_of_three_le {i : Fin (m + 3)} (hi : 3 ≤ i.val) :
    Commute (compress m (term m 0)) (compress m (term m i)) := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin m, j.succ.succ.succ = i :=
    ⟨⟨i.val - 3, by omega⟩, Fin.ext (by simp; omega)⟩
  rw [term_succ_succ_succ, compress_siteOp_spinZ m (Fin.succ_ne_zero _)]
  exact commute_compress_smul_groundProj m _ _

end TNLean.Lattice.LowEnergyExample
