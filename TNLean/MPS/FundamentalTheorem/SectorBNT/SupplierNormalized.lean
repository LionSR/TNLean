/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.Supplier
import TNLean.MPS.SharedInfra.Scaling

/-!
# Normalized SectorBNT supplier after blocking

The canonical form of arXiv:1606.00608 (eq:II_CF1,
`Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 237-246) writes a tensor as
$A^i = \oplus_{k=1}^r \mu_k A_k^i$ with each $A_k$ a normal tensor, and line 246 fixes the
weight normalization: since the states are not normalized, one can always choose
$|\mu_k| \le 1$ with at least one weight of unit modulus, "something which we will assume from
now on."  The supplier `MPSTensor.exists_isBNTCanonicalForm_afterBlocking_pos` leaves that
normalization choice as a hypothesis on the produced weights.  This file discharges it:
dividing every weight by the largest modulus $m = \max_k |\mu_k|$ realizes the line-246
choice, and the discarded factor reappears as the scalar $m^N$ multiplying the length-$N$
matrix product coefficients.

## Main declarations

* `MPSTensor.exists_weight_normalization` — for a nonempty family of nonzero weights
  $\mu_1, \dots, \mu_r$ there is $m > 0$ with $|\mu_k / m| \le 1$ for every $k$, equality for
  some $k$, and $\mu_k / m \ne 0$ for every $k$ (the choice at line 246 of the source, with
  $m = \max_k |\mu_k|$).
* `MPSTensor.exists_isBNTCanonicalForm_afterBlocking_pos_normalized` — for a tensor whose
  blocked matrix product coefficients do not vanish identically at positive lengths, some
  blocking length $p$ admits a basis-of-normal-tensors canonical form $P$ and a scale $m > 0$
  with $V^{(N)}(A^{[p]}) = m^N V^{(N)}(P)$ at every positive length $N$.

## References

* `Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 237-246 — the canonical form eq:II_CF1 and
  the line-246 weight normalization discharged here.
* `Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 271-279 — the basis-of-normal-tensors
  definition and the characterization prop:char-BNT.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- **The weight normalization at line 246 of the source.**

Source: arXiv:1606.00608, `Papers/1606.00608/MPDO-22-12-17-2.tex`, line 246: since the states
are not normalized, one can always choose $|\mu_k| \le 1$ with at least one weight of unit
modulus.  For a nonempty family of nonzero weights $\mu_1, \dots, \mu_r$, dividing by the
largest modulus $m = \max_k |\mu_k| > 0$ produces weights $\mu_k / m$ that are still nonzero,
have modulus at most one, and include one of modulus exactly one. -/
theorem exists_weight_normalization {r : ℕ} (hr : 0 < r)
    (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ (∀ k, ‖μ k / (m : ℂ)‖ ≤ 1) ∧ (∃ k, ‖μ k / (m : ℂ)‖ = 1) ∧
      ∀ k, μ k / (m : ℂ) ≠ 0 := by
  classical
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_mem_eq_sup' hne fun k => ‖μ k‖
  have hle : ∀ k, ‖μ k‖ ≤ Finset.univ.sup' hne fun k => ‖μ k‖ := fun k =>
    Finset.le_sup' (fun k => ‖μ k‖) (Finset.mem_univ k)
  have hm_pos : 0 < Finset.univ.sup' hne fun k => ‖μ k‖ := by
    rw [hk₀]
    exact norm_pos_iff.mpr (hμ k₀)
  have hm_norm : ‖((Finset.univ.sup' hne fun k => ‖μ k‖ : ℝ) : ℂ)‖ =
      Finset.univ.sup' hne fun k => ‖μ k‖ := by
    rw [Complex.norm_real]
    exact Real.norm_of_nonneg hm_pos.le
  have hm_ne : ((Finset.univ.sup' hne fun k => ‖μ k‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hm_pos.ne'
  refine ⟨Finset.univ.sup' hne fun k => ‖μ k‖, hm_pos, ?_, ⟨k₀, ?_⟩,
    fun k => div_ne_zero (hμ k) hm_ne⟩
  · intro k
    rw [norm_div, hm_norm]
    exact (div_le_one hm_pos).mpr (hle k)
  · rw [norm_div, hm_norm, ← hk₀]
    exact div_self hm_pos.ne'

/-- **Normalized arbitrary-input basis-of-normal-tensors supplier (positive length).**

Source: arXiv:1606.00608, `Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 237-246 for the
canonical form eq:II_CF1 with the line-246 weight normalization, and lines 271-279 for the
basis-of-normal-tensors definition and prop:char-BNT.

For a tensor $A$ satisfying the nonvanishing hypothesis below, there are a positive blocking
length $p$, a scale $m > 0$, and a sector decomposition $P$ in basis-of-normal-tensors
canonical form such that at every positive length $N$ the matrix product coefficients satisfy
$V^{(N)}(A^{[p]}) = m^N \, V^{(N)}(P)$, where $A^{[p]}$ denotes the $p$-blocked tensor.  The
scale $m$ is the largest weight modulus of the prepared block family; dividing the weights by
$m$ realizes the line-246 choice $|\mu_k| \le 1$ with some $|\mu_k| = 1$, so the sector
decomposition carries the normalized weights and the factor $m^N$ records the original ones.

The nonvanishing hypothesis: for every blocking length $p > 0$ some positive-length matrix
product coefficient of the $p$-blocked tensor is nonzero.  The prepared block family can be
empty ($r = 0$) exactly when every positive-length coefficient of the blocked tensor
vanishes (for example the zero tensor): the empty direct sum has all positive-length
coefficients zero, and the positive-length agreement transfers this to the blocked tensor.
For an empty weight family the line-246 choice "at least one weight of unit modulus" is
impossible.  Since the length-$N$ coefficients of the $p$-blocked tensor are the
length-$pN$ coefficients of $A$, the hypothesis asks that for every $p > 0$ the
coefficients of $A$ not vanish on all positive multiples of $p$.  This is stronger than
nonvanishing of a single coefficient of $A$; it is quantified over every $p$ because the
blocking length is produced by the construction.

**Scope restriction (blocked nonvanishing):** the source states the line-246 choice for
any tensor and does not carry this hypothesis; it enters only to exclude blocked families
that vanish identically at positive lengths, where the choice is unsatisfiable.  Recorded
in docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex. -/
theorem exists_isBNTCanonicalForm_afterBlocking_pos_normalized
    {d D : ℕ} (A : MPSTensor d D)
    (hNZ : ∀ p : ℕ, 0 < p →
      ∃ N : ℕ, 0 < N ∧ ∃ σ : Fin N → Fin (blockPhysDim d p),
        mpv (blockTensor (d := d) (D := D) A p) σ ≠ 0) :
    ∃ p : ℕ, 0 < p ∧ ∃ m : ℝ, 0 < m ∧
      ∃ P : SectorDecomposition (blockPhysDim d p),
        IsBNTCanonicalForm P ∧
        ∀ N : ℕ, 0 < N → ∀ σ : Fin N → Fin (blockPhysDim d p),
          mpv (blockTensor (d := d) (D := D) A p) σ = (m : ℂ) ^ N * mpv P.toTensor σ := by
  classical
  obtain ⟨p, hp, r, dim, μ, blocks, hDim, hTP, hPrim, hIrr, -, hμne, hSamePos⟩ :=
    exists_prepared_BNT_blocks_afterBlocking_pos (d := d) (D := D) A
  -- The nonvanishing hypothesis forces a nonempty block family.
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with hr0 | hpos
    · exfalso
      obtain ⟨N, hN, σ, hσ⟩ := hNZ p hp
      apply hσ
      rw [hSamePos N hN σ, mpv_toTensorFromBlocks_eq_sum]
      subst hr0
      simp
    · exact hpos
  -- Normalize the weights by the largest modulus.
  obtain ⟨m, hm, hLe, hUnit, hne⟩ := exists_weight_normalization hr μ hμne
  have hm0 : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  -- The block properties do not involve the weights, so the normalized weights feed the
  -- prepared-block constructor directly.
  obtain ⟨P, hSame, hBNT⟩ :=
    exists_isBNTCanonicalForm_of_tp_primitive_irr_blocks
      (d := blockPhysDim d p) (r := r) (dim := dim)
      (fun k => μ k / (m : ℂ)) blocks hDim hTP hPrim hIrr hne hLe hUnit
  refine ⟨p, hp, m, hm, P, hBNT, ?_⟩
  intro N hN σ
  have hμeq : (fun k => (m : ℂ) * (μ k / (m : ℂ))) = μ := by
    funext k
    rw [mul_comm]
    exact div_mul_cancel₀ (μ k) hm0
  calc
    mpv (blockTensor (d := d) (D := D) A p) σ
        = mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) σ :=
      hSamePos N hN σ
    _ = mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (μ := fun k => (m : ℂ) * (μ k / (m : ℂ))) blocks) σ := by
      rw [hμeq]
    _ = (m : ℂ) ^ N * mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (μ := fun k => μ k / (m : ℂ)) blocks) σ :=
      mpv_toTensorFromBlocks_weight_mul_left (m : ℂ) _ blocks σ
    _ = (m : ℂ) ^ N * mpv P.toTensor σ := by
      rw [hSame N σ]

end MPSTensor
