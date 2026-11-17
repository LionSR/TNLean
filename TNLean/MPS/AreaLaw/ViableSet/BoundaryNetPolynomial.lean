/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundaryNet

/-!
# Polynomial growth of the boundary net

For fixed local dimension `q`, bond bound `D` and error constant `c > 0`, the boundary
net at radius `c / (2L)` has size at most `C L^p`, where `p = 2(qD)²` and
`C = (2 ⌈2(qD)²/c⌉ + 1)^p`. The coefficient and degree are independent of the chain length.
The same bound applies to the net on every actual bond of dimension at most `D`.

This makes explicit the polynomial-size assertion in Landau, Vazirani and Vidick,
arXiv:1307.5143v1, Claim 2.7, `algo53.tex`, lines 519–527.

**Local fix (net cardinality):** The degree uses the corrected quadratic dependence on
the matrix dimension, rather than the printed linear exponent; the correction is documented
in https://sirui-lu.com/QICLean/paper-gaps/lvv13_trace_norm_net.pdf.
-/

open Matrix

namespace TNLean.MPS.AreaLaw

/-- The corrected boundary-net bound at radius `c / (2L)` is bounded by an explicit
polynomial in the chain length. This is the cardinality estimate used in LVV13,
arXiv:1307.5143v1, Claim 2.7, `algo53.tex`, lines 519–527, with the corrected exponent
documented in the module docstring. -/
theorem boundaryNet_card_bound_le_polynomial {L q D : ℕ} (hL : 1 ≤ L) {c : ℝ}
    (_hc : 0 < c) :
    let p := 2 * (q * D) ^ 2
    let A := ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊
    (2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ + 1) ^ p ≤
      (2 * A + 1) ^ p * L ^ p := by
  dsimp only
  have hreal := mul_le_mul_of_nonneg_left
    (Nat.le_ceil (2 * ((q * D : ℕ) : ℝ) ^ 2 / c)) (Nat.cast_nonneg L)
  have hceil : ⌈((q * D : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ ≤
      L * ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊ := by
    apply Nat.ceil_le.mpr
    simpa only [Nat.cast_mul, div_div_eq_mul_div, mul_div_assoc, mul_comm, mul_left_comm,
      mul_assoc] using hreal
  have hbase : 2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ + 1 ≤
      (2 * ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊ + 1) * L := by
    nlinarith only [hceil, hL]
  exact (Nat.pow_le_pow_left hbase (2 * (q * D) ^ 2)).trans_eq (mul_pow _ _ _)

/-- At radius `c / (2L)`, a net on the actual site-and-bond boundary space has size
bounded by an explicit polynomial in `L`. Chain form of the net used in LVV13,
arXiv:1307.5143v1, Claim 2.7, `algo53.tex`, lines 519–527, with the corrected exponent
documented in the module docstring. -/
theorem exists_finset_boundary_rectangularTraceNorm_net_polynomial {L q k m D : ℕ}
    (hq : 1 ≤ q) (hL : 1 ≤ L) {c : ℝ} (hc : 0 < c) (hm : m ≤ D) :
    let p := 2 * (q * D) ^ 2
    let A := ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊
    ∃ N : Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ),
      N.card ≤ (2 * A + 1) ^ p * L ^ p ∧
      ∀ Y : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ,
        rectangularTraceNorm Y ≤ 1 →
          ∃ X ∈ N, rectangularTraceNorm (Y - X) ≤ c / (2 * L) := by
  classical
  have hη : 0 < c / (2 * L) :=
    div_pos hc (mul_pos (by norm_num)
      (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hL)))
  obtain ⟨N, hN, hcover⟩ :=
    exists_finset_boundary_rectangularTraceNorm_net (L := L) (k := k) hq hη hm
  exact ⟨N, hN.trans (boundaryNet_card_bound_le_polynomial (q := q) (D := D) hL hc), hcover⟩

/-- At radius `c / (2L)`, the boundary net may be chosen with Hermitian centers while
retaining the same polynomial cardinality bound. This is the form suited to the
semidefinite-program formulation of LVV13, arXiv:1307.5143v1, Claim 2.7,
`algo53.tex`, lines 472–478 and 519–527. -/
theorem exists_finset_hermitian_boundary_rectangularTraceNorm_net_polynomial
    {L q k m D : ℕ} (hq : 1 ≤ q) (hL : 1 ≤ L) {c : ℝ} (hc : 0 < c) (hm : m ≤ D) :
    let p := 2 * (q * D) ^ 2
    let A := ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊
    ∃ N : Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ),
      N.card ≤ (2 * A + 1) ^ p * L ^ p ∧
      (∀ X ∈ N, X.IsHermitian) ∧
      ∀ Y : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ,
        Y.IsHermitian → rectangularTraceNorm Y ≤ 1 →
          ∃ X ∈ N, rectangularTraceNorm (Y - X) ≤ c / (2 * L) := by
  classical
  have hη : 0 < c / (2 * L) :=
    div_pos hc (mul_pos (by norm_num)
      (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hL)))
  obtain ⟨N, hN, hNherm, hcover⟩ :=
    exists_finset_hermitian_boundary_rectangularTraceNorm_net
      (L := L) (k := k) hq hη hm
  exact ⟨N, hN.trans (boundaryNet_card_bound_le_polynomial (q := q) (D := D) hL hc),
    hNherm, hcover⟩

/-- Boundary nets for all actual bond dimensions up to `D` can be chosen with
polynomial total cardinality. Consequently, at a fixed cut, the
size-trimming construction poses at most this many boundary-constrained
minimization problems. LVV13, Claim 2.7, `algo53.tex`, lines 472–478 and
519–527, with the corrected net exponent documented in the module docstring. -/
theorem exists_boundaryNets_polynomial_total_cardinality {L q k D : ℕ}
    (hq : 1 ≤ q) (hL : 1 ≤ L) {c : ℝ} (hc : 0 < c) :
    let p := 2 * (q * D) ^ 2
    let A := ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊
    ∃ N : (m : Fin (D + 1)) →
        Finset (Matrix (CutSite L q k × Fin m.val) (CutSite L q k × Fin m.val) ℂ),
      (∀ m, (N m).card ≤ (2 * A + 1) ^ p * L ^ p) ∧
      (∀ (m) (Y : Matrix (CutSite L q k × Fin m.val)
          (CutSite L q k × Fin m.val) ℂ),
        rectangularTraceNorm Y ≤ 1 →
          ∃ X ∈ N m, rectangularTraceNorm (Y - X) ≤ c / (2 * L)) ∧
      (∑ m, (N m).card) ≤ (D + 1) * (2 * A + 1) ^ p * L ^ p := by
  classical
  intro p A
  choose N hN hcover using fun m : Fin (D + 1) ↦
    exists_finset_boundary_rectangularTraceNorm_net_polynomial
      (L := L) (q := q) (k := k) (D := D) hq hL hc (Nat.le_of_lt_succ m.isLt)
  refine ⟨N, hN, hcover, ?_⟩
  calc
    (∑ m, (N m).card) ≤
        ∑ _m : Fin (D + 1), (2 * A + 1) ^ p * L ^ p :=
      Finset.sum_le_sum fun m _ ↦ hN m
    _ = (D + 1) * (2 * A + 1) ^ p * L ^ p := by
      simp [Nat.mul_assoc]

/-- Across all positive cuts of a chain, the total number of boundary-net
points, and hence the number of boundary-constrained minimization problems in
the size-trimming sweep, has one additional power of the chain length. -/
theorem exists_boundaryNets_sweep_polynomial_total_cardinality {L q D : ℕ}
    (hq : 1 ≤ q) (hL : 1 ≤ L) {c : ℝ} (hc : 0 < c) :
    let p := 2 * (q * D) ^ 2
    let A := ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊
    ∃ N : (i : Fin L) → (m : Fin (D + 1)) →
        Finset (Matrix (CutSite L q (i.val + 1) × Fin m.val)
          (CutSite L q (i.val + 1) × Fin m.val) ℂ),
      (∀ (i) (m) (Y : Matrix (CutSite L q (i.val + 1) × Fin m.val)
          (CutSite L q (i.val + 1) × Fin m.val) ℂ),
        rectangularTraceNorm Y ≤ 1 →
          ∃ X ∈ N i m, rectangularTraceNorm (Y - X) ≤ c / (2 * L)) ∧
      (∑ i, ∑ m, (N i m).card) ≤
        (D + 1) * (2 * A + 1) ^ p * L ^ (p + 1) := by
  classical
  intro p A
  choose N _hcard hcover htotal using fun i : Fin L ↦
    exists_boundaryNets_polynomial_total_cardinality
      (L := L) (q := q) (k := i.val + 1) (D := D) hq hL hc
  refine ⟨N, hcover, ?_⟩
  calc
    (∑ i, ∑ m, (N i m).card) ≤
        ∑ _i : Fin L, (D + 1) * (2 * A + 1) ^ p * L ^ p :=
      Finset.sum_le_sum fun i _ ↦ htotal i
    _ = (D + 1) * (2 * A + 1) ^ p * L ^ (p + 1) := by
      rw [pow_succ]
      simp
      ring

end TNLean.MPS.AreaLaw
