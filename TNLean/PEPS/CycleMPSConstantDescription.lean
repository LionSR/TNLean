import TNLean.PEPS.CycleMPSChainOverlapCapstone

import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Translation-invariant description of an injective closed MPS chain

This file delivers the Applications-section corollary of arXiv:1804.04964
(`Papers/1804.04964/paper_normal.tex`, the corollary at line 1804, proof lines
1807--1890) in the uniform physical- and bond-dimension setting: an injective
site-dependent closed chain whose generated state is invariant under the cyclic
shift of the local tensors admits a translation-invariant description by a
single repeated injective tensor `B` of the same bond dimension
(`exists_constant_injectiveMPS_of_cyclicShiftInvariantState`).

The argument follows the source.  Comparing the chain with its cyclic shift
through the injective MPS Fundamental Theorem
(`fundamentalTheorem_injectiveMPSChain_cyclicShift`) supplies one invertible
gauge `Z_v` per bond with `A_{v+1}^i = Z_v A_v^i Z_{v+1}⁻¹`.  Telescoping the
gauges into the running products `P_m = Z_{m-1} ⋯ Z_0` expresses every local
tensor through the first one, `A_m^i = P_m (A_0^i Z_0) P_{m+1}⁻¹`, so the closed
trace collapses to `tr(B^{σ_0} ⋯ B^{σ_{n-1}} P_n⁻¹)` with the tentative repeated
tensor `B = A_0 Z_0`.  Reading the gauge relation across the seam (`A_{n+1} ≡
A_0`) shows the loop product `P_n` commutes with the full matrix algebra spanned
by `B`, hence is a scalar `λ ≠ 0`.  An `n`-th root `c^n = λ⁻¹`, available because
`ℂ` is algebraically closed, absorbs the residual scalar into the repeated
tensor `B' = c · B`, which is still injective and generates the same closed
state.

**Scope restriction (uniform bond dimension):** the source corollary also
concludes that all per-bond dimensions of the original site-dependent
representation are equal; in the uniform `MPSChainTensor d D n` setting that
clause is built into the type and carries no content.  The per-edge
bond-dimension form, which makes the equal-dimension conclusion non-vacuous,
remains the follow-up recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Applications
  section, the corollary at line 1804, proof lines 1807--1890 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped Matrix
open scoped Fin.NatCast

namespace TNLean
namespace PEPS

open MPSChainTensor

/-- The running product `Z_{m-1} ⋯ Z_0` of the first `m` cyclic-shift gauges.
This is the uniform-bond-dimension form of the products denoted `L_i`, `R_i` in
arXiv:1804.04964, eq:translation A_i (line 1844). -/
private def gaugePartial {n D : ℕ} [NeZero n] (Z : Fin n → GL (Fin D) ℂ) :
    ℕ → GL (Fin D) ℂ
  | 0 => 1
  | (m + 1) => Z (m : Fin n) * gaugePartial Z m

/-- **Translation-invariant description of an injective closed MPS chain**
(arXiv:1804.04964, Applications section, the corollary at line 1804, proof lines
1807--1890), in the uniform physical- and bond-dimension setting.

An injective site-dependent closed chain on `n ≥ 3` sites whose closed-chain
state is invariant under the cyclic shift `A_v ↦ A_{v+1}` has a
translation-invariant description: there is one repeated injective tensor `B` of
the same bond dimension `D` whose constant chain generates the same closed
state.

The cyclic-shift comparison
(`fundamentalTheorem_injectiveMPSChain_cyclicShift`) supplies the per-bond
gauges; telescoping them into the running products `gaugePartial` expresses
every tensor through the first; the seam relation `A_{n+1} ≡ A_0` pins the loop
product to a scalar; and an `n`-th root absorbs that scalar into the repeated
tensor. -/
theorem exists_constant_injectiveMPS_of_cyclicShiftInvariantState
    {n d D : ℕ} [NeZero n] (hn : 3 ≤ n) (A : MPSChainTensor d D n)
    (hA : IsInjective A) (hTI : IsCyclicShiftInvariantState A) :
    ∃ B : MPSTensor d D, MPSTensor.IsInjective B ∧ SameState A (fun _ : Fin n => B) := by
  have hn0 : 0 < n := by omega
  -- A vanishing bond dimension makes every matrix the unique `0 × 0` matrix.
  rcases Nat.eq_zero_or_pos D with hD0 | hD
  · subst hD0
    refine ⟨fun _ => 0, ?_, ?_⟩
    · refine eq_top_iff.mpr fun x _ => ?_
      rw [Subsingleton.elim x 0]
      exact Submodule.zero_mem _
    · intro σ
      simp only [MPSChainTensor.coeff_eq, Matrix.trace, Matrix.diag,
        Finset.univ_eq_empty, Finset.sum_empty]
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  -- The cyclic-shift comparison: one invertible gauge per bond.
  obtain ⟨Z, hZ0⟩ := fundamentalTheorem_injectiveMPSChain_cyclicShift hn A hA hTI
  have hZ : ∀ (k : Fin n) (i : Fin d), A (cyclicSucc k) i =
      (Z k : Matrix (Fin D) (Fin D) ℂ) * A k i *
        (((Z (cyclicSucc k))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
    fun k i => hZ0 k i
  -- The running products of the gauges and the tentative repeated tensor.
  set P : ℕ → GL (Fin D) ℂ := gaugePartial Z with hPdef
  have hP0 : P 0 = 1 := rfl
  have hPsucc : ∀ m : ℕ, P (m + 1) = Z (m : Fin n) * P m := fun _ => rfl
  set B : MPSTensor d D := fun i => A 0 i * (Z 0 : Matrix (Fin D) (Fin D) ℂ) with hBdef
  -- For `m < n` the cast `(m : Fin n)` is the literal index `⟨m, _⟩`.
  have hcast : ∀ (m : ℕ) (hm : m < n), (m : Fin n) = ⟨m, hm⟩ := by
    intro m hm
    apply Fin.ext
    rw [Fin.val_natCast, Nat.mod_eq_of_lt hm]
  -- Each tensor expressed through the first via the running products.
  have hmain : ∀ m : ℕ, ∀ (hm : m < n) (i : Fin d),
      A ⟨m, hm⟩ i = (P m : Matrix (Fin D) (Fin D) ℂ) * B i *
        (((P (m + 1))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    intro m
    induction m with
    | zero =>
        intro hm i
        have hidx : (⟨0, hm⟩ : Fin n) = 0 := Fin.ext (by simp)
        have h0 : ((0 : ℕ) : Fin n) = (0 : Fin n) := Fin.ext (by simp)
        rw [hidx, hP0, hPsucc 0, hP0, h0, mul_one, hBdef]
        simp only [Units.val_one, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    | succ k IH =>
        intro hm i
        have hk : k < n := by omega
        have hjcast : (k : Fin n) = (⟨k, hk⟩ : Fin n) := hcast k hk
        have hsucc : cyclicSucc (⟨k, hk⟩ : Fin n) = (⟨k + 1, hm⟩ : Fin n) := by
          rw [cyclicSucc_eq_add_one]
          apply Fin.ext
          have hone : ((1 : Fin n).val) = 1 := by
            rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
          rw [Fin.val_add_eq_ite, hone]
          change (if n ≤ k + 1 then k + 1 - n else k + 1) = k + 1
          split_ifs <;> omega
        have hZk := hZ (⟨k, hk⟩ : Fin n) i
        rw [hsucc] at hZk
        rw [hZk, IH hk i]
        have hZkc : Z (⟨k, hk⟩ : Fin n) = Z (k : Fin n) := by rw [hjcast]
        have hZk1c : Z (⟨k + 1, hm⟩ : Fin n) = Z ((k + 1 : ℕ) : Fin n) := by
          rw [hcast (k + 1) hm]
        rw [hZkc, hZk1c]
        have hPk1 : (P (k + 1) : Matrix (Fin D) (Fin D) ℂ) =
            (Z (k : Fin n) : Matrix (Fin D) (Fin D) ℂ) *
              (P k : Matrix (Fin D) (Fin D) ℂ) := by
          rw [hPsucc k, Units.val_mul]
        have hPk2 : (((P (k + 1 + 1))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
            (((P (k + 1))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
              (((Z ((k + 1 : ℕ) : Fin n))⁻¹ : GL (Fin D) ℂ) :
                Matrix (Fin D) (Fin D) ℂ) := by
          rw [hPsucc (k + 1), mul_inv_rev, Units.val_mul]
        rw [hPk1, hPk2]
        simp only [Matrix.mul_assoc]
  -- The arc product telescopes: the running products survive only at the ends.
  have htel : ∀ (w : List (Fin d)) (s : ℕ), s + w.length ≤ n →
      arcEval A s w = (P s : Matrix (Fin D) (Fin D) ℂ) * MPSTensor.evalWord B w *
        (((P (s + w.length))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    intro w
    induction w with
    | nil =>
        intro s _
        simp only [arcEval_nil, List.length_nil, Nat.add_zero, MPSTensor.evalWord_nil,
          Matrix.mul_one, Units.mul_inv]
    | cons i w ih =>
        intro s hs
        have hsn : s < n := by simp only [List.length_cons] at hs; omega
        have hsle : s + 1 + w.length ≤ n := by simp only [List.length_cons] at hs; omega
        rw [arcEval_cons, MPSTensor.evalWord_cons, ih (s + 1) hsle, hcast s hsn, hmain s hsn i]
        have hlen : s + (i :: w).length = s + 1 + w.length := by
          rw [List.length_cons]; omega
        rw [hlen]
        simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]
  -- The repeated tensor spans the full matrix algebra.
  have hspanB : Submodule.span ℂ (Set.range B) = ⊤ := by
    have hsurj : Function.Surjective
        ⇑(LinearMap.mulRight ℂ (Z 0 : Matrix (Fin D) (Fin D) ℂ)) := by
      intro y
      refine ⟨y * (((Z 0)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ), ?_⟩
      simp only [LinearMap.mulRight_apply, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    have hrange : Set.range B =
        ⇑(LinearMap.mulRight ℂ (Z 0 : Matrix (Fin D) (Fin D) ℂ)) '' Set.range (A 0) := by
      ext x
      simp only [Set.mem_range, Set.mem_image, LinearMap.mulRight_apply, hBdef]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨A 0 i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    rw [hrange, ← Submodule.map_span, (hA 0).span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.mpr hsurj]
  -- The loop product commutes with the spanning tensor, hence is a scalar.
  have hn1 : n - 1 < n := by omega
  have hseamSucc : cyclicSucc (⟨n - 1, hn1⟩ : Fin n) = (0 : Fin n) := by
    rw [cyclicSucc_eq_add_one]
    apply Fin.ext
    have hone : ((1 : Fin n).val) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add_eq_ite, hone, Fin.val_zero]
    change (if n ≤ n - 1 + 1 then n - 1 + 1 - n else n - 1 + 1) = 0
    split_ifs <;> omega
  have hnsub : n - 1 + 1 = n := by omega
  have hcomm : ∀ M ∈ Set.range B,
      (P n : Matrix (Fin D) (Fin D) ℂ) * M = M * (P n : Matrix (Fin D) (Fin D) ℂ) := by
    rintro M ⟨i, rfl⟩
    -- The seam relation written through the running products.
    have hZseam := hZ (⟨n - 1, hn1⟩ : Fin n) i
    rw [hseamSucc] at hZseam
    have hAnm1 := hmain (n - 1) hn1 i
    rw [hnsub] at hAnm1
    have hZc : Z (⟨n - 1, hn1⟩ : Fin n) = Z ((n - 1 : ℕ) : Fin n) := by
      rw [hcast (n - 1) hn1]
    have hPn : (P n : Matrix (Fin D) (Fin D) ℂ) =
        (Z ((n - 1 : ℕ) : Fin n) : Matrix (Fin D) (Fin D) ℂ) *
          (P (n - 1) : Matrix (Fin D) (Fin D) ℂ) := by
      conv_lhs => rw [← hnsub]
      rw [hPsucc (n - 1), Units.val_mul]
    -- `A 0 i` read two ways: directly, and across the seam.
    have hA0 : A 0 i = B i * (((Z 0)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
      rw [hBdef]; simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    have hseam : B i * (((Z 0)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
        ((P n : Matrix (Fin D) (Fin D) ℂ) * B i *
            (((P n)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) *
          (((Z 0)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
      rw [← hA0, hZseam, hAnm1, hZc, hPn]
      simp only [Matrix.mul_assoc]
    -- Cancel the trailing `Z₀⁻¹`, then conjugate back.
    have hfix : B i =
        (P n : Matrix (Fin D) (Fin D) ℂ) * B i *
          (((P n)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
      have h := congrArg (· * (Z 0 : Matrix (Fin D) (Fin D) ℂ)) hseam
      simpa only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] using h
    have h := congrArg (fun X => X * (P n : Matrix (Fin D) (Fin D) ℂ)) hfix
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] at h
    exact h.symm
  obtain ⟨lam, hlam⟩ :=
    Matrix.isScalar_of_commute_span_eq_top (P n : Matrix (Fin D) (Fin D) ℂ) hspanB hcomm
  have hscal1 : (P n : Matrix (Fin D) (Fin D) ℂ) = lam • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [hlam]; ext a b
    by_cases hab : a = b <;>
      simp [Matrix.scalar_apply, Matrix.smul_apply, hab]
  have hlam0 : lam ≠ 0 := by
    intro h
    have hunit : (P n : Matrix (Fin D) (Fin D) ℂ) *
        (((P n)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = 1 := Units.mul_inv _
    rw [hscal1, h, zero_smul, Matrix.zero_mul] at hunit
    exact one_ne_zero hunit.symm
  have hPinv : (((P n)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
      lam⁻¹ • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    have hmul : (P n : Matrix (Fin D) (Fin D) ℂ) *
        (((P n)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = 1 := Units.mul_inv _
    rw [hscal1, Matrix.smul_mul, Matrix.one_mul] at hmul
    have h := congrArg (fun M => lam⁻¹ • M) hmul
    simpa only [smul_smul, inv_mul_cancel₀ hlam0, one_smul] using h
  -- The closed coefficient up to the residual scalar.
  have hcoeffA : ∀ σ : Fin n → Fin d, coeff A σ =
      lam⁻¹ * Matrix.trace (MPSTensor.evalWord B (List.ofFn σ)) := by
    intro σ
    have hlenσ : (List.ofFn σ).length = n := List.length_ofFn
    have h0n : 0 + (List.ofFn σ).length = n := by rw [Nat.zero_add, hlenσ]
    rw [coeff_eq_trace_arcEval A σ, htel (List.ofFn σ) 0 (by rw [hlenσ]; omega), h0n, hP0]
    simp only [Units.val_one, Matrix.one_mul]
    rw [hPinv, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  -- Absorb the residual scalar into the repeated tensor via an `n`-th root.
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) lam⁻¹ hn0
  have hc0 : c ≠ 0 := by
    intro h
    apply hlam0
    have hz : (0 : ℂ) = lam⁻¹ := by rw [← hc, h, zero_pow (by omega : n ≠ 0)]
    exact inv_eq_zero.mp hz.symm
  refine ⟨fun i => c • B i, ?_, ?_⟩
  · -- Injectivity is preserved by the nonzero scaling.
    change Submodule.span ℂ (Set.range (fun i => c • B i)) =
      (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ))
    have hsurj : Function.Surjective
        ⇑(LinearMap.lsmul ℂ (Matrix (Fin D) (Fin D) ℂ) c) := by
      intro y
      refine ⟨c⁻¹ • y, ?_⟩
      simp only [LinearMap.lsmul_apply, smul_smul, mul_inv_cancel₀ hc0, one_smul]
    have hrange : Set.range (fun i => c • B i) =
        ⇑(LinearMap.lsmul ℂ (Matrix (Fin D) (Fin D) ℂ) c) '' Set.range B := by
      ext x
      simp only [Set.mem_range, Set.mem_image, LinearMap.lsmul_apply]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨B i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    rw [hrange, ← Submodule.map_span, hspanB, Submodule.map_top,
      LinearMap.range_eq_top.mpr hsurj]
  · -- The constant chain generates the same closed state.
    intro σ
    rw [hcoeffA σ, coeff_eq_trace_arcEval (fun _ : Fin n => fun i => c • B i) σ,
      arcEval_const, MPSTensor.evalWord_smul, List.length_ofFn, Matrix.trace_smul,
      smul_eq_mul, hc]

end PEPS
end TNLean
