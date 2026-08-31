/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.VaryingBondOBC
import TNLean.PEPS.CycleMPSChainOverlapCapstone
import TNLean.PEPS.CycleShiftBondUniformity

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Translation-invariant description of an injective closed MPS chain

This file delivers the positive-bond, at-least-three-site form of the
Applications-section corollary of arXiv:1804.04964
(`Papers/1804.04964/paper_normal.tex`, the corollary at line 1804, proof lines
1807--1890).  For a cycle-graph tensor with one virtual dimension per bond,
cyclic-shift invariance first makes all bond dimensions equal.  The dependent
spaces `Fin (D_e)` are then reindexed to one common `Fin D`, producing the
uniform closed chain to which the already proved `L_i,R_i` telescoping and seam
closure apply.  The result is a single repeated injective tensor `B` of the
same bond dimension
(`exists_constant_injectiveMPS_of_cyclicShiftInvariantState_per_bond`).

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

**Local fix (cyclic seam scalar):** At source line 1876, the paper sets the
closing products `R_{n+1}` and `L_{n+1}` equal to the identity.  The
closed-chain argument only forces the closing loop product to be a nonzero
scalar.  The proof below absorbs an inverse `n`-th root of that scalar into
the repeated tensor.  This correction is documented in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

**Scope restriction (positive bonds and at least three sites):** The final
theorem below assumes positive virtual dimensions and `3 ≤ n`.  Positivity is
not intrinsic to the current `Tensor` type, and the source corollary at line
1804 does not state either hypothesis.  However, the source section explicitly
works with at least three sites at line 145, and the corollary's proof invokes
the corresponding Fundamental Theorem at lines 688--725.  Thus `3 ≤ n` records
the intended source context rather than a missing short-chain extension.  The
literal two-site statement is false for nondegenerate rectangular bond data,
so omission of this qualifier from the printed corollary is a source-scope
defect.  The remaining source-facing gap is recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

The uniform-chain theorem
`exists_constant_injectiveMPS_of_cyclicShiftInvariantState` remains the
source's telescoping calculation.  The graph-to-chain bridge below only makes
the source's implicit identification of the now-equal virtual spaces explicit;
it does not introduce a second varying-bond chain model.

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

/-! ### Reindexing equal cycle bonds to one matrix chain -/

/-- Reindex a cycle-graph tensor whose bond dimensions are all equal to `D`
as a site-dependent chain of `D × D` matrices.  The row index is read from
the bond entering the site and the column index from the bond leaving it.

This is the explicit dependent-index identification used after the
equal-bond-dimension step in arXiv:1804.04964, Applications section, proof
lines 1843--1890 of `Papers/1804.04964/paper_normal.tex`. -/
noncomputable def Tensor.reindexMPSChain
    {n d D : ℕ} [NeZero n] (hn : 3 ≤ n)
    (A : Tensor (SimpleGraph.cycleGraph n) d)
    (hDim : (fun _ : Edge (SimpleGraph.cycleGraph n) => D) = A.bondDim) :
    MPSChainTensor d D n :=
  let A' := reindexTensor A hDim
  fun v i a b =>
    A'.component v ((cycleIncidentPairEquiv (D := D) hn v).symm (a, b)) i

/-- Reindexing all cycle bonds to one common `Fin D` preserves every
closed-chain coefficient.

Source: arXiv:1804.04964, Applications section, lines 1843--1889 of
`Papers/1804.04964/paper_normal.tex`, where the equal virtual spaces are read
as square matrices before the `L_i,R_i` telescoping. -/
theorem Tensor.stateCoeff_reindexMPSChain
    {n d D : ℕ} [NeZero n] (hn : 3 ≤ n)
    (A : Tensor (SimpleGraph.cycleGraph n) d)
    (hDim : (fun _ : Edge (SimpleGraph.cycleGraph n) => D) = A.bondDim)
    (sigma : Fin n → Fin d) :
    stateCoeff A sigma = MPSChainTensor.coeff (A.reindexMPSChain hn hDim) sigma := by
  rw [← stateCoeff_reindexTensor A hDim sigma,
    MPSChainTensor.coeff_eq_sum_cyclic]
  unfold stateCoeff
  refine (Fintype.sum_equiv
    (Equiv.arrowCongr (cycleEdgeEquiv hn).symm (Equiv.refl (Fin D)))
    (fun eta : VirtualConfig (reindexTensor A hDim) =>
      ∏ v : Fin n, (reindexTensor A hDim).component v (fun ie => eta ie.1) (sigma v))
    (fun g : Fin n → Fin D =>
      ∏ v : Fin n, (A.reindexMPSChain hn hDim) v (sigma v) (g (v - 1)) (g v))
    (fun eta => Finset.prod_congr rfl fun v _ => by
      have hedge (w : Fin n) :
          ((Equiv.arrowCongr (cycleEdgeEquiv hn).symm (Equiv.refl (Fin D))) eta) w =
            eta (cycleSuccEdge hn w) := rfl
      rw [hedge (v - 1), hedge v]
      change (reindexTensor A hDim).component v (fun ie => eta ie.1) (sigma v) =
        (reindexTensor A hDim).component v
          ((cycleIncidentPairEquiv (D := D) hn v).symm
            (eta (cycleSuccEdge hn (v - 1)), eta (cycleSuccEdge hn v))) (sigma v)
      congr 1
      exact ((cycleIncidentPairEquiv (D := D) hn v).symm_apply_apply
        (fun ie => eta ie.1)).symm)).trans
    (Fintype.sum_equiv
      (Equiv.arrowCongr (Equiv.subRight (1 : Fin n)).symm (Equiv.refl (Fin D)))
      (fun g : Fin n → Fin D =>
        ∏ v : Fin n, (A.reindexMPSChain hn hDim) v (sigma v) (g (v - 1)) (g v))
      (fun g : Fin n → Fin D =>
        ∏ v : Fin n, (A.reindexMPSChain hn hDim) v (sigma v) (g v) (g (v + 1)))
      (fun g => Finset.prod_congr rfl fun v _ => by
        simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl,
          Function.comp_apply, Equiv.subRight_apply, id_eq]
        rw [add_sub_cancel_right]))

/-- Reindexing all cycle bonds to one common `Fin D` carries vertex
injectivity to sitewise matrix injectivity.

Source: arXiv:1804.04964, Applications section, lines 1843--1890 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem Tensor.isInjective_reindexMPSChain
    {n d D : ℕ} [NeZero n] (hn : 3 ≤ n)
    (A : Tensor (SimpleGraph.cycleGraph n) d)
    (hDim : (fun _ : Edge (SimpleGraph.cycleGraph n) => D) = A.bondDim)
    (hA : IsVertexInjective A) :
    MPSChainTensor.IsInjective (A.reindexMPSChain hn hDim) := by
  let A' := reindexTensor A hDim
  have hA' : IsVertexInjective A' := isVertexInjective_reindexTensor A hDim hA
  intro v
  let q := cycleIncidentPairEquiv (D := D) hn v
  let f : Fin D × Fin D → Fin d → ℂ :=
    A'.component v ∘ q.symm
  have hLI : LinearIndependent ℂ f := (hA' v).comp q.symm q.symm.injective
  let e : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] ((Fin D × Fin D) → ℂ) :=
    (LinearEquiv.curry ℂ ℂ (Fin D) (Fin D)).symm
  have hcomp :
      (⇑(e : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ((Fin D × Fin D) → ℂ))) ∘
        (A.reindexMPSChain hn hDim v) = flip f := by
    funext i p
    rfl
  rw [Kraus.IsInjective, ← Submodule.map_eq_top_iff (e := e),
    Submodule.map_span, ← Set.range_comp, hcomp]
  exact span_flip_eq_top_iff_linearIndependent.mpr hLI

/-- The common-bond reindexing preserves cyclic-shift invariance of the
closed-chain state.

Source: arXiv:1804.04964, Applications section, lines 1807--1890 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem Tensor.isCyclicShiftInvariantState_reindexMPSChain
    {n d D : ℕ} [NeZero n] (hn : 3 ≤ n)
    (A : Tensor (SimpleGraph.cycleGraph n) d)
    (hDim : (fun _ : Edge (SimpleGraph.cycleGraph n) => D) = A.bondDim)
    (hTI : IsCycleShiftInvariantState A hn) :
    MPSChainTensor.IsCyclicShiftInvariantState (A.reindexMPSChain hn hDim) := by
  intro sigma
  rw [MPSChainTensor.coeff_cyclicShift,
    ← A.stateCoeff_reindexMPSChain hn hDim sigma,
    ← A.stateCoeff_reindexMPSChain hn hDim (fun v => sigma ((finRotate n).symm v))]
  have h := hTI sigma
  rw [Tensor.cycleShift, stateCoeff_transport] at h
  have hrotate (v : Fin n) :
      (cycleRotate hn).symm v = (finRotate n).symm v := rfl
  simpa only [hrotate] using h

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
    {n d D : ℕ} [NeZero n] (hn : 3 ≤ n) (hD : 0 < D)
    (A : MPSChainTensor d D n)
    (hA : IsInjective A) (hTI : IsCyclicShiftInvariantState A) :
    ∃ B : MPSTensor d D, Kraus.IsInjective B ∧
      MPSChainTensor.SameState A (fun _ : Fin n => B) := by
  have hn0 : 0 < n := by omega
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  -- The cyclic-shift comparison: one invertible gauge per bond.
  obtain ⟨Z, hZ0⟩ := fundamentalTheorem_injectiveMPSChain_cyclicShift hn hD A hA hTI
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
      arcEval A s w = (P s : Matrix (Fin D) (Fin D) ℂ) * Kraus.evalWord B w *
        (((P (s + w.length))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    intro w
    induction w with
    | nil =>
        intro s _
        simp only [arcEval_nil, List.length_nil, Nat.add_zero, Kraus.evalWord_nil,
          Matrix.mul_one, Units.mul_inv]
    | cons i w ih =>
        intro s hs
        have hsn : s < n := by simp only [List.length_cons] at hs; omega
        have hsle : s + 1 + w.length ≤ n := by simp only [List.length_cons] at hs; omega
        rw [arcEval_cons, Kraus.evalWord_cons, ih (s + 1) hsle, hcast s hsn, hmain s hsn i]
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
      lam⁻¹ * Matrix.trace (Kraus.evalWord B (List.ofFn σ)) := by
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
      arcEval_const, Kraus.evalWord_smul, List.length_ofFn, Matrix.trace_smul,
      smul_eq_mul, hc]

/-- **Positive-bond, at-least-three-site translation-invariant description of
an injective closed MPS chain with one dimension per bond**
(arXiv:1804.04964, Applications section, corollary line 1804 and proof lines
1807--1890).

Let a site-dependent injective MPS on the cycle graph have positive virtual
dimension on every bond, and suppose that its closed-chain state is invariant
under the cyclic shift `Aᵥ ↦ Aᵥ₊₁`.  Then all bond dimensions equal one
positive integer `D`, and the state is generated by one repeated injective
`D × D` matrix tensor `B`.

The first step is `bondDim_eq_of_isCycleShiftInvariantState`, corresponding to
source lines 1807--1842.  The tensor is then explicitly reindexed to the
uniform chain `Tensor.reindexMPSChain`.  The existing uniform theorem above
supplies the source's `L_i,R_i` telescoping, seam closure, and repeated tensor
from lines 1843--1889.  The explicit positive-bond and `3 ≤ n` hypotheses are
the scope restriction documented in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`. -/
theorem exists_constant_injectiveMPS_of_cyclicShiftInvariantState_per_bond
    {n d : ℕ} [NeZero n] (hn : 3 ≤ n)
    (A : Tensor (SimpleGraph.cycleGraph n) d)
    (hA : IsVertexInjective A) (hTI : IsCycleShiftInvariantState A hn)
    (hpos : ∀ e : Edge (SimpleGraph.cycleGraph n), 0 < A.bondDim e) :
    ∃ D : ℕ, 0 < D ∧ (∀ e, A.bondDim e = D) ∧
      ∃ B : MPSTensor d D, Kraus.IsInjective B ∧
        ∀ sigma : Fin n → Fin d, stateCoeff A sigma = MPSTensor.mpv B sigma := by
  let e₀ := cycleSuccEdge hn (0 : Fin n)
  let D := A.bondDim e₀
  have hD : 0 < D := hpos e₀
  have hDim : ∀ e : Edge (SimpleGraph.cycleGraph n), A.bondDim e = D := fun e =>
    bondDim_eq_of_isCycleShiftInvariantState hn A hA hTI hpos e e₀
  have hDim' : (fun _ : Edge (SimpleGraph.cycleGraph n) => D) = A.bondDim := by
    funext e
    exact (hDim e).symm
  let C := A.reindexMPSChain hn hDim'
  have hCInjective : MPSChainTensor.IsInjective C :=
    A.isInjective_reindexMPSChain hn hDim' hA
  have hCShift : MPSChainTensor.IsCyclicShiftInvariantState C :=
    A.isCyclicShiftInvariantState_reindexMPSChain hn hDim' hTI
  obtain ⟨B, hBInjective, hBC⟩ :=
    exists_constant_injectiveMPS_of_cyclicShiftInvariantState hn hD C hCInjective hCShift
  refine ⟨D, hD, hDim, B, hBInjective, ?_⟩
  intro sigma
  calc
    stateCoeff A sigma = MPSChainTensor.coeff C sigma :=
      A.stateCoeff_reindexMPSChain hn hDim' sigma
    _ = MPSChainTensor.coeff (fun _ : Fin n => B) sigma := hBC sigma
    _ = MPSTensor.mpv B sigma := by
      rw [MPSChainTensor.coeff_eq_trace_arcEval, MPSChainTensor.arcEval_const,
        MPSTensor.mpv_eq, MPSTensor.coeff_eq]

end PEPS
end TNLean
