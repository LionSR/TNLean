/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Core.ReductionResidual

/-!
# Boundary-dressed uniqueness of rectangular reductions

This file proves that two reductions from the same tensor to the same normal
target agree up to a nonzero scalar after sufficiently long words.  The
conclusion remains boundary-dressed: it does not cancel the source words to
assert equalities between the rectangular boundary matrices themselves.

Source: Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2, Theorem 22,
`cornerproblem.tex` lines 3156--3162 and proof at lines 4007--4035.
-/

open scoped Matrix

namespace MPSTensor

variable {d D_A D_B : ℕ}

private theorem mul_single_mul_apply {D : ℕ}
    (P Q : Matrix (Fin D) (Fin D) ℂ) (i j a b : Fin D) :
    (P * Matrix.single j a (1 : ℂ) * Q) i b = P i j * Q a b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [Matrix.mul_single_apply_same]
    simp
  · intro k _ hka
    rw [Matrix.mul_single_apply_of_ne (c := (1 : ℂ)) (i := j) (j := a)
      (a := i) (b := k) hka]
    simp
  · simp

private theorem exists_evalWord_ne_zero_of_isNBlkInjective
    {A : MPSTensor d D_A} {L : ℕ} (hD : D_A ≠ 0)
    (hA : Kraus.IsNBlkInjective A L) :
    ∃ σ : Fin L → Fin d, Kraus.evalWord A (List.ofFn σ) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hbot : Kraus.wordSpan A L = ⊥ := by
    rw [Kraus.wordSpan]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro X ⟨σ, rfl⟩
      change Kraus.evalWord A (List.ofFn σ) ∈ (⊥ : Submodule ℂ _)
      simp [h σ]
    · exact bot_le
  unfold Kraus.IsNBlkInjective at hA
  rw [hbot] at hA
  let a : Fin D_A := ⟨0, Nat.pos_of_ne_zero hD⟩
  have hone : (1 : Matrix (Fin D_A) (Fin D_A) ℂ) ∈
      (⊥ : Submodule ℂ (Matrix (Fin D_A) (Fin D_A) ℂ)) := by
    rw [hA]
    exact Submodule.mem_top
  have honeZero : (1 : Matrix (Fin D_A) (Fin D_A) ℂ) = 0 := hone
  have := congrFun (congrFun honeZero a) a
  simp at this

private theorem cross_mul_evalWord_mul_cross
    {B : MPSTensor d D_B} {A : MPSTensor d D_A}
    {V : Matrix (Fin D_A) (Fin D_B) ℂ} {W : Matrix (Fin D_B) (Fin D_A) ℂ}
    {V' : Matrix (Fin D_A) (Fin D_B) ℂ} {W' : Matrix (Fin D_B) (Fin D_A) ℂ}
    (h : IsReduction B A V W) (h' : IsReduction B A V' W') {N : ℕ}
    (hBound : IsReductionResidualNilpotencyBound B A V W N)
    (hBound' : IsReductionResidualNilpotencyBound B A V' W' N)
    (p c q : List (Fin d)) (hc : c ≠ [])
    (hp : N ≤ p.length + 1) (hq : N ≤ q.length + 1) :
    (V * Kraus.evalWord B p * W') * Kraus.evalWord A c * Kraus.evalWord A q =
      Kraus.evalWord A p * Kraus.evalWord A c *
        (V * Kraus.evalWord B q * W') := by
  have hext' :=
    h'.evalWord_mul_reduced_exterior_eq_evalWord_append hBound' p c q hc hp hq
  have hext := h.evalWord_mul_reduced_exterior_eq_evalWord_append hBound p c q hc hp hq
  have hleft :
      (V * Kraus.evalWord B p * W') * Kraus.evalWord A c * Kraus.evalWord A q =
        V * Kraus.evalWord B (p ++ c ++ q) * W' := by
    calc
      _ = V * (Kraus.evalWord B p * W' * Kraus.evalWord A c * V' *
          Kraus.evalWord B q) * W' := by
        rw [← h'.evalWord q]
        simp only [Matrix.mul_assoc]
      _ = _ := congrArg (fun X ↦ V * X * W') hext'
  have hright :
      Kraus.evalWord A p * Kraus.evalWord A c *
          (V * Kraus.evalWord B q * W') =
        V * Kraus.evalWord B (p ++ c ++ q) * W' := by
    calc
      _ = V * (Kraus.evalWord B p * W * Kraus.evalWord A c * V *
          Kraus.evalWord B q) * W' := by
        rw [← h.evalWord p]
        simp only [Matrix.mul_assoc]
      _ = _ := congrArg (fun X ↦ V * X * W') hext
  exact hleft.trans hright.symm

private theorem cross_mul_matrix_mul_cross
    {B : MPSTensor d D_B} {A : MPSTensor d D_A}
    {V : Matrix (Fin D_A) (Fin D_B) ℂ} {W : Matrix (Fin D_B) (Fin D_A) ℂ}
    {V' : Matrix (Fin D_A) (Fin D_B) ℂ} {W' : Matrix (Fin D_B) (Fin D_A) ℂ}
    (h : IsReduction B A V W) (h' : IsReduction B A V' W') {N L : ℕ}
    (hBound : IsReductionResidualNilpotencyBound B A V W N)
    (hBound' : IsReductionResidualNilpotencyBound B A V' W' N)
    (hLpos : 0 < L) (hA : Kraus.IsNBlkInjective A L)
    (p q : List (Fin d)) (hp : N ≤ p.length + 1) (hq : N ≤ q.length + 1)
    (M : Matrix (Fin D_A) (Fin D_A) ℂ) :
    (V * Kraus.evalWord B p * W') * M * Kraus.evalWord A q =
      Kraus.evalWord A p * M * (V * Kraus.evalWord B q * W') := by
  have hmem : M ∈ Kraus.wordSpan A L := by rw [hA]; exact Submodule.mem_top
  rw [Kraus.wordSpan] at hmem
  induction hmem using Submodule.span_induction with
  | mem M hM =>
      obtain ⟨σ, rfl⟩ := hM
      exact cross_mul_evalWord_mul_cross h h' hBound hBound' p (List.ofFn σ) q
        (by simpa using hLpos.ne') hp hq
  | zero => simp
  | add X Y _ _ hX hY => simp only [Matrix.mul_add, Matrix.add_mul, hX, hY]
  | smul c X _ hX =>
      simp only [Matrix.mul_smul, Matrix.smul_mul, hX]

private theorem exists_cross_scalar
    {B : MPSTensor d D_B} {A : MPSTensor d D_A}
    {V : Matrix (Fin D_A) (Fin D_B) ℂ} {W : Matrix (Fin D_B) (Fin D_A) ℂ}
    {V' : Matrix (Fin D_A) (Fin D_B) ℂ} {W' : Matrix (Fin D_B) (Fin D_A) ℂ}
    (hD : D_A ≠ 0) (hNormal : Kraus.IsNormal A)
    (h : IsReduction B A V W) (h' : IsReduction B A V' W') {N : ℕ}
    (hBound : IsReductionResidualNilpotencyBound B A V W N)
    (hBound' : IsReductionResidualNilpotencyBound B A V' W' N) :
    ∃ z : ℂ, ∀ u : List (Fin d), N ≤ u.length + 1 →
      V * Kraus.evalWord B u * W' = z • Kraus.evalWord A u := by
  classical
  obtain ⟨L, hLpos, hL⟩ := hNormal
  let m := N + 1
  have hm : 0 < m := by simp [m]
  have hK := isNBlkInjective_mul_of_isNBlkInjective A hm hL
  obtain ⟨σ, hσ⟩ := exists_evalWord_ne_zero_of_isNBlkInjective hD hK
  have hab : ∃ a b, Kraus.evalWord A (List.ofFn σ) a b ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hσ
    ext a b
    exact hall a b
  obtain ⟨a, b, hab⟩ := hab
  let q := List.ofFn σ
  have hq : N ≤ q.length + 1 := by
    simp only [q, List.length_ofFn]
    dsimp [m]
    nlinarith
  let z := (V * Kraus.evalWord B q * W') a b / Kraus.evalWord A q a b
  refine ⟨z, fun u hu ↦ ?_⟩
  ext i j
  have hsingle := congrFun (congrFun
    (cross_mul_matrix_mul_cross h h' hBound hBound' hLpos hL u q hu hq
      (Matrix.single j a (1 : ℂ))) i) b
  let X := V * Kraus.evalWord B u * W'
  let Y := V * Kraus.evalWord B q * W'
  change (X * Matrix.single j a (1 : ℂ) * Kraus.evalWord A q) i b =
    (Kraus.evalWord A u * Matrix.single j a (1 : ℂ) * Y) i b at hsingle
  simp only [mul_single_mul_apply] at hsingle
  change X i j = z * Kraus.evalWord A u i j
  have hden : Kraus.evalWord A q a b ≠ 0 := by simpa [q] using hab
  dsimp [z]
  change X i j = (Y a b / Kraus.evalWord A q a b) * Kraus.evalWord A u i j
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hden).2
  simpa only [mul_comm] using hsingle

namespace IsReduction

variable {B : MPSTensor d D_B} {A : MPSTensor d D_A}
  {V : Matrix (Fin D_A) (Fin D_B) ℂ} {W : Matrix (Fin D_B) (Fin D_A) ℂ}
  {V' : Matrix (Fin D_A) (Fin D_B) ℂ} {W' : Matrix (Fin D_B) (Fin D_A) ℂ}

/-- Two reductions to the same normal tensor are uniquely proportional after
words longer than twice a common residual nilpotency bound.  Both conclusions
retain the source word next to the rectangular boundary, as in MGSC18
Theorem 22; no bare equality between boundary matrices is asserted.

Source: Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2, Theorem 22,
`cornerproblem.tex` lines 3156--3162 and 4007--4035. -/
theorem exists_boundary_dressed_proportional
    (h : IsReduction B A V W) (h' : IsReduction B A V' W')
    (hNormal : Kraus.IsNormal A) {N₀ : ℕ}
    (hBound : IsReductionResidualNilpotencyBound B A V W N₀)
    (hBound' : IsReductionResidualNilpotencyBound B A V' W' N₀) :
    ∃ z : ℂ, z ≠ 0 ∧ ∀ w : List (Fin d), 2 * N₀ < w.length →
      V * Kraus.evalWord B w = z • (V' * Kraus.evalWord B w) ∧
        Kraus.evalWord B w * W = z⁻¹ • (Kraus.evalWord B w * W') := by
  classical
  by_cases hD : D_A = 0
  · subst D_A
    refine ⟨1, one_ne_zero, fun w _ ↦ ?_⟩
    constructor
    · ext i
      exact Fin.elim0 i
    · ext i j
      exact Fin.elim0 j
  obtain ⟨z, hz⟩ := exists_cross_scalar hD hNormal h h' hBound hBound'
  obtain ⟨μ, hμ⟩ := exists_cross_scalar hD hNormal h' h hBound' hBound
  have hzμ : z * μ = 1 := by
    obtain ⟨L, hLpos, hL⟩ := hNormal
    let m := N₀ + 1
    have hm : 0 < m := by simp [m]
    have htotal := isNBlkInjective_mul_of_isNBlkInjective A
      (show 0 < 2 * m + 1 by omega) hL
    obtain ⟨σ, hσ⟩ := exists_evalWord_ne_zero_of_isNBlkInjective hD htotal
    let word := List.ofFn σ
    let p := word.take (m * L)
    let r := word.drop (m * L)
    let c := r.take L
    let q := r.drop L
    have hsplit : p ++ c ++ q = word := by
      simp only [p, c, q, r, List.take_append_drop, List.append_assoc]
    have htotalLen : (2 * m + 1) * L = m * L + (m + 1) * L := by ring
    have hpLen : p.length = m * L := by
      simp [p, word, List.length_take, htotalLen]
    have hrLen : r.length = (m + 1) * L := by
      simp [r, word, List.length_drop, htotalLen]
    have hcLen : c.length = L := by simp [c, hrLen, hLpos]
    have hqLen : q.length = m * L := by simp [q, hrLen, Nat.add_mul]
    have hp : N₀ ≤ p.length + 1 := by rw [hpLen]; dsimp [m]; nlinarith
    have hq : N₀ ≤ q.length + 1 := by rw [hqLen]; dsimp [m]; nlinarith
    have hc : c ≠ [] := by
      intro hc0
      rw [hc0] at hcLen
      simp at hcLen
      omega
    have hext := h'.evalWord_mul_reduced_exterior_eq_evalWord_append
      hBound' p c q hc hp hq
    have hpCross : V * Kraus.evalWord B p * W' = z • Kraus.evalWord A p := hz p hp
    have hqCross : V' * Kraus.evalWord B q * W = μ • Kraus.evalWord A q := hμ q hq
    have hword : Kraus.evalWord A (p ++ c ++ q) ≠ 0 := by
      simpa [hsplit, word] using hσ
    have hscalar : (z * μ) • Kraus.evalWord A (p ++ c ++ q) =
        Kraus.evalWord A (p ++ c ++ q) := by
      calc
        _ = (z • Kraus.evalWord A p) * Kraus.evalWord A c *
              (μ • Kraus.evalWord A q) := by
            simp only [Kraus.evalWord_append, Matrix.smul_mul, Matrix.mul_smul,
              smul_smul, Matrix.mul_assoc]
            rw [mul_comm μ z]
        _ = (V * Kraus.evalWord B p * W') * Kraus.evalWord A c *
              (V' * Kraus.evalWord B q * W) := by rw [hpCross, hqCross]
        _ = V * (Kraus.evalWord B p * W' * Kraus.evalWord A c * V' *
              Kraus.evalWord B q) * W := by simp only [Matrix.mul_assoc]
        _ = V * Kraus.evalWord B (p ++ c ++ q) * W :=
          congrArg (fun X ↦ V * X * W) hext
        _ = _ := h.evalWord (p ++ c ++ q)
    by_contra hne
    apply hword
    have : (z * μ - 1) • Kraus.evalWord A (p ++ c ++ q) = 0 := by
      rw [sub_smul, one_smul, hscalar, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have hzne : z ≠ 0 := by
    intro hzero
    simp [hzero] at hzμ
  refine ⟨z, hzne, fun w hw ↦ ?_⟩
  let p := w.take N₀
  let r := w.drop N₀
  let c := r.take (r.length - N₀)
  let q := r.drop (r.length - N₀)
  have hpLen : p.length = N₀ := by simp [p, List.length_take]; omega
  have hrLen : r.length = w.length - N₀ := by simp [r, List.length_drop]
  have hcLen : c.length = w.length - 2 * N₀ := by
    simp [c, hrLen, List.length_take]
    omega
  have hqLen : q.length = N₀ := by
    simp [q, hrLen]
    omega
  have hsplit : p ++ c ++ q = w := by
    simp only [p, r, c, q, List.take_append_drop, List.append_assoc]
  have hc : c ≠ [] := by
    intro hc0
    rw [hc0] at hcLen
    simp at hcLen
    omega
  have hp : N₀ ≤ p.length + 1 := by omega
  have hq : N₀ ≤ q.length + 1 := by omega
  have hext := h'.evalWord_mul_reduced_exterior_eq_evalWord_append
    hBound' p c q hc hp hq
  have hext' := h.evalWord_mul_reduced_exterior_eq_evalWord_append
    hBound p c q hc hp hq
  constructor
  · have hpCross : V * Kraus.evalWord B p * W' =
        z • Kraus.evalWord A p := hz p hp
    have hleft : V * Kraus.evalWord B w =
        z • (Kraus.evalWord A p * Kraus.evalWord A c * V' *
          Kraus.evalWord B q) := by
      calc
        _ = V * (Kraus.evalWord B p * W' * Kraus.evalWord A c * V' *
              Kraus.evalWord B q) := by rw [← hsplit, ← hext]
        _ = (V * Kraus.evalWord B p * W') * Kraus.evalWord A c * V' *
              Kraus.evalWord B q := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hpCross]; simp only [Matrix.smul_mul, Matrix.mul_assoc]
    have hright : V' * Kraus.evalWord B w =
        Kraus.evalWord A p * Kraus.evalWord A c * V' * Kraus.evalWord B q := by
      calc
        _ = V' * (Kraus.evalWord B p * W' * Kraus.evalWord A c * V' *
              Kraus.evalWord B q) := by rw [← hsplit, ← hext]
        _ = _ := by
          rw [← h'.evalWord p]
          simp only [Matrix.mul_assoc]
    rw [hleft, hright]
  · have hqCross : V * Kraus.evalWord B q * W' =
        z • Kraus.evalWord A q := hz q hq
    have hforward : Kraus.evalWord B w * W' =
        z • (Kraus.evalWord B w * W) := by
      calc
        _ = (Kraus.evalWord B p * W * Kraus.evalWord A c * V *
              Kraus.evalWord B q) * W' := by rw [← hsplit, ← hext']
        _ = Kraus.evalWord B p * W * Kraus.evalWord A c *
              (V * Kraus.evalWord B q * W') := by simp only [Matrix.mul_assoc]
        _ = z • (Kraus.evalWord B p * W * Kraus.evalWord A c *
              Kraus.evalWord A q) := by rw [hqCross]; simp only [Matrix.mul_smul]
        _ = z • ((Kraus.evalWord B p * W * Kraus.evalWord A c * V *
              Kraus.evalWord B q) * W) := by
          congr 1
          rw [← h.evalWord q]
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hext', hsplit]
    calc
      Kraus.evalWord B w * W = z⁻¹ • (z • (Kraus.evalWord B w * W)) := by
        rw [smul_smul, inv_mul_cancel₀ hzne, one_smul]
      _ = z⁻¹ • (Kraus.evalWord B w * W') := by rw [hforward]

/-- Source-form boundary-dressed uniqueness, phrased using the least residual
nilpotency lengths of the two selected reductions.  Positive-length MPV
equality ensures that each least length is an actual bound; the two supplied
inequalities then promote those bounds to the common threshold `N₀`.

Source: Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2, Theorem 22,
`cornerproblem.tex` lines 3156--3162 and 4007--4035. -/
theorem exists_boundary_dressed_proportional_of_nilpotencyLength_le
    (h : IsReduction B A V W) (h' : IsReduction B A V' W')
    (hNormal : Kraus.IsNormal A) (hSame : SameMPV₂Pos B A) {N₀ : ℕ}
    (hLength : reductionResidualNilpotencyLength B A V W ≤ N₀)
    (hLength' : reductionResidualNilpotencyLength B A V' W' ≤ N₀) :
    ∃ z : ℂ, z ≠ 0 ∧ ∀ w : List (Fin d), 2 * N₀ < w.length →
      V * Kraus.evalWord B w = z • (V' * Kraus.evalWord B w) ∧
        Kraus.evalWord B w * W = z⁻¹ • (Kraus.evalWord B w * W') := by
  have hBound : IsReductionResidualNilpotencyBound B A V W N₀ := by
    intro w hw
    exact evalWord_reductionResidual_eq_zero_of_bound_le_length
      (h.reductionResidualNilpotencyLength_isBound hSame) w (by simpa [hw] using hLength)
  have hBound' : IsReductionResidualNilpotencyBound B A V' W' N₀ := by
    intro w hw
    exact evalWord_reductionResidual_eq_zero_of_bound_le_length
      (h'.reductionResidualNilpotencyLength_isBound hSame) w (by simpa [hw] using hLength')
  exact h.exists_boundary_dressed_proportional h' hNormal hBound hBound'

end IsReduction

end MPSTensor
