/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.MatrixReducedProjection
import QICLean.Analysis.SupportCompression
import TNLean.MPS.MPU.VirtualSandwich

/-!
# Reduced representatives of matrix product unitaries

This file formalizes the reduced-representative calculation in
[Cirac--Perez-Garcia--Schuch--Verstraete 2017, arXiv:1703.09188],
Proposition IV.5, lines 747--783. All fixed-point and support hypotheses are explicit:
none is inferred from the bare MPU predicate.
**Scope restriction (supplied fixed pair):** the source derives these
hypotheses by blocking to `D ^ 4` sites and passing through the isometry `V`
of the Proposition IV.5 argument, a supplier this file does not construct. See
`docs/paper-gaps/mpu_reduced_representative_supplied_fixed_pair.tex`.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}

private theorem evalWord_mul_of_letterwise_right_absorption
    (W : MPOTensor d D) (P : Matrix (Fin D) (Fin D) ℂ)
    (hWP : ∀ i j, W i j * P = W i j) :
    ∀ {is js : List (Fin d)}, is.length = js.length → is ≠ [] →
      evalWord W is js * P = evalWord W is js := by
  intro is
  induction is with
  | nil => simp
  | cons i is ih =>
      intro js hlen _
      cases js with
      | nil => simp at hlen
      | cons j js =>
          by_cases his : is = []
          · subst is
            have hjs : js = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
            subst js
            simp [evalWord, hWP]
          · simp only [evalWord_cons]
            rw [Matrix.mul_assoc, ih (by simpa using hlen) his]

private theorem mul_evalWord_of_letterwise_left_absorption
    (W : MPOTensor d D) (Q : Matrix (Fin D) (Fin D) ℂ)
    (hQW : ∀ i j, Q * W i j = W i j) :
    ∀ {is js : List (Fin d)}, is.length = js.length → is ≠ [] →
      Q * evalWord W is js = evalWord W is js := by
  intro is js hlen his
  cases is with
  | nil => exact (his rfl).elim
  | cons i is =>
      cases js with
      | nil => simp at hlen
      | cons j js =>
          simp only [evalWord_cons]
          rw [← Matrix.mul_assoc, hQW]

private theorem evalWord_virtualSandwich_reducedProjection
    (W : MPOTensor d D) (P Q : Matrix (Fin D) (Fin D) ℂ)
    (hP : IsOrthogonalProjection P)
    (hWP : ∀ i j, W i j * P = W i j)
    (hQW : ∀ i j, Q * W i j = W i j) :
    ∀ {is js : List (Fin d)}, is.length = js.length → is ≠ [] →
      evalWord (virtualSandwich (Matrix.reducedProjection P Q) W
        (Matrix.reducedProjection P Q)) is js =
      Matrix.reducedProjection P Q * evalWord W is js *
        Matrix.reducedProjection P Q := by
  let T := Matrix.reducedProjection P Q
  have hTproj := Matrix.reducedProjection_isOrthogonalProjection P Q
  have hTT : T * T = T := by simpa [T] using hTproj.2
  have hTQ : T * Q = P * Q := Matrix.reducedProjection_mul_second hP
  intro is
  induction is with
  | nil => simp
  | cons i is ih =>
      intro js hlen _
      cases js with
      | nil => simp at hlen
      | cons j js =>
          by_cases his : is = []
          · subst is
            have hjs : js = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
            subst js
            simp [evalWord, virtualSandwich, Matrix.mul_assoc]
          · have htail : is.length = js.length := by simpa using hlen
            have hQtail := mul_evalWord_of_letterwise_left_absorption W Q hQW htail his
            have hTtail : T * evalWord W is js = P * evalWord W is js := by
              calc
                T * evalWord W is js = T * (Q * evalWord W is js) := by rw [hQtail]
                _ = (T * Q) * evalWord W is js := by rw [Matrix.mul_assoc]
                _ = (P * Q) * evalWord W is js := by rw [hTQ]
                _ = P * evalWord W is js := by rw [Matrix.mul_assoc, hQtail]
            simp only [evalWord_cons, virtualSandwich_apply, ih htail his]
            change (T * W i j * T) * (T * evalWord W is js * T) =
              T * (W i j * evalWord W is js) * T
            calc
              (T * W i j * T) * (T * evalWord W is js * T) =
                  T * W i j * (T * T) * evalWord W is js * T := by
                    noncomm_ring
              _ = T * W i j * (T * evalWord W is js) * T := by
                    rw [hTT]
                    noncomm_ring
              _ = T * W i j * (P * evalWord W is js) * T := by rw [hTtail]
              _ = T * (W i j * P) * evalWord W is js * T := by
                    noncomm_ring
              _ = T * W i j * evalWord W is js * T := by rw [hWP]
              _ = T * (W i j * evalWord W is js) * T := by noncomm_ring

/-- The reduced tensor and the original tensor define the same periodic MPO at every
system size, under the paper's explicit letterwise support absorptions.

Source: arXiv:1703.09188, Proposition IV.5, lines 756 and 773--783. -/
theorem mpo_virtualSandwich_reducedProjection_eq
    (W : MPOTensor d D) (P Q : Matrix (Fin D) (Fin D) ℂ)
    (hP : IsOrthogonalProjection P)
    (hWP : ∀ i j, W i j * P = W i j)
    (hQW : ∀ i j, Q * W i j = W i j) (N : ℕ) :
    mpo (virtualSandwich (Matrix.reducedProjection P Q) W
      (Matrix.reducedProjection P Q)) N = mpo W N := by
  let T := Matrix.reducedProjection P Q
  have hTproj := Matrix.reducedProjection_isOrthogonalProjection P Q
  have hTQ : T * Q = P * Q := Matrix.reducedProjection_mul_second hP
  ext σ τ
  by_cases hN : N = 0
  · subst N
    simp [mpoMatrixEntry]
  · have hσ : (List.ofFn σ) ≠ [] := by
      intro hnil
      apply hN
      have := congrArg List.length hnil
      simpa using this
    have hword := evalWord_virtualSandwich_reducedProjection W P Q hP hWP hQW
      (is := List.ofFn σ) (js := List.ofFn τ)
      (show (List.ofFn σ).length = (List.ofFn τ).length by simp) hσ
    simp only [mpo_apply, mpoMatrixEntry, hword]
    have hlen : (List.ofFn σ).length = (List.ofFn τ).length := by simp
    have hQword := mul_evalWord_of_letterwise_left_absorption W Q hQW hlen hσ
    have hwordP := evalWord_mul_of_letterwise_right_absorption W P hWP hlen hσ
    calc
      Matrix.trace (T * evalWord W (List.ofFn σ) (List.ofFn τ) * T) =
          Matrix.trace (T * (T * evalWord W (List.ofFn σ) (List.ofFn τ))) := by
            rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (T * evalWord W (List.ofFn σ) (List.ofFn τ)) := by
            rw [← Matrix.mul_assoc, hTproj.2]
      _ = Matrix.trace (evalWord W (List.ofFn σ) (List.ofFn τ) * T) :=
            Matrix.trace_mul_comm _ _
      _ = Matrix.trace (T * evalWord W (List.ofFn σ) (List.ofFn τ)) :=
            Matrix.trace_mul_comm _ _
      _ = Matrix.trace (P * evalWord W (List.ofFn σ) (List.ofFn τ)) := by
            congr 1
            calc
              T * evalWord W (List.ofFn σ) (List.ofFn τ) =
                  T * (Q * evalWord W (List.ofFn σ) (List.ofFn τ)) := by rw [hQword]
              _ = (T * Q) * evalWord W (List.ofFn σ) (List.ofFn τ) := by
                    rw [Matrix.mul_assoc]
              _ = P * evalWord W (List.ofFn σ) (List.ofFn τ) := by
                    rw [hTQ, Matrix.mul_assoc, hQword]
      _ = Matrix.trace (evalWord W (List.ofFn σ) (List.ofFn τ) * P) :=
            Matrix.trace_mul_comm _ _
      _ = Matrix.trace (evalWord W (List.ofFn σ) (List.ofFn τ)) := by rw [hwordP]

private theorem transferMap_virtualSandwich_projection
    (W : MPOTensor d D) (T : Matrix (Fin D) (Fin D) ℂ) (hT : T.IsHermitian)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    transferMap (virtualSandwich T W T) X =
      T * transferMap W (T * X * T) * T := by
  simpa only [hT.eq] using transferMap_virtualSandwich T W T X

/-- The reduced tensor has the compressed rank-one transfer formula.

The rank-one formula is supplied as a hypothesis rather than derived from `IsMPU`;
the matrices `P` and `Q` forming the reduced projection are parameters.

Source: arXiv:1703.09188, Proposition IV.5, lines 747--752 and 778--781. -/
theorem transferMap_virtualSandwich_reducedProjection
    (W : MPOTensor d D) (L R P Q : Matrix (Fin D) (Fin D) ℂ)
    (hTransfer : ∀ X, transferMap W X = Matrix.trace (L * X) • R)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    transferMap (virtualSandwich (Matrix.reducedProjection P Q) W
      (Matrix.reducedProjection P Q)) X =
      Matrix.trace ((Matrix.reducedProjection P Q * L *
        Matrix.reducedProjection P Q) * X) •
        (Matrix.reducedProjection P Q * R * Matrix.reducedProjection P Q) := by
  let T := Matrix.reducedProjection P Q
  have hTproj := Matrix.reducedProjection_isOrthogonalProjection P Q
  rw [transferMap_virtualSandwich_projection W T hTproj.1 X, hTransfer]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc
    Matrix.trace (L * (T * X * T)) = Matrix.trace ((L * (T * X)) * T) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (T * (L * (T * X))) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((T * L * T) * X) := by simp only [Matrix.mul_assoc]

/-- The compressed left and right matrices retain the normalization
`trace (L * R) = 1` under the two-sided support absorptions for `L` and `R`.

Source: arXiv:1703.09188, Proposition IV.5, lines 750--752 and 778--781. -/
theorem trace_compressed_fixed_pair_reducedProjection
    (L R P Q : Matrix (Fin D) (Fin D) ℂ)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hPL : P * L = L) (hLP : L * P = L)
    (hQR : Q * R = R) (hRQ : R * Q = R)
    (htr : Matrix.trace (L * R) = 1) :
    Matrix.trace ((Matrix.reducedProjection P Q * L * Matrix.reducedProjection P Q) *
      (Matrix.reducedProjection P Q * R * Matrix.reducedProjection P Q)) = 1 := by
  let T := Matrix.reducedProjection P Q
  have hTproj := Matrix.reducedProjection_isOrthogonalProjection P Q
  have hTQ : T * Q = P * Q := Matrix.reducedProjection_mul_second hP
  have hQT : Q * T = Q * P := (Matrix.second_mul_reducedProjection hP hQ).symm
  have hTR : T * R = P * R := by
    calc
      T * R = T * (Q * R) := by rw [hQR]
      _ = (T * Q) * R := by rw [Matrix.mul_assoc]
      _ = P * R := by rw [hTQ, Matrix.mul_assoc, hQR]
  have hTT : T * T = T := by simpa [T] using hTproj.2
  calc
    Matrix.trace ((T * L * T) * (T * R * T)) =
        Matrix.trace (T * (L * T * (T * R * T))) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace ((L * T * (T * R * T)) * T) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (L * T * R * T) := by
      congr 1
      calc
        (L * T * (T * R * T)) * T = L * (T * T) * R * (T * T) := by
          noncomm_ring
        _ = L * T * R * T := by simp only [hTT]
    _ = Matrix.trace (L * R * T) := by
      congr 1
      calc
        L * T * R * T = L * (T * R) * T := by simp only [Matrix.mul_assoc]
        _ = L * (P * R) * T := by rw [hTR]
        _ = L * R * T := by rw [← Matrix.mul_assoc, hLP]
    _ = Matrix.trace (R * T * L) := by
      rw [show L * R * T = L * (R * T) by simp only [Matrix.mul_assoc]]
      rw [Matrix.trace_mul_cycle' L R T, Matrix.trace_mul_cycle' T L R]
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (R * L) := by
      congr 1
      calc
        R * T * L = (R * Q) * T * (P * L) := by rw [hRQ, hPL]
        _ = R * (Q * T) * (P * L) := by noncomm_ring
        _ = R * (Q * P) * (P * L) := by rw [hQT]
        _ = (R * Q) * (P * P) * L := by noncomm_ring
        _ = R * L := by rw [hRQ, hP.2, Matrix.mul_assoc, hPL]
    _ = Matrix.trace (L * R) := Matrix.trace_mul_comm R L
    _ = 1 := htr

/-- In isometric coordinates for the reduced range, both compressed fixed matrices are
positive definite. The right-hand statement uses reduced-range transversality, since the
reduced range need not be contained in `range Q`.

Source: arXiv:1703.09188, Proposition IV.5, lines 756 and 778--781. -/
theorem compressed_fixed_pair_posDef_reducedProjection
    (L R P Q : Matrix (Fin D) (Fin D) ℂ)
    (hL : L.PosSemidef) (hR : R.PosSemidef)
    (hLP : hL.supportProj = P) (hRQ : hR.supportProj = Q)
    {k : ℕ} (V : Matrix (Fin D) (Fin k) ℂ)
    (hV : Vᴴ * V = 1)
    (hVrange : V * Vᴴ = Matrix.reducedProjection P Q) :
    (Vᴴ * L * V).PosDef ∧ (Vᴴ * R * V).PosDef := by
  have hP : IsOrthogonalProjection P := by
    rw [← hLP]
    exact hL.isOrthogonalProjection_supportProj
  have hQ : IsOrthogonalProjection Q := by
    rw [← hRQ]
    exact hR.isOrthogonalProjection_supportProj
  let T := Matrix.reducedProjection P Q
  have hPT : P * T = T := Matrix.mul_reducedProjection hP
  have hVfixed (x : Fin k → ℂ) : T *ᵥ (V *ᵥ x) = V *ᵥ x := by
    rw [show T = V * Vᴴ by simpa [T] using hVrange.symm, Matrix.mulVec_mulVec]
    simp [Matrix.mul_assoc, hV]
  constructor
  · apply hL.compression_posDef_of_support_action_ne_zero V
    intro x hx hzero
    have hPx : P *ᵥ (V *ᵥ x) = V *ᵥ x := by
      calc
        P *ᵥ (V *ᵥ x) = P *ᵥ (T *ᵥ (V *ᵥ x)) := by rw [hVfixed]
        _ = (P * T) *ᵥ (V *ᵥ x) := by rw [Matrix.mulVec_mulVec]
        _ = V *ᵥ x := by rw [hPT, hVfixed]
    rw [hLP, hPx] at hzero
    exact hx (by
      have := congrArg (fun y ↦ Vᴴ *ᵥ y) hzero
      simpa [Matrix.mulVec_mulVec, hV] using this)
  · apply hR.compression_posDef_of_support_action_ne_zero V
    intro x hx hzero
    let y : EuclideanSpace ℂ (Fin D) := WithLp.toLp 2 (V *ᵥ x)
    have hy : y ≠ 0 := by
      intro hyzero
      apply hx
      have := congrArg (fun z : EuclideanSpace ℂ (Fin D) ↦ Vᴴ *ᵥ (z : Fin D → ℂ)) hyzero
      simpa [y, Matrix.mulVec_mulVec, hV] using this
    have hxKer : y ∈ LinearMap.ker (Matrix.toEuclideanLin Q) := by
      rw [LinearMap.mem_ker]
      simpa [y, hRQ, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using hzero
    have hxRange : y ∈ LinearMap.range (Matrix.toEuclideanLin T) := by
      refine ⟨y, ?_⟩
      simpa [y, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using hVfixed x
    have hdisj := Matrix.disjoint_ker_range_reducedProjection hP hQ
    exact hy ((Submodule.disjoint_def.mp hdisj) y hxKer (by simpa [T] using hxRange))

end MPOTensor
