/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.CyclicSectors.Compression

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

/-- If cyclic projections sum to `1`, then none of the summands can vanish. -/
theorem cyclic_projection_ne_zero_of_sum_one
    {m D : ℕ} [NeZero m] [NeZero D]
    {T : MatrixEnd D} {P : Fin m → MatrixAlg D}
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclic : ∀ k, T (P (k + 1)) = P k) :
    ∀ k, P k ≠ 0 := by
  by_contra! hzero
  obtain ⟨k₀, hk₀⟩ := hzero
  have hback : ∀ j : Fin m, P (j + 1) = 0 → P j = 0 := by
    intro j hj
    rw [← hCyclic j, hj, map_zero]
  have hall : ∀ j : Fin m, P j = 0 := by
    suffices hs : ∀ n : ℕ, n < m → ∀ j : Fin m,
        (k₀ - j).val = n → P j = 0 by
      intro j
      exact hs _ (k₀ - j).isLt j rfl
    intro n
    induction n with
    | zero =>
        intro _ j hj
        have : k₀ - j = 0 := by
          ext
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_eq_zero_iff] at hj ⊢
          exact hj
        have : k₀ = j := sub_eq_zero.mp this
        subst this
        exact hk₀
    | succ n ih =>
        intro hd j hj
        apply hback j
        apply ih (by omega) (j + 1)
        have h_eq : k₀ - (j + 1) = (k₀ - j) - 1 := by abel
        rw [h_eq, Fin.val_sub_one_of_ne_zero (by intro h; simp [h] at hj)]
        omega
  exact absurd
    (show (∑ k : Fin m, P k) = 0 from Finset.sum_eq_zero (fun k _ => hall k))
    (by rw [hPsum]; exact one_ne_zero)

/-- **Compression-transfer comparison theorem.**

Given a `∗`-algebra compression equivalence `φ : M_n(ℂ) ≃ₗ[ℂ] cornerSubmodule P`
intertwining the compressed adjoint transfer map (of `C`) with the
`P·B`-adjoint transfer map on the corner (`hIntertwine`), and preserving both
multiplication (`hMul`) and the adjoint (`hStar`), primitivity and
irreducibility of the corner restriction of the ambient `T = transferMap Bᴴ`
transport to primitivity and irreducibility of `transferMap Cᴴ`.

The proof uses `hMul` / `hStar` to lift orthogonal projections on
`M_n(ℂ)` to corner projections `Q = (φ Q').1 ≤ P`, transports
`PreservesCorner` across `φ` via the intertwining identity, and applies
`IsPrimitive.conj_iff_cross` to move primitivity across the cross-space
conjugation `cornerRestriction P T = φ.conj (transferMap Cᴴ)`.
-/
theorem compressedTensor_adjointTransferMap_cornerBridge
    {r D n : ℕ} [NeZero n]
    (B : MPSTensor r D) (C : MPSTensor r n) (P : MatrixAlg D)
    (T : MatrixEnd D)
    (φ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P)
    (hT :
      transferMap (d := r) (D := D) (fun i => (B i)ᴴ) = T)
    (hPproj : IsOrthogonalProjection P)
    (hIntertwine : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      (φ (transferMap (d := r) (D := n) (fun i => (C i)ᴴ) X)).1 =
        transferMap (d := r) (D := D) (fun i => (P * B i)ᴴ) ((φ X).1))
    (hMul : ∀ X Y : Matrix (Fin n) (Fin n) ℂ,
      (φ (X * Y)).1 = (φ X).1 * (φ Y).1)
    (hStar : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      (φ Xᴴ).1 = ((φ X).1)ᴴ)
    (hInv : PreservesCorner P T)
    (hCornerPrim :
      _root_.IsPrimitive (cornerRestriction P T hInv))
    (hCornerIrr : IsIrreducibleOnCorner P T) :
    _root_.IsPrimitive
      (transferMap (d := r) (D := n) (fun i => (C i)ᴴ)) ∧
      IsIrreducibleMap
        (transferMap (d := r) (D := n) (fun i => (C i)ᴴ)) := by
  classical
  set F_C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    transferMap (d := r) (D := n) (fun i => (C i)ᴴ) with hF_C_def
  have hPherm : Pᴴ = P := hPproj.1.eq
  -- On the corner, the ambient `T` and the `P*B`-adjoint transfer map agree.
  have hTeq :
      ∀ Y : MatrixAlg D, P * Y * P = Y →
        transferMap (d := r) (D := D) (fun i => (P * B i)ᴴ) Y = T Y := by
    intro Y hY
    have hstep :
        transferMap (d := r) (D := D) (fun i => (P * B i)ᴴ) Y =
          transferMap (d := r) (D := D) (fun i => (B i)ᴴ) Y := by
      simp only [transferMap_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      have hPBi : ((P * B i)ᴴ) = (B i)ᴴ * P := by
        rw [Matrix.conjTranspose_mul, hPherm]
      simp only [Matrix.conjTranspose_conjTranspose]
      rw [hPBi]
      calc
        (B i)ᴴ * P * Y * (P * B i)
            = (B i)ᴴ * (P * Y * P) * B i := by
              simp [Matrix.mul_assoc]
        _ = (B i)ᴴ * Y * B i := by rw [hY]
    rw [hstep, hT]
  -- `cornerRestriction P T hInv = φ.conj F_C`.
  have hConj :
      cornerRestriction P T hInv = φ.conj F_C := by
    refine LinearMap.ext ?_
    intro Y
    refine Subtype.ext ?_
    change T Y.1 = (φ.conj F_C Y).1
    rw [LinearEquiv.conj_apply_apply]
    have hkey := hIntertwine (φ.symm Y)
    have hφsy : (φ (φ.symm Y)).1 = Y.1 :=
      congrArg Subtype.val (LinearEquiv.apply_symm_apply φ Y)
    rw [hφsy] at hkey
    rw [hkey]
    exact (hTeq Y.1 Y.2).symm
  -- Primitivity: transport from the corner via cross-space conjugation.
  have hPrim_F_C : _root_.IsPrimitive F_C :=
    (IsPrimitive.conj_iff_cross (e := φ) (f := F_C)).mp (hConj ▸ hCornerPrim)
  -- Irreducibility: map orthogonal projections `Q'` in `M_n(ℂ)` to corner projections.
  -- `(φ 1).1 = P` since `(φ 1).1` is the identity of `cornerSubmodule P`.
  have hφ1_eq_P : (φ 1).1 = P := by
    have hPcorn : P * P * P = P := by rw [hPproj.2, hPproj.2]
    set Yinv : Matrix (Fin n) (Fin n) ℂ := φ.symm ⟨P, hPcorn⟩
    have hφYinv : (φ Yinv).1 = P :=
      congrArg Subtype.val (LinearEquiv.apply_symm_apply φ ⟨P, hPcorn⟩)
    have hPleft : (φ 1).1 * P = P := by
      have hmul := hMul 1 Yinv
      rw [one_mul, hφYinv] at hmul
      exact hmul.symm
    calc
      (φ 1).1 = P * (φ 1).1 * P := ((φ 1).2).symm
      _ = P * ((φ 1).1 * P) := by simp [Matrix.mul_assoc]
      _ = P * P := by rw [hPleft]
      _ = P := hPproj.2
  have hIrr : IsIrreducibleMap F_C := by
    intro Q' hQ'proj hQ'preserves
    set Q : MatrixAlg D := (φ Q').1 with hQ_def
    have hQ_corner : P * Q * P = Q := (φ Q').2
    have hQherm : Qᴴ = Q := by
      have hstar := hStar Q'
      rw [hQ'proj.1.eq] at hstar
      exact hstar.symm
    have hQidem : Q * Q = Q := by
      have h1 := hMul Q' Q'
      rw [hQ'proj.2] at h1
      exact h1.symm
    have hQP : Q * P = Q := by
      calc Q * P = P * Q * P * P := by rw [hQ_corner]
        _ = P * Q * (P * P) := by simp [Matrix.mul_assoc]
        _ = P * Q * P := by rw [hPproj.2]
        _ = Q := hQ_corner
    have hPQ : P * Q = Q := by
      calc P * Q = P * (P * Q * P) := by rw [hQ_corner]
        _ = (P * P) * Q * P := by simp [Matrix.mul_assoc]
        _ = P * Q * P := by rw [hPproj.2]
        _ = Q := hQ_corner
    have hQproj : IsOrthogonalProjection Q := ⟨hQherm, hQidem⟩
    -- PreservesCorner Q T: use `hIntertwine`, `hMul`, and Q'-invariance of F_C.
    have hQinv : PreservesCorner Q T := by
      intro Y
      set W : MatrixAlg D := P * Y * P with hW_def
      have hW_corner : P * W * P = W := by
        change P * (P * Y * P) * P = P * Y * P
        calc
          P * (P * Y * P) * P = (P * P) * Y * (P * P) := by simp [Matrix.mul_assoc]
          _ = P * Y * P := by rw [hPproj.2]
      have hQYQ_eq : Q * Y * Q = Q * W * Q := by
        calc Q * Y * Q
            = (Q * P) * Y * (P * Q) := by rw [hQP, hPQ]
          _ = Q * (P * Y * P) * Q := by simp [Matrix.mul_assoc]
          _ = Q * W * Q := rfl
      set W' : Matrix (Fin n) (Fin n) ℂ := φ.symm ⟨W, hW_corner⟩
      have hφW' : (φ W').1 = W :=
        congrArg Subtype.val (LinearEquiv.apply_symm_apply φ ⟨W, hW_corner⟩)
      set Z' : Matrix (Fin n) (Fin n) ℂ := Q' * W' * Q' with hZ'_def
      have hQWQ_φZ' : Q * W * Q = (φ Z').1 := by
        have hZ'assoc : Z' = Q' * (W' * Q') := by
          simp [hZ'_def, Matrix.mul_assoc]
        calc
          Q * W * Q = (φ Q').1 * W * (φ Q').1 := rfl
          _ = (φ Q').1 * (φ W').1 * (φ Q').1 := by rw [hφW']
          _ = (φ Q').1 * ((φ W').1 * (φ Q').1) := by simp [Matrix.mul_assoc]
          _ = (φ Q').1 * (φ (W' * Q')).1 := by rw [hMul W' Q']
          _ = (φ (Q' * (W' * Q'))).1 := by rw [hMul Q' (W' * Q')]
          _ = (φ Z').1 := by rw [← hZ'assoc]
      have hQYQ_φZ' : Q * Y * Q = (φ Z').1 := hQYQ_eq.trans hQWQ_φZ'
      -- F_C Z' ∈ corner(Q') by Q'-invariance of F_C.
      have hF_C_fix : Q' * F_C Z' * Q' = F_C Z' := by
        have := hQ'preserves W'
        simpa [hZ'_def, hF_C_def] using this
      -- Transport Q'-invariance of F_C via φ.
      have hφF_C_fix : (φ (F_C Z')).1 = Q * (φ (F_C Z')).1 * Q := by
        have key : (φ (Q' * F_C Z' * Q')).1 = Q * (φ (F_C Z')).1 * Q := by
          calc
            (φ (Q' * F_C Z' * Q')).1
                = (φ (Q' * (F_C Z' * Q'))).1 := by rw [Matrix.mul_assoc]
              _ = (φ Q').1 * (φ (F_C Z' * Q')).1 := hMul _ _
              _ = (φ Q').1 * ((φ (F_C Z')).1 * (φ Q').1) := by rw [hMul (F_C Z') Q']
              _ = Q * (φ (F_C Z')).1 * Q := by simp [hQ_def, Matrix.mul_assoc]
        rw [hF_C_fix] at key
        exact key
      -- `T ((φ Z').1) = (φ (F_C Z')).1`.
      have hTφZ' : T ((φ Z').1) = (φ (F_C Z')).1 := by
        have hZ'corner : P * (φ Z').1 * P = (φ Z').1 := (φ Z').2
        have hIw := (hIntertwine Z').symm
        rw [hTeq _ hZ'corner] at hIw
        exact hIw
      rw [hQYQ_φZ', hTφZ']
      exact hφF_C_fix.symm
    rcases hCornerIrr Q hQproj hQP hPQ hQinv with hQ0 | hQP_eq
    · left
      apply φ.injective
      apply Subtype.ext
      simp only [map_zero, Submodule.coe_zero]
      exact hQ0
    · right
      apply φ.injective
      apply Subtype.ext
      rw [hφ1_eq_P]
      exact hQP_eq
  exact ⟨hPrim_F_C, hIrr⟩

end MPSTensor
