/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.AnnihilatingPowerPerturbation
import QICLean.Channel.KrausCPTP

/-!
# Lifting an annihilating perturbation into a matrix corner

An input corner prepared in one fixed matrix and an output corner read
only through its trace allow a rectangular perturbation to be lifted
to the full matrix algebra. Its square and its two products with the
original map vanish. This is the isolated middle-corner construction in
the cyclic selection argument for arXiv:1708.00029, Theorem 4.1.

A second construction couples two adjacent corners through a supplied
nilpotent middle map. The mixed products cancel and the square of the
original map kills the perturbation, preserving all powers from the
square onward. No complete-positivity conclusion is asserted here.
-/

open scoped Matrix

namespace Matrix

private theorem exists_hermitian_functional_killing {m : ℕ}
    (hm : 2 ≤ m) (ρ : Matrix (Fin m) (Fin m) ℂ) (hρ : ρ.IsHermitian) :
    ∃ φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ,
      φ ≠ 0 ∧ φ ρ = 0 ∧
      (∀ X, X.IsHermitian → IsSelfAdjoint (φ X)) := by
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have h' := congrArg Fin.val h
    simp only [i, j] at h'
    omega
  let e (k : Fin m) : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun X => X k k
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  by_cases hZero : ρ i i = 0
  · refine ⟨e i, ?_, hZero, ?_⟩
    · intro h
      have h' := congrArg (fun φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ =>
        φ (Matrix.single i i 1)) h
      change (Matrix.single i i (1 : ℂ)) i i = 0 at h'
      simp at h'
    · intro X hX
      change star (X i i) = X i i
      exact hX.apply i i
  · let φ := ρ j j • e i - ρ i i • e j
    refine ⟨φ, ?_, ?_, ?_⟩
    · intro h
      have h' := congrArg (fun ψ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ =>
        ψ (Matrix.single j j 1)) h
      change ρ j j * (Matrix.single j j (1 : ℂ)) i i -
        ρ i i * (Matrix.single j j (1 : ℂ)) j j = 0 at h'
      have hNeg : -(ρ i i) = 0 := by
        simpa [hij, hij.symm] using h'
      exact hZero (neg_eq_zero.mp hNeg)
    · change ρ j j * ρ i i - ρ i i * ρ j j = 0
      ring
    · intro X hX
      change star (ρ j j * X i i - ρ i i * X j j) =
        ρ j j * X i i - ρ i i * X j j
      rw [star_sub, star_mul, star_mul, hρ.apply j j, hρ.apply i i,
        hX.apply i i, hX.apply j j]
      ring

/-- Between matrix algebras of dimensions at least two, every Hermitian
prepared matrix is killed by a nonzero Hermitian-preserving complex-linear
map of zero output trace. No positivity or faithfulness assumption on the
prepared matrix is required. This supplies the algebraic direction in the
isolated-corner argument associated with arXiv:1708.00029, Theorem 4.1;
support in a prescribed Choi face is a separate condition. -/
theorem exists_nonzero_trace_zero_map_killing_hermitian {m n : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (ρ : Matrix (Fin m) (Fin m) ℂ) (hρ : ρ.IsHermitian) :
    ∃ L : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ,
      L ≠ 0 ∧ (∀ Y, (L Y).trace = 0) ∧ L ρ = 0 ∧
      (∀ Y, Y.IsHermitian → (L Y).IsHermitian) := by
  obtain ⟨φ, hφne, hφkill, hφherm⟩ := exists_hermitian_functional_killing hm ρ hρ
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨1, by omega⟩
  have huv : u ≠ v := by
    intro h
    have h' := congrArg Fin.val h
    simp only [u, v] at h'
    omega
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.single u u 1 - Matrix.single v v 1
  have hAne : A ≠ 0 := by
    intro h
    have h' := congrArg (fun B : Matrix (Fin n) (Fin n) ℂ => B u u) h
    simp [A, huv.symm] at h'
  have hAtrace : A.trace = 0 := by
    simp [A, Matrix.trace, Matrix.diag, Matrix.single_apply]
  have hAherm : A.IsHermitian := by
    change Aᴴ = A
    ext i j
    simp [A, Matrix.conjTranspose_apply, Matrix.single_apply, and_comm]
  let L := φ.smulRight A
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hφne
    ext X : 1
    change φ X = 0
    have h' := congrArg
      (fun T : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ => T X) h
    have hSmul : φ X • A = 0 := by simpa [L] using h'
    exact (smul_eq_zero.mp hSmul).resolve_right hAne
  · intro Y
    change (φ Y • A).trace = 0
    rw [Matrix.trace_smul, hAtrace, smul_zero]
  · change φ ρ • A = 0
    rw [hφkill, zero_smul]
  · intro Y hY
    exact hAherm.smul (hφherm Y hY)

private theorem recover_isometric_corner {D r : ℕ}
    (V : Matrix (Fin D) (Fin r) ℂ) (hV : Vᴴ * V = 1)
    (Y : Matrix (Fin r) (Fin r) ℂ) : Vᴴ * (V * Y * Vᴴ) * V = Y := by
  calc
    Vᴴ * (V * Y * Vᴴ) * V = (Vᴴ * V) * Y * (Vᴴ * V) := by
      simp only [Matrix.mul_assoc]
    _ = Y := by rw [hV, Matrix.one_mul, Matrix.mul_one]

/-- A nonzero Hermitian-preserving rectangular direction that kills the
incoming prepared matrix and has zero output trace lifts to a nonzero
annihilating direction on orthogonal matrix corners. The exact incoming
and outgoing branch identities are assumed, not inferred from channel
irreducibility. This is the isolated-corner construction used in the
written argument associated with arXiv:1708.00029, Theorem 4.1. Complete
positivity of the perturbed map and its Choi-face compatibility remain
separate obligations. -/
theorem exists_annihilating_corner_perturbation {D m n : ℕ}
    (V : Matrix (Fin D) (Fin m) ℂ) (W : Matrix (Fin D) (Fin n) ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) (hOrth : Vᴴ * W = 0)
    (F : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (L : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hLne : L ≠ 0)
    (ρ : Matrix (Fin m) (Fin m) ℂ) (σ : Matrix (Fin D) (Fin D) ℂ)
    (φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ)
    (hIn : ∀ X, Vᴴ * F X * V = φ X • ρ)
    (hOut : ∀ Y, F (W * Y * Wᴴ) = Y.trace • σ)
    (hTrace : ∀ Y, (L Y).trace = 0) (hKill : L ρ = 0)
    (hHerm : ∀ Y, Y.IsHermitian → (L Y).IsHermitian) :
    ∃ K : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ),
      K ≠ 0 ∧ (∀ X, K X = W * L (Vᴴ * X * V) * Wᴴ) ∧
      F * K = 0 ∧ K * F = 0 ∧ K * K = 0 ∧
      (∀ X, (K X).trace = 0) ∧
      (∀ X, X.IsHermitian → (K X).IsHermitian) ∧
      (∀ p : ℕ, 2 ≤ p → (F + K) ^ p = F ^ p) := by
  let K : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    singleKrausMap W ∘ₗ L ∘ₗ singleKrausMap Vᴴ
  have hK (X : Matrix (Fin D) (Fin D) ℂ) :
      K X = W * L (Vᴴ * X * V) * Wᴴ := by
    simp only [K, LinearMap.comp_apply, singleKrausMap_apply,
      Matrix.conjTranspose_conjTranspose]
  have hExtract (Y : Matrix (Fin n) (Fin n) ℂ) :
      Vᴴ * (W * Y * Wᴴ) * V = 0 := by
    calc
      Vᴴ * (W * Y * Wᴴ) * V = (Vᴴ * W) * Y * Wᴴ * V := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hOrth, Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]
  have hKne : K ≠ 0 := by
    intro hZero
    apply hLne
    ext Y : 1
    change L Y = 0
    have hEval : W * L Y * Wᴴ = 0 := by
      have h := congrArg
        (fun T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) => T (V * Y * Vᴴ)) hZero
      simpa only [hK, recover_isometric_corner V hV, LinearMap.zero_apply] using h
    have h := congrArg (fun Z => Wᴴ * Z * W) hEval
    simpa only [recover_isometric_corner W hW, Matrix.mul_zero, Matrix.zero_mul] using h
  have hFK : F * K = 0 := by
    ext X : 1
    change F (K X) = 0
    rw [hK, hOut, hTrace, zero_smul]
  have hKF : K * F = 0 := by
    ext X : 1
    change K (F X) = 0
    rw [hK, hIn, map_smul, hKill, smul_zero, Matrix.mul_zero, Matrix.zero_mul]
  have hExtractK (X : Matrix (Fin D) (Fin D) ℂ) : Vᴴ * K X * V = 0 := by
    rw [hK, hExtract]
  have hKK : K * K = 0 := by
    ext X : 1
    change K (K X) = 0
    calc
      K (K X) = W * L (Vᴴ * K X * V) * Wᴴ := hK (K X)
      _ = 0 := by rw [hExtractK, map_zero, Matrix.mul_zero, Matrix.zero_mul]
  have hKtrace (X : Matrix (Fin D) (Fin D) ℂ) : (K X).trace = 0 := by
    rw [hK, Matrix.trace_mul_cycle, hW, Matrix.one_mul, hTrace]
  have hKherm (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.IsHermitian) :
      (K X).IsHermitian := by
    rw [hK]
    exact Matrix.isHermitian_mul_mul_conjTranspose W
      (hHerm _ (Matrix.isHermitian_conjTranspose_mul_mul V hX))
  refine ⟨K, hKne, hK, hFK, hKF, hKK, hKtrace, hKherm, ?_⟩
  intro p hp
  exact add_pow_eq_of_annihilating_square_zero hFK hKF hKK hp

/-- The isolated-corner branch identities give a nonzero annihilating
direction whenever both corner dimensions are at least two and the
incoming prepared matrix is Hermitian. This removes the supplied
rectangular direction from the isolated-corner construction for
arXiv:1708.00029, Theorem 4.1. Complete positivity and compatibility with
the original Choi support remain separate obligations. -/
theorem exists_annihilating_corner_perturbation_of_two_le {D m n : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (V : Matrix (Fin D) (Fin m) ℂ) (W : Matrix (Fin D) (Fin n) ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) (hOrth : Vᴴ * W = 0)
    (F : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (ρ : Matrix (Fin m) (Fin m) ℂ) (hρ : ρ.IsHermitian)
    (σ : Matrix (Fin D) (Fin D) ℂ)
    (φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ)
    (hIn : ∀ X, Vᴴ * F X * V = φ X • ρ)
    (hOut : ∀ Y, F (W * Y * Wᴴ) = Y.trace • σ) :
    ∃ K : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ),
      K ≠ 0 ∧ F * K = 0 ∧ K * F = 0 ∧ K * K = 0 ∧
      (∀ X, (K X).trace = 0) ∧
      (∀ X, X.IsHermitian → (K X).IsHermitian) ∧
      (∀ p : ℕ, 2 ≤ p → (F + K) ^ p = F ^ p) := by
  obtain ⟨L, hLne, hTrace, hKill, hHerm⟩ :=
    exists_nonzero_trace_zero_map_killing_hermitian hm hn ρ hρ
  obtain ⟨K, hKne, _, hFK, hKF, hKK, hKT, hKH, hPow⟩ :=
    exists_annihilating_corner_perturbation V W hV hW hOrth F L hLne
      ρ σ φ hIn hOut hTrace hKill hHerm
  exact ⟨K, hKne, hFK, hKF, hKK, hKT, hKH, hPow⟩

private theorem extract_orthogonal_corner_zero {D m n : ℕ}
    (V : Matrix (Fin D) (Fin m) ℂ) (W : Matrix (Fin D) (Fin n) ℂ)
    (hOrth : Vᴴ * W = 0) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Vᴴ * (W * Y * Wᴴ) * V = 0 := by
  calc
    Vᴴ * (W * Y * Wᴴ) * V = (Vᴴ * W) * Y * Wᴴ * V := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hOrth, Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]

/-- A supplied nilpotent, trace-zero middle map gives opposite changes
in two adjacent matrix corners. Their mixed products cancel, and every
power from the square onward is unchanged for every scalar parameter.
The exact branch identities and middle direction are explicit hypotheses;
complete positivity and Choi-face compatibility are separate obligations.
This is the coupled-corner construction in the written selection argument
associated with arXiv:1708.00029, Theorem 4.1. -/
theorem exists_anticommuting_two_corner_perturbation {D a b c : ℕ}
    (V : Matrix (Fin D) (Fin a) ℂ) (W : Matrix (Fin D) (Fin b) ℂ)
    (U : Matrix (Fin D) (Fin c) ℂ)
    (hW : Wᴴ * W = 1) (hU : Uᴴ * U = 1)
    (hVW : Vᴴ * W = 0) (hVU : Vᴴ * U = 0) (hWU : Wᴴ * U = 0)
    (F : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (P : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ)
    (Q : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin c) (Fin c) ℂ)
    (H : Module.End ℂ (Matrix (Fin b) (Fin b) ℂ))
    (ρ : Matrix (Fin a) (Fin a) ℂ) (σ : Matrix (Fin D) (Fin D) ℂ)
    (φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ)
    (hInV : ∀ X, Vᴴ * F X * V = φ X • ρ)
    (hInW : ∀ X, Wᴴ * F X * W = P (Vᴴ * X * V))
    (hOutW : ∀ Y, F (W * Y * Wᴴ) = U * Q Y * Uᴴ)
    (hOutU : ∀ Z, F (U * Z * Uᴴ) = Z.trace • σ)
    (hQTrace : ∀ Y, (Q Y).trace = Y.trace)
    (hHTrace : ∀ Y, (H Y).trace = 0) (hKill : H (P ρ) = 0)
    (hHH : H * H = 0) (hQH : Q ∘ₗ H ≠ 0)
    (hPHerm : ∀ X, X.IsHermitian → (P X).IsHermitian)
    (hQHerm : ∀ Y, Y.IsHermitian → (Q Y).IsHermitian)
    (hHHerm : ∀ Y, Y.IsHermitian → (H Y).IsHermitian) :
    ∃ K : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ),
      K ≠ 0 ∧
      (∀ X, K X = W * H (P (Vᴴ * X * V)) * Wᴴ -
        U * Q (H (Wᴴ * X * W)) * Uᴴ) ∧
      F * K + K * F = 0 ∧ K * K = 0 ∧ F ^ 2 * K = 0 ∧
      (∀ X, (K X).trace = 0) ∧
      (∀ X, X.IsHermitian → (K X).IsHermitian) ∧
      (∀ t : ℂ, ∀ p : ℕ, 2 ≤ p → (F + t • K) ^ p = F ^ p) := by
  let K : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    (singleKrausMap W ∘ₗ H ∘ₗ P ∘ₗ singleKrausMap Vᴴ) -
      (singleKrausMap U ∘ₗ Q ∘ₗ H ∘ₗ singleKrausMap Wᴴ)
  have hK (X : Matrix (Fin D) (Fin D) ℂ) :
      K X = W * H (P (Vᴴ * X * V)) * Wᴴ -
        U * Q (H (Wᴴ * X * W)) * Uᴴ := by
    simp only [K, LinearMap.sub_apply, LinearMap.comp_apply, singleKrausMap_apply,
      Matrix.conjTranspose_conjTranspose]
  have hVWK := extract_orthogonal_corner_zero V W hVW
  have hVUK := extract_orthogonal_corner_zero V U hVU
  have hWUK := extract_orthogonal_corner_zero W U hWU
  have hExtractV (X : Matrix (Fin D) (Fin D) ℂ) : Vᴴ * K X * V = 0 := by
    rw [hK, Matrix.mul_sub, Matrix.sub_mul, hVWK, hVUK, sub_self]
  have hExtractW (X : Matrix (Fin D) (Fin D) ℂ) :
      Wᴴ * K X * W = H (P (Vᴴ * X * V)) := by
    rw [hK, Matrix.mul_sub, Matrix.sub_mul, recover_isometric_corner W hW,
      hWUK, sub_zero]
  have hKne : K ≠ 0 := by
    intro hZero
    apply hQH
    ext Y : 1
    change Q (H Y) = 0
    have hLift : U * Q (H Y) * Uᴴ = 0 := by
      have h := congrArg
        (fun T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) => T (W * Y * Wᴴ)) hZero
      simpa only [hK, hVWK, recover_isometric_corner W hW, map_zero,
        Matrix.mul_zero, Matrix.zero_mul, zero_sub, LinearMap.zero_apply,
        neg_eq_zero] using h
    have h := congrArg (fun Z => Uᴴ * Z * U) hLift
    simpa only [recover_isometric_corner U hU, Matrix.mul_zero, Matrix.zero_mul] using h
  have hFK (X : Matrix (Fin D) (Fin D) ℂ) :
      F (K X) = U * Q (H (P (Vᴴ * X * V))) * Uᴴ := by
    rw [hK, map_sub, hOutW, hOutU, hQTrace, hHTrace, zero_smul, sub_zero]
  have hKF (X : Matrix (Fin D) (Fin D) ℂ) :
      K (F X) = -(U * Q (H (P (Vᴴ * X * V))) * Uᴴ) := by
    rw [hK, hInV, hInW, map_smul, map_smul, hKill, smul_zero,
      Matrix.mul_zero, Matrix.zero_mul, zero_sub]
  have hMixed : F * K + K * F = 0 := by
    ext X : 1
    change F (K X) + K (F X) = 0
    rw [hFK, hKF, add_neg_cancel]
  have hHHApply (Y : Matrix (Fin b) (Fin b) ℂ) : H (H Y) = 0 := by
    exact congrArg (fun T : Module.End ℂ (Matrix (Fin b) (Fin b) ℂ) => T Y) hHH
  have hKK : K * K = 0 := by
    ext X : 1
    change K (K X) = 0
    calc
      K (K X) = W * H (P (Vᴴ * K X * V)) * Wᴴ -
          U * Q (H (Wᴴ * K X * W)) * Uᴴ := hK (K X)
      _ = 0 := by
        rw [hExtractV, hExtractW]
        simp only [map_zero, hHHApply, Matrix.mul_zero, Matrix.zero_mul, sub_self]
  have hSqK : F ^ 2 * K = 0 := by
    ext X : 1
    change F (F (K X)) = 0
    rw [hFK, hOutU, hQTrace, hHTrace, zero_smul]
  have hTrace (X : Matrix (Fin D) (Fin D) ℂ) : (K X).trace = 0 := by
    rw [hK, Matrix.trace_sub, Matrix.trace_mul_cycle, hW, Matrix.one_mul,
      Matrix.trace_mul_cycle, hU, Matrix.one_mul, hHTrace, hQTrace, hHTrace, sub_self]
  have hHerm (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.IsHermitian) :
      (K X).IsHermitian := by
    rw [hK]
    exact (Matrix.isHermitian_mul_mul_conjTranspose W
      (hHHerm _ (hPHerm _ (Matrix.isHermitian_conjTranspose_mul_mul V hX)))).sub
      (Matrix.isHermitian_mul_mul_conjTranspose U
        (hQHerm _ (hHHerm _ (Matrix.isHermitian_conjTranspose_mul_mul W hX))))
  refine ⟨K, hKne, hK, hMixed, hKK, hSqK, hTrace, hHerm, ?_⟩
  intro t p hp
  apply add_pow_eq_of_anticommuting_square_zero (F := F) (H := t • K) ?_ ?_ ?_ hp
  · rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_add, hMixed, smul_zero]
  · rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hKK, smul_zero, smul_zero]
  · rw [Algebra.mul_smul_comm, hSqK, smul_zero]

end Matrix
