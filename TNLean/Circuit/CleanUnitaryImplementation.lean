/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import TNLean.Circuit.QuantitativeUnitaryGates
import TNLean.Circuit.ZeroRegisterReflection
import TNLean.Circuit.PairProductPowers
open QuantumCircuit

/-!
# Unitary implementations with a reusable initialized workspace

Let `J` include the logical space into the full space with workspace in
its initialized state. The equality `U * J = J * Z` says that the ambient
operator implements `Z` on every logical input and returns the workspace
to its initial state. This equality is preserved by products and powers.
If both operators are unitary, it is also preserved by adjoints and
inverses. These facts justify reusing one scratch register in the nested
reflections of Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.

The closure results are algebraic statements about an actual matrix
equality. They do not assume a circuit decomposition. Separate existence
results below derive such a decomposition from a logical unitary by
unitary extension and the quantitative neighboring-pair synthesis. The
bound `38 * (d ^ n) ^ 6` is exponential in the number of sites `n`; in
the MPU construction it is used on packets with only `O(log D)` sites.
-/

open Matrix
open scoped Kronecker

namespace QuantumCircuit

section Matrices

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The initialized logical space is invariant and the workspace is returned
to its initialized state. When `J` is an initialized basis inclusion, this
identity holds on every logical state, including states entangled with a
reference. The identity alone does not assert that either operator is unitary.
Source: reusable scratch in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def IsCleanImplementation (J : Matrix ι κ ℂ) (U : Matrix ι ι ℂ)
    (Z : Matrix κ κ ℂ) : Prop :=
  U * J = J * Z

namespace IsCleanImplementation

/-- The identity operation preserves initialized workspace. Source: the
clean-workspace convention in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem one (J : Matrix ι κ ℂ) : IsCleanImplementation J 1 1 := by
  simp [IsCleanImplementation]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Two clean implementations may use the same workspace consecutively.
Source: the recursive composition in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem mul {J : Matrix ι κ ℂ} {U V : Matrix ι ι ℂ} {Z W : Matrix κ κ ℂ}
    (hU : IsCleanImplementation J U Z) (hV : IsCleanImplementation J V W) :
    IsCleanImplementation J (U * V) (Z * W) := by
  change U * J = J * Z at hU
  change V * J = J * W at hV
  change U * V * J = J * (Z * W)
  rw [Matrix.mul_assoc, hV, ← Matrix.mul_assoc, hU, Matrix.mul_assoc]

/-- Repetition of a clean implementation returns the same workspace to its
initialized state after every iteration. Source: the amplification powers in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem pow {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J U Z) (k : ℕ) :
    IsCleanImplementation J (U ^ k) (Z ^ k) := by
  induction k with
  | zero => simpa using one J
  | succ k ih => simpa only [pow_succ] using ih.mul h

/-- The adjoint of a clean implementation of a full logical unitary is
also clean. Unitarity is required on the whole logical space, so this result
does not infer inverse cleanup from an isometry on only selected inputs.
Source: inverse calls in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem conjTranspose {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J U Z)
    (hU : U ∈ unitary (Matrix ι ι ℂ)) (hZ : Z ∈ unitary (Matrix κ κ ℂ)) :
    IsCleanImplementation J Uᴴ Zᴴ := by
  change U * J = J * Z at h
  change Uᴴ * J = J * Zᴴ
  have hUleft : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hU
  have hZright : Z * Zᴴ = 1 := Unitary.mul_star_self_of_mem hZ
  calc
    Uᴴ * J = Uᴴ * (J * (Z * Zᴴ)) := by rw [hZright, Matrix.mul_one]
    _ = Uᴴ * ((J * Z) * Zᴴ) := by rw [Matrix.mul_assoc]
    _ = Uᴴ * ((U * J) * Zᴴ) := by rw [h]
    _ = (Uᴴ * U) * J * Zᴴ := by simp only [Matrix.mul_assoc]
    _ = J * Zᴴ := by rw [hUleft, Matrix.one_mul]

/-- The star inverse of a clean unitary implementation is clean on every
logical input. Source: inverse calls in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem star {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J U Z)
    (hU : U ∈ unitary (Matrix ι ι ℂ)) (hZ : Z ∈ unitary (Matrix κ κ ℂ)) :
    IsCleanImplementation J (star U) (star Z) :=
  h.conjTranspose hU hZ

/-- The ordinary matrix inverse of a clean unitary implementation is clean.
Source: inverse calls in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem inv {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J U Z)
    (hU : U ∈ unitary (Matrix ι ι ℂ)) (hZ : Z ∈ unitary (Matrix κ κ ℂ)) :
    IsCleanImplementation J U⁻¹ Z⁻¹ := by
  rw [Matrix.inv_eq_left_inv (Unitary.star_mul_self_of_mem hU),
    Matrix.inv_eq_left_inv (Unitary.star_mul_self_of_mem hZ)]
  exact h.star hU hZ

omit [DecidableEq ι] [DecidableEq κ] in
/-- A clean implementation acts as the logical operator on all vectors,
with no change to the initialized workspace. Source: the all-input cleanup
condition in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem mulVec {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J U Z) (v : κ → ℂ) :
    U *ᵥ (J *ᵥ v) = J *ᵥ (Z *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun A ↦ A *ᵥ v) h

/-- An ambient unitary preserving an initialized isometric inclusion induces
an actual full unitary on the logical space. Source: the all-logical-input
condition in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem logical_mem_unitary {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ}
    {Z : Matrix κ κ ℂ} (h : IsCleanImplementation J U Z) (hJ : J.IsIsometry)
    (hU : U ∈ unitary (Matrix ι ι ℂ)) : Z ∈ unitary (Matrix κ κ ℂ) := by
  change U * J = J * Z at h
  have hUleft : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hU
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change Zᴴ * Z = 1
  calc
    Zᴴ * Z = Zᴴ * (Jᴴ * J) * Z := by rw [hJ, Matrix.mul_one]
    _ = (J * Z)ᴴ * (J * Z) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (U * J)ᴴ * (U * J) := by rw [h]
    _ = Jᴴ * (Uᴴ * U) * J := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hUleft, Matrix.mul_one, hJ]

/-- For an initialized isometric inclusion, ambient unitarity and the clean
identity already imply cleanup of the adjoint on every logical input.
Source: reusable inverse calls in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem conjTranspose_of_isometry {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ}
    {Z : Matrix κ κ ℂ} (h : IsCleanImplementation J U Z) (hJ : J.IsIsometry)
    (hU : U ∈ unitary (Matrix ι ι ℂ)) : IsCleanImplementation J Uᴴ Zᴴ :=
  h.conjTranspose hU (h.logical_mem_unitary hJ hU)

omit [DecidableEq ι] [DecidableEq κ] in
/-- A clean implementation remains valid in the presence of an arbitrary
finite reference system. This matrix identity includes every state entangled
with that reference. Source: the uniform cleanup condition in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem kronecker_one {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J U Z) (ρ : Type*) [Fintype ρ] [DecidableEq ρ] :
    IsCleanImplementation (J ⊗ₖ (1 : Matrix ρ ρ ℂ))
      (U ⊗ₖ (1 : Matrix ρ ρ ℂ)) (Z ⊗ₖ (1 : Matrix ρ ρ ℂ)) := by
  change (U ⊗ₖ (1 : Matrix ρ ρ ℂ)) * (J ⊗ₖ (1 : Matrix ρ ρ ℂ)) =
    (J ⊗ₖ (1 : Matrix ρ ρ ℂ)) * (Z ⊗ₖ (1 : Matrix ρ ρ ℂ))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h]

end IsCleanImplementation

/-- The matrix of an injective placement of logical basis vectors among
ambient basis vectors. Selecting initialized workspace coordinates is a
special case. Source: the initialized basis inclusions in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def initializedBasisMatrix (e : κ ↪ ι) : Matrix ι κ ℂ :=
  (1 : Matrix ι ι ℂ).submatrix id e

omit [Fintype κ] in
/-- A basis inclusion is an isometry. This follows from Mathlib's submatrix
multiplication and injective submatrix identity. Source: the initialized
subspace in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem initializedBasisMatrix_isIsometry (e : κ ↪ ι) :
    (initializedBasisMatrix e).IsIsometry := by
  simp only [Matrix.IsIsometry, initializedBasisMatrix, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_one]
  change (1 : Matrix ι ι ℂ).submatrix e (Equiv.refl ι) *
    (1 : Matrix ι ι ℂ).submatrix (Equiv.refl ι) e = 1
  rw [Matrix.submatrix_mul_equiv, Matrix.one_mul]
  exact Matrix.submatrix_one e e.injective

omit [Fintype κ] [DecidableEq κ] in
/-- Multiplying by a basis inclusion selects the corresponding input columns.
Source: the initialized columns in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem mul_initializedBasisMatrix (e : κ ↪ ι) (U : Matrix ι ι ℂ) :
    U * initializedBasisMatrix e = U.submatrix id e := by
  exact Matrix.mul_submatrix_one (Equiv.refl ι) e U

end Matrices

section Registers

variable {d n K : ℕ}

/-- An isometry with arbitrary finite output coordinates can be encoded by
an injective placement of its rows in a qudit register and then implemented
on prescribed initialized input columns. The neighboring-pair circuit is
derived, with the explicit Hilbert-dimension bound and exact global phase.
Source: the leaf and merger packets in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_isPairProduct_mul_initializedBasisMatrix_eq {ι κ : Type*}
    [Fintype ι] [DecidableEq κ]
    (hd : 2 ≤ d) (hn : 2 ≤ n) (f : ι ↪ (Fin n → Fin d)) (e : κ ↪ (Fin n → Fin d))
    {V : Matrix ι κ ℂ} (hV : V.IsIsometry) :
    ∃ U : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ,
      IsPairProduct d n (38 * (d ^ n) ^ 6) U ∧
      U * initializedBasisMatrix e = initializedBasisMatrix f * V := by
  classical
  have hencoded := (initializedBasisMatrix_isIsometry f).mul _ _ hV
  obtain ⟨U, hU, hUV⟩ := exists_isPairProduct_apply_embedding_eq hd hn hencoded e
  refine ⟨U, hU, ?_⟩
  rw [mul_initializedBasisMatrix]
  ext u k
  exact hUV u k

/-- Every full logical unitary admits a clean implementation along an
initialized basis inclusion by an actual neighboring-pair circuit. The
circuit is derived by unitary extension, with its global phase retained;
no clean implementation or synthesis witness is supplied. This quantitative
leaf construction is a derived consequence of Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_isPairProduct_isCleanImplementation {κ : Type*}
    [Fintype κ] [DecidableEq κ] (hd : 2 ≤ d) (hn : 2 ≤ n)
    (e : κ ↪ (Fin n → Fin d)) {Z : Matrix κ κ ℂ}
    (hZ : Z ∈ unitary (Matrix κ κ ℂ)) :
    ∃ U : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ,
      IsPairProduct d n (38 * (d ^ n) ^ 6) U ∧
      IsCleanImplementation (initializedBasisMatrix e) U Z := by
  have hZiso : Z.IsIsometry := Unitary.star_mul_self_of_mem hZ
  exact exists_isPairProduct_mul_initializedBasisMatrix_eq hd hn e e hZiso

variable {a : ℕ} [NeZero d]

/-- Include a logical register by appending initialized zero workspace.
Source: clean-workspace conventions in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def zeroWorkspaceEmbedding : (Fin n → Fin d) ↪ (Fin (n + a) → Fin d) where
  toFun x := Fin.append x 0
  inj' x y h := by
    funext i
    have hi := congrFun h (Fin.castAdd a i)
    simpa only [Fin.append_left] using hi

/-- The concrete zero-register circuit is a clean implementation of the
logical reflection on its entire logical space. Thus every inverse and
power of that circuit may reuse the same scratch register by the closure
results above. Source: the initialized-register reflection in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isCleanImplementation_zeroRegisterReflection (hd : 2 ≤ d) (ha : 0 < a) :
    IsCleanImplementation
      (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := a) (a := a)))
      (zeroRegisterReflection (d := d) ha)
      (1 - (2 : ℂ) • Matrix.diagonal fun x : (Fin a → Fin d) ↦ if x = 0 then (1 : ℂ) else 0) := by
  have hJ :
      initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := a) (a := a)) =
        (Matrix.of fun (z : (Fin (a + a) → Fin d)) (x : (Fin a → Fin d)) ↦
          if z = Fin.append x 0 then (1 : ℂ) else 0) := by
    ext z x
    rfl
  rw [IsCleanImplementation, hJ]
  exact zeroRegisterReflection_mul_cleanEmbedding hd ha

end Registers

end QuantumCircuit
