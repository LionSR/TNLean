/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinsetEnumeration
import TNLean.MPS.Preparation.BlockGateUnitary
import TNLean.MPS.Preparation.SequentialFactorization

/-!
# The block unitary of a tensor that is not injective

For a blocked tensor `B = V P` that is not injective, the isometric factor `V` is a partial
isometry, `V†V = Π` with `Π` the projector onto the range of `P` (arXiv:2307.01696,
Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors"). A unitary `T` on
the pair space whose first `r` columns span the range of `Π`
(`Matrix.exists_unitary_mul_diagonal_of_isHermitian`) makes `V T` isometric on its first `r`
inputs and zero on the others; `V T` is a matrix product map, so it has a sequential
factorization on those inputs (`MPSPreparation.exists_isometric_chain_polarIsoMatrix_mul_unitary`),
and the block unitary of that chain, preceded by the gate `T†` on the input pair
(`MPSPreparation.exists_blockUnitary_of_equiv_mul`), implements an isometry `W` with `W Π = V`,
an isometric extension of `V` (`MPSPreparation.exists_blockUnitary_isometricExtension`).

## Main results

* `Matrix.exists_unitary_mul_diagonal_of_isHermitian` — an orthonormal basis adapted to an
  orthogonal projector.
* `MPSTensor.polarIsoMatrix_mul_polarSupportMatrix` — `V Π = V`.
* `MPSPreparation.exists_blockUnitary_isometricExtension` — a block unitary of depth `O(q)`
  implementing an isometric extension of `V`.

## References

* arXiv:2307.01696, paragraph "The sequential-RG circuit" and its footnote ("The subsequent
  derivation remains valid also for non-injective tensors `B`. In that case `P⁻¹` is understood
  as pseudo-inverse."), and Supplemental Material, "Proof of Lemma 1 and extension to non-normal
  tensors" (`V†V = Π`).
-/

open Matrix MPSTensor
open MPSChainTensor (eval)
open scoped BigOperators ComplexOrder
open QuantumCircuit

/-! ### A basis adapted to a projector -/

namespace Matrix

/-- **An orthonormal basis adapted to an orthogonal projector.** For a Hermitian idempotent `E`
on `ℂ^m` there are `r ≤ m` and a unitary `T` whose first `r` columns span the range of `E` and
whose other columns span its kernel: `E T = T diag(1, …, 1, 0, …, 0)`. -/
theorem exists_unitary_mul_diagonal_of_isHermitian {m : ℕ} {E : Matrix (Fin m) (Fin m) ℂ}
    (hE : E.IsHermitian) (hEE : E * E = E) :
    ∃ (r : ℕ) (T : Matrix (Fin m) (Fin m) ℂ), r ≤ m ∧ T ∈ unitary (Matrix (Fin m) (Fin m) ℂ) ∧
      E * T = T * diagonal fun y => if y.val < r then 1 else 0 := by
  classical
  set U : Matrix (Fin m) (Fin m) ℂ := ↑hE.eigenvectorUnitary with hUdef
  set μ : Fin m → ℂ := fun j => (hE.eigenvalues j : ℂ) with hμ
  have hU : U ∈ unitary (Matrix (Fin m) (Fin m) ℂ) := hE.eigenvectorUnitary.2
  have hEU : E * U = U * diagonal μ := by
    ext i j
    have h := congrFun (hE.mulVec_eigenvectorBasis j) i
    simp only [mulVec, dotProduct, Pi.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_eq_mul] at h
    rw [mul_diagonal, mul_apply]
    simpa [U, μ, mul_comm] using h
  have hμμ : ∀ j, μ j = 0 ∨ μ j = 1 := fun j => by
    have h : U * (diagonal μ * diagonal μ) = U * diagonal μ := by
      rw [← Matrix.mul_assoc, ← hEU, Matrix.mul_assoc, ← hEU, ← Matrix.mul_assoc, hEE]
    have h' := congrArg (star U * ·) h
    simp only [← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hU, Matrix.one_mul,
      diagonal_mul_diagonal] at h'
    have := congrFun (congrFun h' j) j
    simp only [diagonal_apply_eq] at this
    rcases mul_eq_zero.mp (show μ j * (μ j - 1) = 0 by rw [mul_sub, this]; ring) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (sub_eq_zero.mp h1)
  set S : Finset (Fin m) := Finset.univ.filter fun j => μ j = 1
  obtain ⟨π, hπ⟩ := Finset.exists_equiv_val_lt_card_iff_mem S
  set ρ : Fin m ≃ Fin m := (finCongr (Fintype.card_fin m).symm).trans π with hρ
  have hρS : ∀ y, ρ y ∈ S ↔ y.val < S.card := fun y => (hπ (finCongr _ y)).symm
  refine ⟨S.card, U.submatrix id ρ, ?_, ?_, ?_⟩
  · simpa using S.card_le_univ
  · refine (Matrix.mem_unitaryGroup_iff' (α := ℂ)).mpr ?_
    calc star (U.submatrix id ρ) * U.submatrix id ρ = (star U * U).submatrix ρ ρ := by
          ext; simp [mul_apply, star_eq_conjTranspose]
      _ = 1 := by rw [Unitary.star_mul_self_of_mem hU, submatrix_one_equiv]
  · ext i y
    have h := congrFun (congrFun hEU i) (ρ y)
    rw [mul_apply, mul_diagonal] at h ⊢
    simp only [submatrix_apply, id] at h ⊢
    rw [h]
    congr 1
    rcases hμμ (ρ y) with h0 | h1
    · have : ¬ y.val < S.card := fun hy => by
        have := (hρS y).mpr hy
        simp [S, h0] at this
      rw [h0, ite_eq_right this]
    · rw [h1, ite_eq_left ((hρS y).mp (by simp [S, h1]))]

end Matrix

/-! ### The isometric factor on the support projector -/

namespace MPSTensor

variable {n D : ℕ}

/-- **The isometric factor is supported on the projector:** `V Π = V`, as `V†V = Π` and
`Π² = Π`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors": `V†V = Π`. -/
theorem polarIsoMatrix_mul_polarSupportMatrix (B : MPSTensor n D) :
    polarIsoMatrix B * polarSupportMatrix B = polarIsoMatrix B := by
  set V := polarIsoMatrix B
  set E := polarSupportMatrix B
  have hE : Eᴴ = E := isHermitian_polarSupportMatrix B
  have h : (V * (1 - E))ᴴ * (V * (1 - E)) = 0 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ,
      conjTranspose_polarIsoMatrix_mul_polarIsoMatrix, conjTranspose_sub, conjTranspose_one, hE,
      Matrix.mul_sub, Matrix.mul_one, polarSupportMatrix_mul_self, sub_self, Matrix.mul_zero]
  have h' := conjTranspose_mul_self_eq_zero.mp h
  rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, eq_comm] at h'

end MPSTensor

/-! ### The block unitary implementing an isometric extension -/

namespace MPSPreparation

variable {d D : ℕ}

/-- **The unitary of a block implementing an isometric extension of the partial isometry.** Let
`D ≥ 1` and `dig` encode the bond indices injectively in `D` sites. There is `C` such that for
every chain `A₀, …, A_{q-1}` of tensors of bond dimension `D`, `q ≥ 3D`, there are a unitary `U`
on the `q` sites, a product of at most `C q` gates on neighbouring sites, and an isometry
`W : ℂ^{D²} → ℂ^{d^q}` with `W Π = V` for the polar decomposition `B = V P`, `V†V = Π`, of the
blocked tensor, such that `U |l, 0 ⋯ 0, r⟩ = W |l, r⟩`. No injectivity is assumed.

arXiv:2307.01696, paragraph "The sequential-RG circuit" and its footnote: the derivation of the
staircase "remains valid also for non-injective tensors `B`", with `P⁻¹` the pseudo-inverse; and
Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors", `V†V = Π`. -/
theorem exists_blockUnitary_isometricExtension (hd : 0 < d) {dig : Fin D → Cfg d D}
    (hdig : Function.Injective dig) (hD : 0 < D) :
    ∃ C : ℕ, ∀ q, 3 * D ≤ q → ∀ A : MPSChainTensor d D q,
      ∃ (U : Matrix (Cfg d q) (Cfg d q) ℂ)
        (W : Matrix (Fin (blockPhysDim d q)) (Fin (D * D)) ℂ),
        IsPairProduct d q (C * q) U ∧ W.IsIsometry ∧
        W * polarSupportMatrix (MPSChainTensor.blockTensor A) =
          polarIsoMatrix (MPSChainTensor.blockTensor A) ∧
        ∀ (l r : Fin D) τ, U τ (blockInputCfg hd q dig l r) =
          W ((decodeBlockEquiv d q).symm τ) (finProdFinEquiv (l, r)) := by
  classical
  obtain ⟨C, hC⟩ := exists_blockUnitary_of_equiv_mul hd (r₁ := D) hD hdig hD (virtualPairEquiv D)
  refine ⟨C, fun q hq A => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  set B := MPSChainTensor.blockTensor A with hBdef
  set V := polarIsoMatrix B with hV
  set E := polarSupportMatrix B with hEdef
  set dec := decodeBlockEquiv d (n + 1)
  obtain ⟨r, T, hr, hT, hET⟩ := Matrix.exists_unitary_mul_diagonal_of_isHermitian
    (isHermitian_polarSupportMatrix B) (polarSupportMatrix_mul_self B)
  set Λ : Matrix (Fin (D * D)) (Fin (D * D)) ℂ := diagonal fun y => if y.val < r then 1 else 0
    with hΛ
  obtain ⟨b, Q, hb0, hbl, -, hrow, -, hiso, hVQ, -⟩ :=
    exists_isometric_chain_polarIsoMatrix_mul_unitary A (Nat.succ_pos n) hr hT hET
  obtain ⟨U, Z, hU, hZ, hUZ⟩ := hC (n + 1) hq b Q hb0 hrow hiso (star T) (Unitary.star_mem hT)
  let W : Matrix (Fin (blockPhysDim d (n + 1))) (Fin (D * D)) ℂ := of fun i x =>
    U (dec i) (blockInputCfg hd (n + 1) dig (virtualPairEquiv D x).1 (virtualPairEquiv D x).2)
  have hWZ : W = (of fun i y => Z (dec i) y) * star T := by
    ext i x
    simp only [W, of_apply, mul_apply]
    exact hUZ x (dec i)
  refine ⟨U, W, hU, ?_, ?_, fun l r' τ => ?_⟩
  · -- the columns of `W` are columns of the unitary `U` at distinct configurations
    have hUu := Unitary.star_mul_self_of_mem hU.mem_unitary
    ext x x'
    rw [mul_apply, ← dec.symm.sum_comp]
    have h := congrFun (congrFun hUu
      (blockInputCfg hd (n + 1) dig (virtualPairEquiv D x).1 (virtualPairEquiv D x).2))
      (blockInputCfg hd (n + 1) dig (virtualPairEquiv D x').1 (virtualPairEquiv D x').2)
    rw [mul_apply] at h
    simp only [W, conjTranspose_apply, of_apply, Equiv.apply_symm_apply]
    simp only [star_apply] at h
    rw [h, one_apply, one_apply]
    refine if_congr ⟨fun hxx => ?_, fun hxx => by rw [hxx]⟩ rfl rfl
    obtain ⟨h1, h2⟩ := blockInputCfg_injective hd (by omega) hdig hxx
    exact (virtualPairEquiv D).injective (Prod.ext h1 h2)
  · -- `W Π = Z Λ T† = V T T† = V`
    have hTE : star T * E = Λ * star T := by
      have h := congrArg conjTranspose hET
      rwa [conjTranspose_mul, conjTranspose_mul, isHermitian_polarSupportMatrix B,
        diagonal_conjTranspose, ← star_eq_conjTranspose,
        show (star fun y : Fin (D * D) => if y.val < r then (1 : ℂ) else 0) =
          fun y => if y.val < r then 1 else 0 from funext fun y => by
            simp only [Pi.star_apply]; split_ifs <;> simp] at h
    have hZΛ : (of fun i y => Z (dec i) y) * Λ = V * T := by
      have hVTΛ : V * T * Λ = V * T := by
        rw [Matrix.mul_assoc, ← hET, ← Matrix.mul_assoc, hV,
          polarIsoMatrix_mul_polarSupportMatrix]
      rw [← hVTΛ]
      ext i y
      rw [hΛ, mul_diagonal, mul_diagonal, of_apply]
      split_ifs with hy
      · rw [hZ y (by rw [hbl]; exact hy), ← hVQ (dec i) y hy]
        simp [dec, V, B]
      · simp
    rw [hWZ, Matrix.mul_assoc, hTE, ← Matrix.mul_assoc, hZΛ, Matrix.mul_assoc,
      Unitary.mul_star_self_of_mem hT, Matrix.mul_one]
  · simp only [W, of_apply, Equiv.apply_symm_apply, virtualPairEquiv, Equiv.symm_apply_apply]

end MPSPreparation
