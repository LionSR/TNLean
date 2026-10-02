/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.EncodedUniformMergingCircuit
import TNLean.MPS.Preparation.QuantitativeSitePermutation

/-!
# Exact encoded merging in the original site coordinates

A site bijection places the joining packet at the end of the logical register.
Conjugate each actual child circuit by this bijection, apply the supported
encoded merger, and conjugate the result back. Each conjugation adds a
quadratic routing cost and fixes the reusable scratch pool. The initialized
columns, logical support, and exact scalar phase return to the original
coordinates.

The encoded joint columns and parent isometry are hypotheses of this coordinate
lemma. Their derivation from actual MPU intervals is a separate argument.
See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation
open scoped Kronecker Matrix ComplexOrder MatrixOrder

namespace MPSPreparation

variable {d n A : ℕ}

/-- The inverse site permutation is the exact adjoint of its operator.

See the coordinate changes in §5 of the circuit manuscript. -/
theorem permOp_conjTranspose (τ : Equiv.Perm (Fin n)) :
    (permOp (d := d) τ)ᴴ = permOp τ.symm := by
  have hinv : permOp (d := d) τ.symm * permOp τ = 1 := by
    rw [← permOp_mul]
    change permOp (τ⁻¹ * τ) = 1
    rw [inv_mul_cancel, permOp_one]
  calc
    (permOp τ)ᴴ = (permOp τ.symm * permOp τ) * (permOp τ)ᴴ := by rw [hinv, one_mul]
    _ = permOp τ.symm := by
      have hright : permOp (d := d) τ * (permOp τ)ᴴ = 1 := by
        simpa only [Matrix.star_eq_conjTranspose] using
          Unitary.mul_star_self_of_mem (permOp_mem_unitary (d := d) τ)
      rw [Matrix.mul_assoc, hright, mul_one]

/-- Pulling a logical matrix into permuted coordinates is adjoint conjugation.

See the coordinate changes in §5 of the circuit manuscript. -/
theorem permOp_conjTranspose_mul_mul (τ : Equiv.Perm (Fin n))
    (X : Matrix (Cfg d n) (Cfg d n) ℂ) :
    (permOp τ)ᴴ * X * permOp τ = X.submatrix (· ∘ τ.symm) (· ∘ τ.symm) := by
  simpa only [permOp_conjTranspose, Equiv.symm_symm] using
    permOp_mul_mul_conjTranspose τ.symm X

/-- A permutation sends logical support to its image under that permutation.

See the coordinate changes in §5 of the circuit manuscript. -/
theorem permOp_conjugate_mem_supportedOperators (τ : Equiv.Perm (Fin n))
    {S : Set (Fin n)} {X : Matrix (Cfg d n) (Cfg d n) ℂ}
    (hX : X ∈ supportedOperators d S) :
    permOp τ * X * (permOp τ)ᴴ ∈ supportedOperators d (τ '' S) := by
  have hid : embedOp id X = X := by
    ext x y
    rw [embedOp_apply,
      ite_eq_left (show AgreeOff id x y from fun i hi ↦ absurd rfl (hi i))]
    rfl
  have heq : permOp τ * X * (permOp τ)ᴴ = embedOp τ X := by
    rw [permOp_mul_mul_conjTranspose]
    conv_lhs => rw [← hid, embedOp_submatrix_perm]
    rfl
  rw [heq]
  exact embedOp_mem_supportedOperators_image τ.injective hX

/-- Multiplication by a site permutation reindexes the rows of any rectangular matrix.

See the coordinate changes in §5 of the circuit manuscript. -/
theorem permOp_mul_rectangular {κ : Type*} (τ : Equiv.Perm (Fin n))
    (F : Matrix (Cfg d n) κ ℂ) :
    (permOp (d := d) τ * F : Matrix (Cfg d n) κ ℂ) = F.submatrix (· ∘ τ) id := by
  ext x i
  simp only [Matrix.mul_apply, permOp, Matrix.of_apply, Matrix.submatrix_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    id_eq]

variable [NeZero d]

/-- Conjugating a circuit by a logical permutation fixing the workspace transports
its exact initialized columns, without any initialization condition outside them.

See the coordinate changes in §5 of the circuit manuscript. -/
theorem conjugate_workspaceFixedSitePerm_columns {κ : Type*}
    (τ : Equiv.Perm (Fin n))
    (C : Matrix (Cfg d (n + A)) (Cfg d (n + A)) ℂ)
    (E F : Matrix (Cfg d n) κ ℂ)
    (hcolumns : C *
        (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := A)) * E) =
      initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := A)) * F) :
    ((permOp (workspaceFixedSitePerm (a := A) τ) * C *
        (permOp (workspaceFixedSitePerm (a := A) τ))ᴴ) *
        (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := A)) *
          (permOp (d := d) τ * E : Matrix (Cfg d n) κ ℂ)) : Matrix (Cfg d (n + A)) κ ℂ) =
      initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := A)) *
        (permOp (d := d) τ * F : Matrix (Cfg d n) κ ℂ) := by
  let J := initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := A))
  let Q := permOp (d := d) (workspaceFixedSitePerm (a := A) τ)
  let P := permOp (d := d) τ
  have hQJ : Q * J = J * P := isCleanImplementation_permOp_workspaceFixedSitePerm τ
  have hQHJ : Qᴴ * J = J * Pᴴ :=
    (isCleanImplementation_permOp_workspaceFixedSitePerm (d := d) (a := A) τ).conjTranspose
      (permOp_mem_unitary _) (permOp_mem_unitary _)
  have hPunitary : Pᴴ * P = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.star_mul_self_of_mem (permOp_mem_unitary (d := d) τ)
  have hinput : Qᴴ * (J * (P * E)) = J * E := by
    rw [← Matrix.mul_assoc, hQHJ]
    calc
      (J * Pᴴ) * (P * E) = J * ((Pᴴ * P) * E) := by simp only [Matrix.mul_assoc]
      _ = J * E := by rw [hPunitary, Matrix.one_mul]
  change (Q * C * Qᴴ) * (J * (P * E)) = J * (P * F)
  calc
    _ = Q * (C * (Qᴴ * (J * (P * E)))) := by simp only [Matrix.mul_assoc]
    _ = Q * (C * (J * E)) := by rw [hinput]
    _ = Q * (J * F) := by rw [hcolumns]
    _ = (Q * J) * F := by rw [Matrix.mul_assoc]
    _ = (J * P) * F := by rw [hQJ]
    _ = J * (P * F) := by rw [Matrix.mul_assoc]

end MPSPreparation

namespace MPUCircuit

/-- The supported encoded merger in arbitrary original site coordinates. The two
child conjugations and final return each have additive quadratic routing cost.
Both the actual child circuits and their full initialized-workspace identities are
retained. Encoded joint columns and the normalized parent isometry remain the
explicit hypotheses of this coordinate lemma.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem exists_permuted_encoded_uniform_merging_circuit
    {d r q a A b L K₁ K₂ : ℕ} {ρ : Type*}
    [Fintype ρ] [DecidableEq ρ] [NeZero d]
    (hd : 2 ≤ d) (hr : 0 < r) (f : ρ ↪ Cfg d a) (e : Fin r ↪ Cfg d q)
    (he : e ⟨0, hr⟩ = fun _ ↦ Fin.castLE hd 0)
    {P : Matrix (Fin r) (Fin r) ℂ} (hP : P.PosDef)
    (siteEquiv : Fin (a + (2 * q + 2)) ≃ Fin L)
    (s : Fin b ↪ Fin (a + (2 * q + 2))) (hpool : b ≤ A) (hpool₂ : 2 ≤ A)
    (support : Set (Fin L))
    (hinputSupport : Set.range s ⊆ siteEquiv.symm '' support)
    (hpacketSupport :
      Set.range (Fin.natAdd a : Fin (2 * q + 2) → Fin (a + (2 * q + 2))) ⊆
        siteEquiv.symm '' support)
    (Z₁ Z₂ : Matrix (Cfg d L) (Cfg d L) ℂ)
    (C₁ C₂ : Matrix (Cfg d (L + A)) (Cfg d (L + A)) ℂ)
    (hC₁ : IsPairProduct d (L + A) K₁ C₁)
    (hC₂ : IsPairProduct d (L + A) K₂ C₂)
    (hclean₁ : IsCleanImplementation
      (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := L) (a := A))) C₁ Z₁)
    (hclean₂ : IsCleanImplementation
      (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := L) (a := A))) C₂ Z₂)
    (hZ₁support : Z₁ ∈ supportedOperators d support)
    (hZ₂support : Z₂ ∈ supportedOperators d support)
    (V : Matrix (ρ × (Fin r × Fin r))
      ({i : Fin (a + (2 * q + 2)) // i ∉ Set.range s} → Fin d) ℂ)
    (hchild :
      (Z₁.submatrix (· ∘ siteEquiv.symm) (· ∘ siteEquiv.symm) *
        Z₂.submatrix (· ∘ siteEquiv.symm) (· ∘ siteEquiv.symm)) *
          initializedBasisMatrix (zeroFlagEmbedding (d := d) s) =
      initializedBasisMatrix
        (appendBasisEmbedding f (compatibleBondDilationEmbedding hd e)) *
        ((1 : Matrix ρ ρ ℂ) ⊗ₖ
          initializedBasisMatrix (joiningChildBasisEmbedding (r := r) hd)) * V)
    (hparent : (normalizedJoiningParent hr P V).IsIsometry) :
    ∃ Z : Matrix (Cfg d L) (Cfg d L) ℂ,
    ∃ C : Matrix (Cfg d (L + A)) (Cfg d (L + A)) ℂ,
      Z ∈ unitary (Matrix (Cfg d L) (Cfg d L) ℂ) ∧
      Z ∈ supportedOperators d support ∧
      IsPairProduct d (L + A)
        (encodedUniformMergingGateCount d q L A b
          (K₁ + 4 * (L + A) ^ 2) (K₂ + 4 * (L + A) ^ 2) r + 4 * (L + A) ^ 2) C ∧
      IsCleanImplementation
        (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := L) (a := A))) C Z ∧
      C * (initializedBasisMatrix
          (zeroWorkspaceEmbedding (d := d) (n := L) (a := A)) *
        (initializedBasisMatrix (zeroFlagEmbedding (d := d) s)).submatrix
          (fun x : Cfg d L ↦ x ∘ siteEquiv) id) =
        initializedBasisMatrix
          (zeroWorkspaceEmbedding (d := d) (n := L) (a := A)) *
          (encodedJoiningParent hd hr f e P V).submatrix
            (fun x : Cfg d L ↦ x ∘ siteEquiv) id := by
  have hlength : a + (2 * q + 2) = L := by
    simpa only [Fintype.card_fin] using Fintype.card_congr siteEquiv
  subst L
  let J := initializedBasisMatrix
    (zeroWorkspaceEmbedding (d := d) (n := a + (2 * q + 2)) (a := A))
  let Q := permOp (d := d) (workspaceFixedSitePerm (a := A) siteEquiv)
  let R := permOp (d := d) siteEquiv
  have hroute := isCleanImplementation_permOp_workspaceFixedSitePerm (d := d) (a := A) siteEquiv
  have hrouteAdj := hroute.conjTranspose (permOp_mem_unitary _) (permOp_mem_unitary _)
  have hQ : IsPairProduct d ((a + (2 * q + 2)) + A)
      (2 * ((a + (2 * q + 2)) + A) ^ 2) Q := isPairProduct_permOp _
  have hC₁' := ((hQ.star.mul hC₁).mul hQ).mono
    (le_of_eq (by ring :
      (2 * ((a + (2 * q + 2)) + A) ^ 2 + K₁) +
          2 * ((a + (2 * q + 2)) + A) ^ 2 =
        K₁ + 4 * ((a + (2 * q + 2)) + A) ^ 2))
  have hC₂' := ((hQ.star.mul hC₂).mul hQ).mono
    (le_of_eq (by ring :
      (2 * ((a + (2 * q + 2)) + A) ^ 2 + K₂) +
          2 * ((a + (2 * q + 2)) + A) ^ 2 =
        K₂ + 4 * ((a + (2 * q + 2)) + A) ^ 2))
  have hclean₁' := (hrouteAdj.mul hclean₁).mul hroute
  have hclean₂' := (hrouteAdj.mul hclean₂).mul hroute
  rw [permOp_conjTranspose_mul_mul siteEquiv Z₁] at hclean₁'
  rw [permOp_conjTranspose_mul_mul siteEquiv Z₂] at hclean₂'
  obtain ⟨Z, W, hW, hZ, hWclean, _, hcolumns, hsupport⟩ :=
    exists_encoded_uniform_merging_circuit hd hr f e he hP s hpool hpool₂
      _ _ (Qᴴ * C₁ * Q) (Qᴴ * C₂ * Q) hC₁' hC₂' hclean₁' hclean₂' V hchild hparent
  have hnew := isPairProduct_isCleanImplementation_conjugate_workspaceFixedSitePerm
    siteEquiv hW hWclean
  have hZ₁' : Z₁.submatrix (· ∘ siteEquiv.symm) (· ∘ siteEquiv.symm) ∈
      supportedOperators d (siteEquiv.symm '' support) := by
    rw [← permOp_conjTranspose_mul_mul]
    simpa only [permOp_conjTranspose, Equiv.symm_symm] using
      permOp_conjugate_mem_supportedOperators siteEquiv.symm hZ₁support
  have hZ₂' : Z₂.submatrix (· ∘ siteEquiv.symm) (· ∘ siteEquiv.symm) ∈
      supportedOperators d (siteEquiv.symm '' support) := by
    rw [← permOp_conjTranspose_mul_mul]
    simpa only [permOp_conjTranspose, Equiv.symm_symm] using
      permOp_conjugate_mem_supportedOperators siteEquiv.symm hZ₂support
  have hZsupport := hsupport (siteEquiv.symm '' support) hZ₁' hZ₂'
    hinputSupport hpacketSupport
  have hreturnedSupport : R * Z * Rᴴ ∈ supportedOperators d support := by
    simpa only [Set.image_image, Function.comp_def, Equiv.apply_symm_apply, Set.image_id'] using
      permOp_conjugate_mem_supportedOperators siteEquiv hZsupport
  have hreturnedUnitary := hnew.2.logical_mem_unitary
    (initializedBasisMatrix_isIsometry _) hnew.1.mem_unitary
  refine ⟨R * Z * Rᴴ, Q * W * Qᴴ, hreturnedUnitary, hreturnedSupport,
    hnew.1, hnew.2, ?_⟩
  have hreturnedColumns := conjugate_workspaceFixedSitePerm_columns siteEquiv W
    (initializedBasisMatrix (zeroFlagEmbedding (d := d) s))
    (encodedJoiningParent hd hr f e P V) hcolumns
  rw [permOp_mul_rectangular (d := d) siteEquiv
    (initializedBasisMatrix (zeroFlagEmbedding (d := d) s)),
    permOp_mul_rectangular (d := d) siteEquiv (encodedJoiningParent hd hr f e P V)]
    at hreturnedColumns
  exact hreturnedColumns

end MPUCircuit
