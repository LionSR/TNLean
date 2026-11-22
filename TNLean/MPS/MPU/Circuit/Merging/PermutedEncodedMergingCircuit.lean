/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Circuit.Merging.EncodedUniformMergingCircuit
import QICLean.Circuit.Compile.SwapRouting
import QICLean.Circuit.Model.CleanWorkspace

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

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped Kronecker Matrix ComplexOrder MatrixOrder

namespace MPSPreparation

variable {d n A : ℕ}

/-- Pulling a logical matrix into permuted coordinates is adjoint conjugation.

See the coordinate changes in §5 of the circuit manuscript. -/
theorem conjTranspose_sitePermOp_mul_mul (τ : Equiv.Perm (Fin n))
    (X : Matrix (Cfg d n) (Cfg d n) ℂ) :
    (ManyBody.sitePermOp (α := Fin d) τ)ᴴ * X * ManyBody.sitePermOp τ =
      X.submatrix (· ∘ τ.symm) (· ∘ τ.symm) := by
  have h : ManyBody.sitePermOp (α := Fin d) τ = (ManyBody.sitePermOp (α := Fin d) τ⁻¹)ᴴ := by
    rw [ManyBody.conjTranspose_sitePermOp, inv_inv]
  rw [ManyBody.conjTranspose_sitePermOp, h]
  ext x y
  simp only [mul_apply, ManyBody.sitePermOp_apply, conjTranspose_apply, submatrix_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp [apply_ite star, Equiv.Perm.coe_inv]

/-- Multiplication by a site permutation reindexes the rows of any rectangular matrix.

See the coordinate changes in §5 of the circuit manuscript. -/
theorem sitePermOp_mul_rectangular {κ : Type*} (τ : Equiv.Perm (Fin n))
    (F : Matrix (Cfg d n) κ ℂ) :
    (ManyBody.sitePermOp (α := Fin d) τ * F : Matrix (Cfg d n) κ ℂ) =
      F.submatrix (· ∘ τ) id := by
  ext x i
  simp only [Matrix.mul_apply, ManyBody.sitePermOp_apply, Matrix.submatrix_apply,
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
        (basisInclusion (workspaceEmbedding (n := n) (0 : Fin A → Fin d)) * E) =
      basisInclusion (workspaceEmbedding (n := n) (0 : Fin A → Fin d)) * F) :
    ((ManyBody.sitePermOp (α := Fin d) (workspaceFixedSitePerm (a := A) τ) * C *
        (ManyBody.sitePermOp (α := Fin d) (workspaceFixedSitePerm (a := A) τ))ᴴ) *
        (basisInclusion (workspaceEmbedding (n := n) (0 : Fin A → Fin d)) *
          (ManyBody.sitePermOp (α := Fin d) τ * E : Matrix (Cfg d n) κ ℂ)) :
          Matrix (Cfg d (n + A)) κ ℂ) =
      basisInclusion (workspaceEmbedding (n := n) (0 : Fin A → Fin d)) *
        (ManyBody.sitePermOp (α := Fin d) τ * F : Matrix (Cfg d n) κ ℂ) := by
  let J := basisInclusion (workspaceEmbedding (n := n) (0 : Fin A → Fin d))
  let Q := ManyBody.sitePermOp (α := Fin d) (workspaceFixedSitePerm (a := A) τ)
  let P := ManyBody.sitePermOp (α := Fin d) τ
  have hroute := isCleanImplementation_sitePermOp_workspaceFixedSitePerm
    (0 : Fin A → Fin d) τ
  have hQJ : Q * J = J * P := hroute
  have hQHJ : Qᴴ * J = J * Pᴴ :=
    hroute.conjTranspose (ManyBody.sitePermOp_mem_unitary _) (ManyBody.sitePermOp_mem_unitary _)
  have hPunitary : Pᴴ * P = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.star_mul_self_of_mem (ManyBody.sitePermOp_mem_unitary (α := Fin d) τ)
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
    (support : Finset (Fin L))
    (hinputSupport : Set.range s ⊆ siteEquiv.symm '' support)
    (hpacketSupport :
      Set.range (Fin.natAdd a : Fin (2 * q + 2) → Fin (a + (2 * q + 2))) ⊆
        siteEquiv.symm '' support)
    (Z₁ Z₂ : Matrix (Cfg d L) (Cfg d L) ℂ)
    (C₁ C₂ : Matrix (Cfg d (L + A)) (Cfg d (L + A)) ℂ)
    (hC₁ : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (L + A))) K₁ C₁)
    (hC₂ : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (L + A))) K₂ C₂)
    (hclean₁ : IsCleanImplementation
      (basisInclusion (workspaceEmbedding (n := L) (0 : Fin A → Fin d))) C₁ Z₁)
    (hclean₂ : IsCleanImplementation
      (basisInclusion (workspaceEmbedding (n := L) (0 : Fin A → Fin d))) C₂ Z₂)
    (hZ₁support : Z₁ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) support)
    (hZ₂support : Z₂ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) support)
    (V : Matrix (ρ × (Fin r × Fin r))
      ({i : Fin (a + (2 * q + 2)) // i ∉ Set.range s} → Fin d) ℂ)
    (hchild :
      (Z₁.submatrix (· ∘ siteEquiv.symm) (· ∘ siteEquiv.symm) *
        Z₂.submatrix (· ∘ siteEquiv.symm) (· ∘ siteEquiv.symm)) *
          basisInclusion (zeroFlagEmbedding (d := d) s) =
      basisInclusion
        (appendBasisEmbedding f (compatibleBondDilationEmbedding hd e)) *
        ((1 : Matrix ρ ρ ℂ) ⊗ₖ
          basisInclusion (joiningChildBasisEmbedding (r := r) hd)) * V)
    (hparent : (normalizedJoiningParent hr P V).IsIsometry) :
    ∃ Z : Matrix (Cfg d L) (Cfg d L) ℂ,
    ∃ C : Matrix (Cfg d (L + A)) (Cfg d (L + A)) ℂ,
      Z ∈ unitary (Matrix (Cfg d L) (Cfg d L) ℂ) ∧
      Z ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) support ∧
      IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (L + A)))
        (encodedUniformMergingGateCount d q L A b
          (K₁ + 4 * (L + A) ^ 2) (K₂ + 4 * (L + A) ^ 2) r + 4 * (L + A) ^ 2) C ∧
      IsCleanImplementation
        (basisInclusion (workspaceEmbedding (n := L) (0 : Fin A → Fin d))) C Z ∧
      C * (basisInclusion
          (workspaceEmbedding (n := L) (0 : Fin A → Fin d)) *
        (basisInclusion (zeroFlagEmbedding (d := d) s)).submatrix
          (fun x : Cfg d L ↦ x ∘ siteEquiv) id) =
        basisInclusion
          (workspaceEmbedding (n := L) (0 : Fin A → Fin d)) *
          (encodedJoiningParent hd hr f e P V).submatrix
            (fun x : Cfg d L ↦ x ∘ siteEquiv) id := by
  have hlength : a + (2 * q + 2) = L := by
    simpa only [Fintype.card_fin] using Fintype.card_congr siteEquiv
  subst L
  let Q := ManyBody.sitePermOp (α := Fin d) (workspaceFixedSitePerm (a := A) siteEquiv)
  let R := ManyBody.sitePermOp (α := Fin d) siteEquiv
  have hroute := isCleanImplementation_sitePermOp_workspaceFixedSitePerm
    (0 : Fin A → Fin d) siteEquiv
  have hrouteAdj := hroute.conjTranspose (ManyBody.sitePermOp_mem_unitary _)
    (ManyBody.sitePermOp_mem_unitary _)
  have hQ : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph ((a + (2 * q + 2)) + A)))
      (2 * ((a + (2 * q + 2)) + A) ^ 2) Q := isGateProduct_sitePermOp _
  have hC₁' := ((hQ.conjTranspose.mul hC₁).mul hQ).mono
    (le_of_eq (by ring :
      (2 * ((a + (2 * q + 2)) + A) ^ 2 + K₁) +
          2 * ((a + (2 * q + 2)) + A) ^ 2 =
        K₁ + 4 * ((a + (2 * q + 2)) + A) ^ 2))
  have hC₂' := ((hQ.conjTranspose.mul hC₂).mul hQ).mono
    (le_of_eq (by ring :
      (2 * ((a + (2 * q + 2)) + A) ^ 2 + K₂) +
          2 * ((a + (2 * q + 2)) + A) ^ 2 =
        K₂ + 4 * ((a + (2 * q + 2)) + A) ^ 2))
  have hclean₁' := (hrouteAdj.mul hclean₁).mul hroute
  have hclean₂' := (hrouteAdj.mul hclean₂).mul hroute
  rw [conjTranspose_sitePermOp_mul_mul siteEquiv Z₁] at hclean₁'
  rw [conjTranspose_sitePermOp_mul_mul siteEquiv Z₂] at hclean₂'
  obtain ⟨Z, W, hW, hZ, hWclean, _, hcolumns, hsupport⟩ :=
    exists_encoded_uniform_merging_circuit hd hr f e he hP s hpool hpool₂
      _ _ (Qᴴ * C₁ * Q) (Qᴴ * C₂ * Q) hC₁' hC₂' hclean₁' hclean₂' V hchild hparent
  have hnew := And.intro
    (IsGateProduct.sitePermOp_mul_mul_conjTranspose (workspaceFixedSitePerm (a := A) siteEquiv) hW)
    (IsCleanImplementation.conjugate_workspaceFixedSitePerm siteEquiv hWclean)
  have hpull : ∀ Y : Matrix (Cfg d (a + (2 * q + 2))) (Cfg d (a + (2 * q + 2))) ℂ,
      Y ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) support →
      Y.submatrix (· ∘ siteEquiv.symm) (· ∘ siteEquiv.symm) ∈
        ManyBody.supportedOperators (fun _ ↦ Fin d) (support.image siteEquiv.symm) := by
    intro Y hY
    have h := ManyBody.sitePermOp_mul_mul_conjTranspose_mem_supportedOperators (α := Fin d)
      siteEquiv⁻¹ hY
    rw [ManyBody.conjTranspose_sitePermOp, inv_inv] at h
    rw [← conjTranspose_sitePermOp_mul_mul, ManyBody.conjTranspose_sitePermOp]
    simpa only [Equiv.Perm.coe_inv] using h
  have hZsupport := hsupport (support.image siteEquiv.symm) (hpull Z₁ hZ₁support)
    (hpull Z₂ hZ₂support)
    (by simpa only [Finset.coe_image] using hinputSupport)
    (by simpa only [Finset.coe_image] using hpacketSupport)
  have hreturnedSupport : R * Z * Rᴴ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) support := by
    simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply,
        Finset.image_id'] using
      ManyBody.sitePermOp_mul_mul_conjTranspose_mem_supportedOperators siteEquiv hZsupport
  have hreturnedUnitary := hnew.2.logical_mem_unitaryGroup
    (basisInclusion_isIsometry _) hnew.1.mem_unitaryGroup
  refine ⟨R * Z * Rᴴ, Q * W * Qᴴ, hreturnedUnitary, hreturnedSupport,
    hnew.1, hnew.2, ?_⟩
  have hreturnedColumns := conjugate_workspaceFixedSitePerm_columns siteEquiv W
    (basisInclusion (zeroFlagEmbedding (d := d) s))
    (encodedJoiningParent hd hr f e P V) hcolumns
  rw [sitePermOp_mul_rectangular (d := d) siteEquiv
    (basisInclusion (zeroFlagEmbedding (d := d) s)),
    sitePermOp_mul_rectangular (d := d) siteEquiv (encodedJoiningParent hd hr f e P V)]
    at hreturnedColumns
  exact hreturnedColumns

end MPUCircuit
