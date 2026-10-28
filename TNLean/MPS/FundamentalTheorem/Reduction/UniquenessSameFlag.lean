/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.NormalCommutant
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessFlag

/-!
# Two multi-block reductions with the same flag

Let `(σ, g)` and `(σ, g_tilde)` be two multi-block reductions of a tensor `B` onto the same family
of normal blocks `C s`, `s ∈ S`, with the same slots and order `σ` and the same flag,
`g_tilde⁻¹ E_k = g⁻¹ E_k` for every leading coordinate subspace `E_k`. The coordinate change
`h = g_tilde g⁻¹` maps every `E_k` onto itself, so it is block upper triangular for the order `σ`,
and its diagonal block `h_{bb}` intertwines the diagonal block of the slot `b` with itself, so it is
a nonzero scalar `λ_b` by Schur's lemma. Reading the rows of `g_tilde = h g` and the columns of
`g_tilde⁻¹ = g⁻¹ h⁻¹` gives $$\widetilde W_b = \lambda_b W_b + \sum_{c \text{ after } b} h_{bc} W_c,
\qquad \widetilde V_b = \lambda_b^{-1} V_b + \sum_{c \text{ before } b} V_c (h^{-1})_{cb}.$$
Conversely every block upper triangular `h` with nonzero scalar diagonal blocks turns `(σ, g)` into
a reduction `(σ, h g)` with the same flag. Together the two directions say that the group `T_σ` of
such matrices acts freely and transitively by `g ↦ h g` on the reductions with a given labelled flag
(`MPSTensor.MultiBlockCompression.withGauge_eq_conjTriangular` and
`MPSTensor.MultiBlockCompression.coordChange_conjTriangularGauge`); the bijection
`MPSTensor.MultiBlockCompression.bijOn_conjTriangular` records the torsor.

This is *Two compressions with the same flag* (blueprint `thm:asym_uniq_same_flag`). The blocks are
assumed normal, as in the existence theorem, and of positive bond dimension; the proof uses only
Schur's lemma, which holds for irreducible blocks.

**Formulation of "the same slots, order and flag".** A multi-block compression carries its number of
zero slots `z` and its order `ord` as fields. A second reduction with `σ_tilde = σ` is therefore
written `P.withGauge g htri hdiag`: the compression with the fields `z` and `ord` of `P` and the
change of coordinates `g`, in which every letter is block upper triangular for the order of `P` with
the prescribed diagonal blocks. Every compression whose `z` equals that of `P` and whose order is
that of `P` is of this form (`MPSTensor.MultiBlockCompression.exists_eq_withGauge`). The equality of
flags is the hypothesis `∀ k, (P.withGauge g htri hdiag).flag k = P.flag k`, equivalently
`g⁻¹ E_k = g_P⁻¹ E_k` (`MPSTensor.MultiBlockCompression.flag_withGauge_eq_iff`).

## Main definitions

* `MPSTensor.coordChange`: the coordinate change `h = g₂ g₁⁻¹` between two block coordinate systems
  of the bond space.
* `MPSTensor.MultiBlockCompression.withGauge`: the compression with the slots and order of `P` and a
  second change of coordinates.
* `MPSTensor.MultiBlockCompression.coordChangeScalar`: the scalar `λ_b` of the diagonal block of the
  coordinate change at the slot `b`.
* `MPSTensor.MultiBlockCompression.conjTriangular`: the compression `(σ, h g)` for a block upper
  triangular `h` with nonzero scalar diagonal blocks.

## Main statements

* `MPSTensor.MultiBlockCompression.blockTriangular_coordChange`: with the same flag, the coordinate
  change is block upper triangular.
* `MPSTensor.MultiBlockCompression.blockDiag'_coordChange_intertwines`,
  `MPSTensor.MultiBlockCompression.blockDiag'_coordChange_eq_smul`,
  `MPSTensor.MultiBlockCompression.coordChangeScalar_ne_zero`: its diagonal blocks intertwine the
  diagonal blocks of the slots with themselves, and are nonzero scalars.
* `MPSTensor.MultiBlockCompression.leftRow_withGauge`,
  `MPSTensor.MultiBlockCompression.rightCol_withGauge`: the displayed formulas of *Two compressions
  with the same flag* (blueprint `thm:asym_uniq_same_flag`) for the reading maps and injections.
* `MPSTensor.MultiBlockCompression.conjTriangular_flag`: the converse, the reduction `(σ, h g)` has
  the flag of `(σ, g)`.
* `MPSTensor.MultiBlockCompression.bijOn_conjTriangular`: the torsor, `(h, μ) ↦ (σ, h g)` is a
  bijection from `T_σ` onto the reductions with the order and flag of `(σ, g)`.

## References

Blueprint chapter *The Multi-Block Asymmetric Fundamental Theorem* (`ch:asymmetric_ft`):
`thm:asym_uniq_same_flag`, *Two compressions with the same flag*, and `thm:asym_uniq_torsor`, *The
compressions with one labelled flag form a torsor*.
-/

open scoped Matrix

namespace Matrix

variable {o : Type*} [Fintype o] [DecidableEq o] {n : o → ℕ}

/-- The rows of `blockProj n k * X` are the rows of `X` at the coordinates of the block `k`. -/
theorem blockProj_mul_apply {m : Type*} (X : Matrix (Σ k, Fin (n k)) m ℂ) (k : o)
    (i : Fin (n k)) (y : m) : (blockProj n k * X) i y = X ⟨k, i⟩ y := by
  simp only [Matrix.mul_apply, blockProj, Matrix.transpose_apply]
  rw [Finset.sum_eq_single ⟨k, i⟩]
  · rw [blockEmbed_apply_fst_eq]
    simp
  · intro x _ hx
    rw [blockEmbed_apply_of_ne hx, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The columns of `X * blockEmbed n k` are the columns of `X` at the coordinates of the block
`k`. -/
theorem mul_blockEmbed_apply {m : Type*} (X : Matrix m (Σ k, Fin (n k)) ℂ) (k : o) (x : m)
    (j : Fin (n k)) : (X * blockEmbed n k) x j = X x ⟨k, j⟩ := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single ⟨k, j⟩]
  · rw [blockEmbed_apply_fst_eq]
    simp
  · intro y _ hy
    rw [blockEmbed_apply_of_ne hy, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The rows of `X` at the block `k`, expanded over the blocks of its columns. -/
theorem blockProj_mul_eq_sum_submatrix_mul_blockProj
    (X : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ) (k : o) :
    blockProj n k * X = ∑ l, X.submatrix (Sigma.mk k) (Sigma.mk l) * blockProj n l := by
  ext i ⟨l, j⟩
  rw [blockProj_mul_apply, Matrix.sum_apply, Finset.sum_eq_single l]
  · simp [Matrix.mul_apply, blockProj, Matrix.transpose_apply, blockEmbed_apply_fst_eq]
  · intro l' _ hl'
    simp only [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun j' _ => by
      have h0 : blockProj n l' j' ⟨l, j⟩ = 0 := by
        simp only [blockProj, Matrix.transpose_apply]
        exact blockEmbed_apply_of_fst_ne (Ne.symm hl') j'
      rw [h0, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The columns of `X` at the block `k`, expanded over the blocks of its rows. -/
theorem mul_blockEmbed_eq_sum_blockEmbed_mul_submatrix
    (X : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ) (k : o) :
    X * blockEmbed n k = ∑ l, blockEmbed n l * X.submatrix (Sigma.mk l) (Sigma.mk k) := by
  ext ⟨l, i⟩ j
  rw [mul_blockEmbed_apply, Matrix.sum_apply, Finset.sum_eq_single l]
  · simp [Matrix.mul_apply, blockEmbed_apply_fst_eq]
  · intro l' _ hl'
    simp only [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun j' _ => by
      rw [blockEmbed_apply_of_fst_ne (x := ⟨l, i⟩) (Ne.symm hl') j', zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A square matrix that is a scalar multiple of the identity is the multiple by its normalized
trace. -/
theorem eq_trace_smul_one_of_exists_eq_smul_one {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ}
    (h : ∃ c : ℂ, M = c • 1) : M = ((m : ℂ)⁻¹ * M.trace) • 1 := by
  obtain ⟨c, rfl⟩ := h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · ext i
    exact i.elim0
  · have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    congr 1
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    field_simp

end Matrix

namespace MPSTensor

variable {d DB : ℕ} {ι : Type*} {D : ι → ℕ} [DecidableEq ι] {S : Finset ι} {z : ℕ}

omit [DecidableEq ι] in
/-- Every slot has positive size when every block has positive bond dimension. -/
theorem slotSize_pos (hD : ∀ s ∈ S, 0 < D s) (b : BlockIndex S z) : 0 < slotSize D b := by
  rcases b with s | t
  · exact hD s.1 s.2
  · exact Nat.one_pos

/-! ### The coordinate change between two block coordinate systems -/

section CoordChange

variable (g₁ g₂ : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S z → ℂ))

/-- The coordinate change `h = g₂ g₁⁻¹` between two block coordinate systems `g₁` and `g₂` of the
bond space (blueprint `thm:asym_uniq_same_flag`, *Two compressions with the same flag*,
`h = g_tilde g⁻¹`). -/
noncomputable def coordChange : Matrix (BlockSpace D S z) (BlockSpace D S z) ℂ :=
  gaugeMatrix g₂ * gaugeMatrixInv g₁

theorem coordChange_mulVec (u : BlockSpace D S z → ℂ) :
    coordChange g₁ g₂ *ᵥ u = g₂ (g₁.symm u) := by
  rw [coordChange, ← Matrix.mulVec_mulVec, gaugeMatrix, gaugeMatrixInv,
    LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  rfl

theorem coordChange_mul_coordChange : coordChange g₂ g₁ * coordChange g₁ g₂ = 1 := by
  rw [coordChange, coordChange, Matrix.mul_assoc, ← Matrix.mul_assoc (gaugeMatrixInv g₂),
    gaugeMatrixInv_mul_gaugeMatrix, Matrix.one_mul, gaugeMatrix_mul_gaugeMatrixInv]

/-- The inverse of the coordinate change is the coordinate change in the other direction. -/
theorem coordChange_inv : (coordChange g₁ g₂)⁻¹ = coordChange g₂ g₁ :=
  Matrix.inv_eq_left_inv (coordChange_mul_coordChange g₁ g₂)

/-- `g₂ = h g₁` as matrices. -/
theorem gaugeMatrix_eq_coordChange_mul :
    gaugeMatrix g₂ = coordChange g₁ g₂ * gaugeMatrix g₁ := by
  rw [coordChange, Matrix.mul_assoc, gaugeMatrixInv_mul_gaugeMatrix, Matrix.mul_one]

/-- `g₂⁻¹ = g₁⁻¹ h⁻¹` as matrices. -/
theorem gaugeMatrixInv_eq_mul_coordChange :
    gaugeMatrixInv g₂ = gaugeMatrixInv g₁ * coordChange g₂ g₁ := by
  rw [coordChange, ← Matrix.mul_assoc, gaugeMatrixInv_mul_gaugeMatrix, Matrix.one_mul]

/-- The coordinate change intertwines the matrices of a bond-space operator in the two
coordinate systems. -/
theorem coordChange_mul_conjMatrix (A : Matrix (Fin DB) (Fin DB) ℂ) :
    coordChange g₁ g₂ * conjMatrix g₁ A = conjMatrix g₂ A * coordChange g₁ g₂ := by
  simp only [coordChange, conjMatrix_eq_gaugeMatrix_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (gaugeMatrixInv g₁) (gaugeMatrix g₁), gaugeMatrixInv_mul_gaugeMatrix,
    Matrix.one_mul, ← Matrix.mul_assoc (gaugeMatrixInv g₂) (gaugeMatrix g₂),
    gaugeMatrixInv_mul_gaugeMatrix, Matrix.one_mul]

end CoordChange

namespace MultiBlockCompression

variable {B : MPSTensor d DB} {C : ∀ s, MPSTensor d (D s)} (P : MultiBlockCompression B S C)

/-! ### Leading spaces and block triangularity -/

/-- A block upper triangular matrix for the order of `P` preserves the leading coordinate
subspaces. -/
theorem mulVec_mem_leadingSpace_of_blockTriangular
    {X : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
    (hX : X.BlockTriangular fun x => P.ord x.1) {k : Fin (S.card + P.z + 1)}
    {u : BlockSpace D S P.z → ℂ} (hu : u ∈ P.leadingSpace k) : X *ᵥ u ∈ P.leadingSpace k := by
  rw [mem_leadingSpace] at hu ⊢
  intro y hy
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun y' _ => ?_
  by_cases hlt : P.ord y'.1 < P.ord y.1
  · rw [hX hlt, zero_mul]
  · rw [hu y' (le_trans hy (Fin.castSucc_le_castSucc_iff.2 (not_lt.1 hlt))), mul_zero]

/-- A matrix preserving every leading coordinate subspace is block upper triangular for the
order of `P`. -/
theorem blockTriangular_of_forall_mulVec_mem_leadingSpace
    {X : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
    (hX : ∀ k, ∀ u ∈ P.leadingSpace k, X *ᵥ u ∈ P.leadingSpace k) :
    X.BlockTriangular fun x => P.ord x.1 := by
  intro x y hlt
  have hu : (Pi.single y (1 : ℂ) : BlockSpace D S P.z → ℂ) ∈ P.leadingSpace (P.ord y.1).succ := by
    rw [mem_leadingSpace]
    intro y' hy'
    have hne : y' ≠ y := by
      rintro rfl
      exact absurd hy' (not_le.2 Fin.castSucc_lt_succ)
    simp [hne]
  have h := P.mem_leadingSpace.1 (hX _ _ hu) x (Fin.succ_le_castSucc_iff.2 hlt)
  simpa [Matrix.mulVec_single_one] using h

/-- **The coordinate change of two reductions with the same flag is block upper triangular**
(blueprint `thm:asym_uniq_same_flag`, *Two compressions with the same flag*, first step of the
proof). If two block coordinate systems `g₁`, `g₂` have the same preimages of the leading coordinate
subspaces, `g₁⁻¹ E_k = g₂⁻¹ E_k`, then `h = g₂ g₁⁻¹` maps every `E_k` into itself and is block upper
triangular for the order of `P`. -/
theorem blockTriangular_coordChange {g₁ g₂ : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ)}
    (hflag : ∀ k, (P.leadingSpace k).comap (g₁ : (Fin DB → ℂ) →ₗ[ℂ] (BlockSpace D S P.z → ℂ)) =
      (P.leadingSpace k).comap (g₂ : (Fin DB → ℂ) →ₗ[ℂ] (BlockSpace D S P.z → ℂ))) :
    (coordChange g₁ g₂).BlockTriangular fun x => P.ord x.1 := by
  refine P.blockTriangular_of_forall_mulVec_mem_leadingSpace fun k u hu => ?_
  rw [coordChange_mulVec]
  have hmem : g₁.symm u ∈ (P.leadingSpace k).comap
      (g₁ : (Fin DB → ℂ) →ₗ[ℂ] (BlockSpace D S P.z → ℂ)) := by
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact hu
  rw [hflag k, Submodule.mem_comap, LinearEquiv.coe_coe] at hmem
  exact hmem

/-! ### A second reduction with the same slots and order -/

/-- **A second reduction with the slots and order of `P`** (blueprint `thm:asym_uniq_same_flag`,
*Two compressions with the same flag*, the reduction `(σ_tilde, g_tilde)` with `σ_tilde = σ`): the
compression with the number of zero slots and the order of `P` and the change of coordinates `g`, in
which every letter is block upper triangular for the order of `P` with the prescribed diagonal
blocks. -/
def withGauge (g : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ))
    (htri : ∀ i, (conjMatrix g (B i)).BlockTriangular fun x => P.ord x.1)
    (hdiag : ∀ i b, (conjMatrix g (B i)).blockDiag' b = blockOf D C i b) :
    MultiBlockCompression B S C where
  z := P.z
  ord := P.ord
  gauge := g
  triangular := htri
  matched i s := hdiag i (Sum.inl s)
  unmatched i t := hdiag i (Sum.inr t)

/-- Every compression with the number of zero slots and the order of `P` is `P.withGauge` of its
own change of coordinates. -/
theorem exists_eq_withGauge {Q : MultiBlockCompression B S C} (hz : Q.z = P.z)
    (hord : HEq Q.ord P.ord) :
    ∃ (g : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ))
      (htri : ∀ i, (conjMatrix g (B i)).BlockTriangular fun x => P.ord x.1)
      (hdiag : ∀ i b, (conjMatrix g (B i)).blockDiag' b = blockOf D C i b),
      Q = P.withGauge g htri hdiag := by
  obtain ⟨z, ord, gauge, tri, mat, unm⟩ := Q
  change z = P.z at hz
  subst hz
  obtain rfl := eq_of_heq hord
  refine ⟨gauge, tri, fun i b => ?_, rfl⟩
  rcases b with s | t
  · exact mat i s
  · exact unm i t

theorem withGauge_congr {g g' : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ)}
    {htri : ∀ i, (conjMatrix g (B i)).BlockTriangular fun x => P.ord x.1}
    {hdiag : ∀ i b, (conjMatrix g (B i)).blockDiag' b = blockOf D C i b}
    {htri' : ∀ i, (conjMatrix g' (B i)).BlockTriangular fun x => P.ord x.1}
    {hdiag' : ∀ i b, (conjMatrix g' (B i)).blockDiag' b = blockOf D C i b} (h : g = g') :
    P.withGauge g htri hdiag = P.withGauge g' htri' hdiag' := by
  subst h
  rfl

theorem mem_flag_iff_toVec_mem_comap {k : Fin (S.card + P.z + 1)} {x : B.WordModule} :
    x ∈ P.flag k ↔ WordModule.toVec B x ∈
      (P.leadingSpace k).comap (P.gauge : (Fin DB → ℂ) →ₗ[ℂ] (BlockSpace D S P.z → ℂ)) :=
  Iff.rfl

/-- Two reductions with the same slots and order have the same flag exactly when their changes of
coordinates have the same preimages of the leading coordinate subspaces, `g_tilde⁻¹ E_k = g⁻¹ E_k`
(blueprint `thm:asym_uniq_same_flag`, *Two compressions with the same flag*, hypothesis).
-/
theorem flag_withGauge_eq_iff (g : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ))
    (htri : ∀ i, (conjMatrix g (B i)).BlockTriangular fun x => P.ord x.1)
    (hdiag : ∀ i b, (conjMatrix g (B i)).blockDiag' b = blockOf D C i b)
    (k : Fin (S.card + P.z + 1)) :
    (P.withGauge g htri hdiag).flag k = P.flag k ↔
      (P.leadingSpace k).comap (g : (Fin DB → ℂ) →ₗ[ℂ] (BlockSpace D S P.z → ℂ)) =
        (P.leadingSpace k).comap (P.gauge : (Fin DB → ℂ) →ₗ[ℂ] (BlockSpace D S P.z → ℂ)) := by
  constructor
  · intro h
    ext v
    have hv := SetLike.ext_iff.1 h ((WordModule.toVec B).symm v)
    change g (WordModule.toVec B ((WordModule.toVec B).symm v)) ∈ P.leadingSpace k ↔
      P.gauge (WordModule.toVec B ((WordModule.toVec B).symm v)) ∈ P.leadingSpace k at hv
    rw [LinearEquiv.apply_symm_apply] at hv
    exact hv
  · intro h
    ext x
    change g (WordModule.toVec B x) ∈ P.leadingSpace k ↔
      P.gauge (WordModule.toVec B x) ∈ P.leadingSpace k
    exact SetLike.ext_iff.1 h (WordModule.toVec B x)

/-! ### The coordinate change of two reductions with the same flag -/

section SameFlag

variable {P} {g : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ)}
  {htri : ∀ i, (conjMatrix g (B i)).BlockTriangular fun x => P.ord x.1}
  {hdiag : ∀ i b, (conjMatrix g (B i)).blockDiag' b = blockOf D C i b}

/-- **The coordinate change is block upper triangular** (blueprint `thm:asym_uniq_same_flag`, *Two
compressions with the same flag*), in the direction from `P` to the second reduction. -/
theorem blockTriangular_coordChange_of_flag_eq
    (hflag : ∀ k, (P.withGauge g htri hdiag).flag k = P.flag k) :
    (coordChange P.gauge g).BlockTriangular fun x => P.ord x.1 :=
  P.blockTriangular_coordChange fun k => ((P.flag_withGauge_eq_iff g htri hdiag k).1 (hflag k)).symm

/-- **The inverse coordinate change is block upper triangular** (blueprint
`thm:asym_uniq_same_flag`, *Two compressions with the same flag*). -/
theorem blockTriangular_coordChange_symm_of_flag_eq
    (hflag : ∀ k, (P.withGauge g htri hdiag).flag k = P.flag k) :
    (coordChange g P.gauge).BlockTriangular fun x => P.ord x.1 :=
  P.blockTriangular_coordChange fun k => (P.flag_withGauge_eq_iff g htri hdiag k).1 (hflag k)

/-- **The diagonal blocks of the coordinate change intertwine** (blueprint
`thm:asym_uniq_same_flag`, *Two compressions with the same flag*, proof). The diagonal block of
`h = g_tilde g⁻¹` at a slot `b` commutes with every letter of the diagonal block of that slot,
because the diagonal block of a product of block upper triangular matrices is the product of their
diagonal blocks. -/
theorem blockDiag'_coordChange_intertwines
    (hflag : ∀ k, (P.withGauge g htri hdiag).flag k = P.flag k) (i : Fin d)
    (b : BlockIndex S P.z) :
    (coordChange P.gauge g).blockDiag' b * blockOf D C i b =
      blockOf D C i b * (coordChange P.gauge g).blockDiag' b := by
  have ht := blockTriangular_coordChange_of_flag_eq hflag
  have h := congrArg (fun M => M.blockDiag' b) (coordChange_mul_conjMatrix P.gauge g (B i))
  rwa [Matrix.blockDiag'_mul_of_blockTriangular P.ord.injective ht (P.triangular i),
    Matrix.blockDiag'_mul_of_blockTriangular P.ord.injective (htri i) ht,
    P.blockDiag'_conjMatrix, hdiag] at h

variable (P g) in
/-- **The scalar of a slot** (blueprint `thm:asym_uniq_same_flag`, *Two compressions with the same
flag*, `λ_b`): the normalized trace of the diagonal block of the coordinate change `h = g_tilde g⁻¹`
at the slot `b`. -/
noncomputable def coordChangeScalar (b : BlockIndex S P.z) : ℂ :=
  (slotSize D b : ℂ)⁻¹ * ((coordChange P.gauge g).blockDiag' b).trace

/-- **The diagonal blocks of the coordinate change are scalars** (blueprint
`thm:asym_uniq_same_flag`, *Two compressions with the same flag*): `h_{bb} = λ_b 1`, by Schur's
lemma on a block slot and because a zero slot is one-dimensional. -/
theorem blockDiag'_coordChange_eq_smul (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hflag : ∀ k, (P.withGauge g htri hdiag).flag k = P.flag k) (b : BlockIndex S P.z) :
    (coordChange P.gauge g).blockDiag' b = P.coordChangeScalar g b • 1 := by
  refine Matrix.eq_trace_smul_one_of_exists_eq_smul_one ?_
  rcases b with s | t
  · exact Kraus.IsNormal.eq_smul_one_of_commute (hC s.1 s.2) fun i =>
      blockDiag'_coordChange_intertwines hflag i (Sum.inl s)
  · refine ⟨(coordChange P.gauge g).blockDiag' (Sum.inr t) 0 0, ?_⟩
    ext i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    simp

/-- The diagonal block of the inverse coordinate change times that of the coordinate change is
the identity. -/
theorem blockDiag'_coordChange_symm_mul
    (hflag : ∀ k, (P.withGauge g htri hdiag).flag k = P.flag k) (b : BlockIndex S P.z) :
    (coordChange g P.gauge).blockDiag' b * (coordChange P.gauge g).blockDiag' b = 1 := by
  have h := congrArg (fun M => M.blockDiag' b) (coordChange_mul_coordChange P.gauge g)
  rwa [Matrix.blockDiag'_mul_of_blockTriangular P.ord.injective
    (blockTriangular_coordChange_symm_of_flag_eq hflag)
    (blockTriangular_coordChange_of_flag_eq hflag), Matrix.blockDiag'_one, Pi.one_apply] at h

/-- **The scalar of a slot is nonzero** (blueprint `thm:asym_uniq_same_flag`, *Two compressions with
the same flag*), because the coordinate change is invertible and block upper triangular. -/
theorem coordChangeScalar_ne_zero (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) (hflag : ∀ k, (P.withGauge g htri hdiag).flag k = P.flag k)
    (b : BlockIndex S P.z) : P.coordChangeScalar g b ≠ 0 := by
  intro h0
  have h := blockDiag'_coordChange_symm_mul hflag b
  rw [blockDiag'_coordChange_eq_smul hC hflag, h0, zero_smul, Matrix.mul_zero] at h
  have : Nonempty (Fin (slotSize D b)) := ⟨⟨0, slotSize_pos hD b⟩⟩
  exact zero_ne_one h

/-- The diagonal block of the inverse coordinate change at a slot is `λ_b⁻¹ 1`. -/
theorem blockDiag'_coordChange_symm_eq_smul (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) (hflag : ∀ k, (P.withGauge g htri hdiag).flag k = P.flag k)
    (b : BlockIndex S P.z) :
    (coordChange g P.gauge).blockDiag' b = (P.coordChangeScalar g b)⁻¹ • 1 := by
  have h := blockDiag'_coordChange_symm_mul hflag b
  rw [blockDiag'_coordChange_eq_smul hC hflag, Matrix.mul_smul, Matrix.mul_one] at h
  rw [← h, smul_smul, inv_mul_cancel₀ (coordChangeScalar_ne_zero hC hD hflag b), one_smul]

/-- **Two compressions with the same flag, the reading maps** (blueprint `thm:asym_uniq_same_flag`,
*Two compressions with the same flag*, displayed formulas): for two reductions with the same slots,
order and flag, $\widetilde W_b = \lambda_b W_b + \sum_{c \text{ after } b} h_{bc} W_c$, the sum
over all slots `c`, zero slots included. -/
theorem leftRow_withGauge (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hflag : ∀ k, (P.withGauge g htri hdiag).flag k = P.flag k) (b : BlockIndex S P.z) :
    (P.withGauge g htri hdiag).leftRow b = P.coordChangeScalar g b • P.leftRow b +
      ∑ c with P.ord b < P.ord c,
        (coordChange P.gauge g).submatrix (Sigma.mk b) (Sigma.mk c) * P.leftRow c := by
  have ht := blockTriangular_coordChange_of_flag_eq hflag
  have hrow : (P.withGauge g htri hdiag).leftRow b =
      ∑ c, (coordChange P.gauge g).submatrix (Sigma.mk b) (Sigma.mk c) * P.leftRow c := by
    change Matrix.blockProj (slotSize D) b * gaugeMatrix g = _
    rw [gaugeMatrix_eq_coordChange_mul P.gauge g, ← Matrix.mul_assoc,
      Matrix.blockProj_mul_eq_sum_submatrix_mul_blockProj, Matrix.sum_mul]
    simp only [Matrix.mul_assoc]
    rfl
  rw [hrow, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => P.ord b < P.ord c),
    add_comm]
  congr 1
  rw [Finset.sum_eq_single_of_mem b (by simp)]
  · rw [show (coordChange P.gauge g).submatrix (Sigma.mk b) (Sigma.mk b) =
        (coordChange P.gauge g).blockDiag' b from rfl, blockDiag'_coordChange_eq_smul hC hflag,
      Matrix.smul_mul, Matrix.one_mul]
  · intro c hc hcb
    have hlt : P.ord c < P.ord b :=
      lt_of_le_of_ne (not_lt.1 (Finset.mem_filter.1 hc).2) fun h => hcb (P.ord.injective h)
    have h0 : (coordChange P.gauge g).submatrix (Sigma.mk b) (Sigma.mk c) = 0 := by
      ext j j'
      exact ht (i := ⟨b, j⟩) (j := ⟨c, j'⟩) hlt
    rw [h0, Matrix.zero_mul]

/-- **Two compressions with the same flag, the injections** (blueprint `thm:asym_uniq_same_flag`,
*Two compressions with the same flag*, displayed formulas): for two reductions with the same slots,
order and flag,
$\widetilde V_b = \lambda_b^{-1} V_b + \sum_{c \text{ before } b} V_c (h^{-1})_{cb}$, the sum over
all slots `c`, zero slots included. -/
theorem rightCol_withGauge (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (hflag : ∀ k, (P.withGauge g htri hdiag).flag k = P.flag k) (b : BlockIndex S P.z) :
    (P.withGauge g htri hdiag).rightCol b = (P.coordChangeScalar g b)⁻¹ • P.rightCol b +
      ∑ c with P.ord c < P.ord b,
        P.rightCol c * (coordChange P.gauge g)⁻¹.submatrix (Sigma.mk c) (Sigma.mk b) := by
  have ht := blockTriangular_coordChange_symm_of_flag_eq hflag
  rw [coordChange_inv]
  have hcol : (P.withGauge g htri hdiag).rightCol b =
      ∑ c, P.rightCol c * (coordChange g P.gauge).submatrix (Sigma.mk c) (Sigma.mk b) := by
    change gaugeMatrixInv g * Matrix.blockEmbed (slotSize D) b = _
    rw [gaugeMatrixInv_eq_mul_coordChange P.gauge g, Matrix.mul_assoc,
      Matrix.mul_blockEmbed_eq_sum_blockEmbed_mul_submatrix, Matrix.mul_sum]
    simp only [← Matrix.mul_assoc]
    rfl
  rw [hcol, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => P.ord c < P.ord b),
    add_comm]
  congr 1
  rw [Finset.sum_eq_single_of_mem b (by simp)]
  · rw [show (coordChange g P.gauge).submatrix (Sigma.mk b) (Sigma.mk b) =
        (coordChange g P.gauge).blockDiag' b from rfl,
      blockDiag'_coordChange_symm_eq_smul hC hD hflag, Matrix.mul_smul, Matrix.mul_one]
  · intro c hc hcb
    have hlt : P.ord b < P.ord c :=
      lt_of_le_of_ne (not_lt.1 (Finset.mem_filter.1 hc).2) fun h => hcb (P.ord.injective h).symm
    have h0 : (coordChange g P.gauge).submatrix (Sigma.mk c) (Sigma.mk b) = 0 := by
      ext j j'
      exact ht (i := ⟨c, j⟩) (j := ⟨b, j'⟩) hlt
    rw [h0, Matrix.mul_zero]

end SameFlag

/-! ### The converse: block upper triangular changes with scalar diagonal blocks -/

section Converse

variable {h : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
  (ht : h.BlockTriangular fun x => P.ord x.1) {μ : BlockIndex S P.z → ℂ} (hμ : ∀ b, μ b ≠ 0)
  (hdiag : ∀ b, h.blockDiag' b = μ b • 1)

include ht hμ hdiag in
/-- A block upper triangular matrix with nonzero scalar diagonal blocks is invertible. -/
theorem det_ne_zero_of_blockDiag'_eq_smul : h.det ≠ 0 := by
  rw [ht.det_fintype]
  refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
  have hblock : h.toSquareBlock (fun x => P.ord x.1) k = μ (P.ord.symm k) • 1 := by
    ext ⟨⟨b₁, j₁⟩, h₁⟩ ⟨⟨b₂, j₂⟩, h₂⟩
    have e₁ : b₁ = P.ord.symm k := P.ord.eq_symm_apply.2 h₁
    have e₂ : b₂ = P.ord.symm k := P.ord.eq_symm_apply.2 h₂
    subst e₁ e₂
    have hentry := congrFun (congrFun (hdiag (P.ord.symm k)) j₁) j₂
    rw [Matrix.blockDiag'_apply] at hentry
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, hentry]
    simp [Matrix.one_apply]
  rw [hblock, Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ (hμ _)

include ht hμ hdiag in
theorem isUnit_det_of_blockDiag'_eq_smul : IsUnit h.det :=
  (P.det_ne_zero_of_blockDiag'_eq_smul ht hμ hdiag).isUnit

/-- The change of coordinates `h g` of the bond space, for a block upper triangular `h` with nonzero
scalar diagonal blocks (blueprint `thm:asym_uniq_same_flag`, *Two compressions with the same flag*,
converse). -/
noncomputable def conjTriangularGauge : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ) :=
  P.gauge.trans (h.toLinearEquiv'
    (Matrix.invertibleOfIsUnitDet h (P.isUnit_det_of_blockDiag'_eq_smul ht hμ hdiag)))

theorem gaugeMatrix_conjTriangularGauge :
    gaugeMatrix (P.conjTriangularGauge ht hμ hdiag) = h * gaugeMatrix P.gauge := by
  rw [gaugeMatrix, gaugeMatrix, conjTriangularGauge, LinearEquiv.coe_trans,
    LinearMap.toMatrix'_comp, Matrix.toLinearEquiv'_apply, LinearMap.toMatrix'_toLin']


theorem gaugeMatrixInv_conjTriangularGauge :
    gaugeMatrixInv (P.conjTriangularGauge ht hμ hdiag) = gaugeMatrixInv P.gauge * h⁻¹ := by
  let := Matrix.invertibleOfIsUnitDet h (P.isUnit_det_of_blockDiag'_eq_smul ht hμ hdiag)
  rw [gaugeMatrixInv, gaugeMatrixInv, conjTriangularGauge, LinearEquiv.trans_symm,
    LinearEquiv.coe_trans, LinearMap.toMatrix'_comp, Matrix.toLinearEquiv'_symm_apply,
    LinearMap.toMatrix'_toLin', Matrix.invOf_eq_nonsing_inv]

theorem conjMatrix_conjTriangularGauge (A : Matrix (Fin DB) (Fin DB) ℂ) :
    conjMatrix (P.conjTriangularGauge ht hμ hdiag) A = h * conjMatrix P.gauge A * h⁻¹ := by
  rw [conjMatrix_eq_gaugeMatrix_mul, conjMatrix_eq_gaugeMatrix_mul, gaugeMatrix_conjTriangularGauge,
    gaugeMatrixInv_conjTriangularGauge]
  simp only [Matrix.mul_assoc]

theorem conjTriangularGauge_apply (v : Fin DB → ℂ) :
    P.conjTriangularGauge ht hμ hdiag v = h *ᵥ P.gauge v := rfl

/-- **The coordinate change of `(σ, h g)` from `(σ, g)` is `h`**: the action `g ↦ h g` is free
(blueprint `thm:asym_uniq_same_flag`, *Two compressions with the same flag*, torsor statement). -/
theorem coordChange_conjTriangularGauge :
    coordChange P.gauge (P.conjTriangularGauge ht hμ hdiag) = h := by
  rw [coordChange, gaugeMatrix_conjTriangularGauge, Matrix.mul_assoc,
    gaugeMatrix_mul_gaugeMatrixInv, Matrix.mul_one]

include ht hμ hdiag in
theorem blockTriangular_inv_of_blockDiag'_eq_smul :
    h⁻¹.BlockTriangular fun x => P.ord x.1 := by
  let := Matrix.invertibleOfIsUnitDet h (P.isUnit_det_of_blockDiag'_eq_smul ht hμ hdiag)
  exact Matrix.blockTriangular_inv_of_blockTriangular ht

include ht hμ hdiag in
/-- The diagonal blocks of the inverse are the inverse scalars, `(h⁻¹)_{bb} = μ_b⁻¹ 1`. -/
theorem blockDiag'_inv_of_blockDiag'_eq_smul (b : BlockIndex S P.z) :
    h⁻¹.blockDiag' b = (μ b)⁻¹ • 1 := by
  have hb := congrArg (fun M => M.blockDiag' b)
    (Matrix.nonsing_inv_mul h (P.isUnit_det_of_blockDiag'_eq_smul ht hμ hdiag))
  rw [Matrix.blockDiag'_mul_of_blockTriangular P.ord.injective
    (P.blockTriangular_inv_of_blockDiag'_eq_smul ht hμ hdiag) ht, hdiag, Matrix.blockDiag'_one,
    Pi.one_apply, Matrix.mul_smul, Matrix.mul_one] at hb
  rw [← hb, smul_smul, inv_mul_cancel₀ (hμ b), one_smul]

/-- **The converse of the same-flag theorem** (blueprint `thm:asym_uniq_same_flag`, *Two
compressions with the same flag*, converse): for a block upper triangular `h` with nonzero scalar
diagonal blocks `h_{bb} = μ_b 1`, the change of coordinates `h g` gives a reduction `(σ, h g)` onto
the same family, with the same slots and order. Its diagonal blocks are
`μ_b C_hat^i_{bb} μ_b⁻¹ = C_hat^i_{bb}`. -/
noncomputable def conjTriangular : MultiBlockCompression B S C :=
  P.withGauge (P.conjTriangularGauge ht hμ hdiag)
    (fun i => by
      rw [conjMatrix_conjTriangularGauge]
      exact (ht.mul (P.triangular i)).mul (P.blockTriangular_inv_of_blockDiag'_eq_smul ht hμ hdiag))
    (fun i b => by
      rw [conjMatrix_conjTriangularGauge, Matrix.blockDiag'_mul_of_blockTriangular P.ord.injective
        (ht.mul (P.triangular i)) (P.blockTriangular_inv_of_blockDiag'_eq_smul ht hμ hdiag),
        Matrix.blockDiag'_mul_of_blockTriangular P.ord.injective ht (P.triangular i), hdiag,
        P.blockDiag'_conjMatrix, P.blockDiag'_inv_of_blockDiag'_eq_smul ht hμ hdiag,
        Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
        inv_mul_cancel₀ (hμ b), one_smul])

theorem conjTriangular_gauge :
    (P.conjTriangular ht hμ hdiag).gauge = P.conjTriangularGauge ht hμ hdiag := rfl

/-- **The reduction `(σ, h g)` has the flag of `(σ, g)`** (blueprint `thm:asym_uniq_same_flag`, *Two
compressions with the same flag*, converse): `(h g)⁻¹ E_k = g⁻¹ h⁻¹ E_k = g⁻¹ E_k`, because `h` and
`h⁻¹` are block upper triangular. -/
theorem conjTriangular_flag (k : Fin (S.card + P.z + 1)) :
    (P.conjTriangular ht hμ hdiag).flag k = P.flag k := by
  refine (P.flag_withGauge_eq_iff _ _ _ k).2 ?_
  ext v
  rw [Submodule.mem_comap, Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    conjTriangularGauge_apply]
  constructor
  · intro hv
    have hmem := P.mulVec_mem_leadingSpace_of_blockTriangular
      (P.blockTriangular_inv_of_blockDiag'_eq_smul ht hμ hdiag) hv
    rwa [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul h (P.isUnit_det_of_blockDiag'_eq_smul ht hμ hdiag),
      Matrix.one_mulVec] at hmem
  · exact P.mulVec_mem_leadingSpace_of_blockTriangular ht

/-- **The reduction `(σ, h g)` has the labelled flag of `(σ, g)`** (blueprint
`thm:asym_uniq_same_flag`, *Two compressions with the same flag*): the same flag, by
`conjTriangular_flag`, and the same order of the labels. -/
theorem toFlagData_conjTriangular : (P.conjTriangular ht hμ hdiag).toFlagData = P.toFlagData := by
  have hflag : (P.conjTriangular ht hμ hdiag).flag = P.flag :=
    funext (P.conjTriangular_flag ht hμ hdiag)
  unfold toFlagData
  congr 1

end Converse

/-! ### The torsor statement -/

section Torsor

variable {P} {g : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ)}
  {htri : ∀ i, (conjMatrix g (B i)).BlockTriangular fun x => P.ord x.1}
  {hdiag : ∀ i b, (conjMatrix g (B i)).blockDiag' b = blockOf D C i b}

/-- **Two compressions with the same flag, transitivity** (blueprint `thm:asym_uniq_same_flag`, *Two
compressions with the same flag*): a second reduction with the same slots, order and flag as `P` is
`(σ, h g)` for its coordinate change `h = g_tilde g⁻¹`, which is block upper triangular with nonzero
scalar diagonal blocks `λ_b 1`. -/
theorem withGauge_eq_conjTriangular (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (hflag : ∀ k, (P.withGauge g htri hdiag).flag k = P.flag k) :
    P.withGauge g htri hdiag = P.conjTriangular (blockTriangular_coordChange_of_flag_eq hflag)
      (coordChangeScalar_ne_zero hC hD hflag) (blockDiag'_coordChange_eq_smul hC hflag) := by
  refine P.withGauge_congr (LinearEquiv.ext fun v => ?_)
  rw [conjTriangularGauge_apply, coordChange_mulVec, LinearEquiv.symm_apply_apply]

end Torsor

/-! ### The torsor as a bijection -/

section TorsorBijection

/-- **The action `h ↦ (σ, h g)` is free** (blueprint `thm:asym_uniq_same_flag`, *Two compressions
with the same flag*): equal reductions `(σ, h g) = (σ, h' g)` have `h = h'`, since `h` is the
coordinate change from `g` to `h g`. -/
theorem eq_of_conjTriangular_eq {h h' : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
    {ht : h.BlockTriangular fun x => P.ord x.1} {μ : BlockIndex S P.z → ℂ} {hμ : ∀ b, μ b ≠ 0}
    {hdiag : ∀ b, h.blockDiag' b = μ b • 1}
    {ht' : h'.BlockTriangular fun x => P.ord x.1} {μ' : BlockIndex S P.z → ℂ}
    {hμ' : ∀ b, μ' b ≠ 0} {hdiag' : ∀ b, h'.blockDiag' b = μ' b • 1}
    (heq : P.conjTriangular ht hμ hdiag = P.conjTriangular ht' hμ' hdiag') : h = h' := by
  -- Compare the two gauges through `P.z`, so that the kernel never compares two `conjTriangular`s.
  have key : ∀ X Y : MultiBlockCompression B S C, X = Y → ∀ (hX : X.z = P.z) (hY : Y.z = P.z),
      (hX ▸ X.gauge : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ)) = hY ▸ Y.gauge := by
    rintro X _ rfl hX hY
    rfl
  have hg := key _ _ heq rfl rfl
  rw [← P.coordChange_conjTriangularGauge ht hμ hdiag,
    ← P.coordChange_conjTriangularGauge ht' hμ' hdiag']
  exact congrArg (coordChange P.gauge) hg

omit [DecidableEq ι] in
/-- The scalars of the diagonal blocks of a matrix are determined by the matrix when every slot
has positive size. -/
theorem eq_of_blockDiag'_eq_smul (hD : ∀ s ∈ S, 0 < D s)
    {h : Matrix (BlockSpace D S z) (BlockSpace D S z) ℂ} {μ μ' : BlockIndex S z → ℂ}
    (hdiag : ∀ b, h.blockDiag' b = μ b • 1) (hdiag' : ∀ b, h.blockDiag' b = μ' b • 1) :
    μ = μ' := by
  funext b
  have e := congrFun (congrFun ((hdiag b).symm.trans (hdiag' b)) ⟨0, slotSize_pos hD b⟩)
    ⟨0, slotSize_pos hD b⟩
  simpa using e

/-- **The torsor of the same-flag theorem** (blueprint `thm:asym_uniq_same_flag`, *Two compressions
with the same flag*): for a reduction `(σ, g)` onto normal blocks of positive bond dimension,
`(h, μ) ↦ (σ, h g)` is a bijection from the group `T_σ` of block upper triangular matrices with
diagonal blocks `μ_b 1`, `μ_b ≠ 0`, onto the reductions with the order and the flag of `(σ, g)`. The
scalars `μ` are recorded with `h`; they are determined by `h` because every slot has positive size.
-/
theorem bijOn_conjTriangular (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s) :
    Set.BijOn
      (fun p : {p : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ × (BlockIndex S P.z → ℂ) //
          p.1.BlockTriangular (fun x => P.ord x.1) ∧ (∀ b, p.2 b ≠ 0) ∧
            ∀ b, p.1.blockDiag' b = p.2 b • 1} =>
        P.conjTriangular p.2.1 p.2.2.1 p.2.2.2)
      Set.univ
      {Q : MultiBlockCompression B S C | ∃ hz : Q.z = P.z, HEq Q.ord P.ord ∧
          ∀ k, Q.flag (Fin.cast (by rw [hz]) k) = P.flag k} := by
  refine ⟨fun p _ => ⟨rfl, HEq.rfl, fun k => P.conjTriangular_flag _ _ _ k⟩, fun p _ q _ hpq => ?_,
    fun Q hQ => ?_⟩
  · obtain ⟨⟨h, μ⟩, ht, hμ, hdiag⟩ := p
    obtain ⟨⟨h', μ'⟩, ht', hμ', hdiag'⟩ := q
    obtain rfl : h = h' := P.eq_of_conjTriangular_eq hpq
    obtain rfl : μ = μ' := eq_of_blockDiag'_eq_smul hD hdiag hdiag'
    rfl
  · obtain ⟨hz, hord, hflag⟩ := hQ
    obtain ⟨g, htri, hdiag, rfl⟩ := P.exists_eq_withGauge hz hord
    have hflag' : ∀ k, (P.withGauge g htri hdiag).flag k = P.flag k := fun k => hflag k
    exact ⟨⟨(coordChange P.gauge g, P.coordChangeScalar g),
      blockTriangular_coordChange_of_flag_eq hflag', coordChangeScalar_ne_zero hC hD hflag',
      blockDiag'_coordChange_eq_smul hC hflag'⟩, trivial,
    (withGauge_eq_conjTriangular hC hD hflag').symm⟩

end TorsorBijection

end MultiBlockCompression

end MPSTensor
