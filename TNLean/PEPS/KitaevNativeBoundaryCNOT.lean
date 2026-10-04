/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.KitaevNativeCheckerboardBlocking
import TNLean.PEPS.TorusRectangleBoundaryCard
import TNLean.PEPS.RegionTransport
import TNLean.Algebra.ZModSmallDifference

/-!
# Boundary CNOTs on the actual native checkerboard block

Source: SCP10, arXiv:1001.3807, the four-site blocking and boundary CNOTs,
lines 2755–2827. The eight actual crossing bonds are enumerated bijectively;
therefore the four pair CNOTs act on every native boundary configuration.
The conclusion is an equality of actual tensor maps.

**Scope restriction (one locally oriented native block):** Both periods are at
least three, and the four corner orientations are locally prescribed. This does
not assert a physical renormalization operation or a globally tiled checkerboard
state. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance kitaevBoundaryWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance kitaevBoundaryHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "TV" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
private abbrev RB (v : TV) :=
  {e : Edge Γₜ // IsRegionBoundaryEdge (torusPlaquetteRegion v) e}
private abbrev RV (v : TV) := {w : TV // w ∈ torusPlaquetteRegion v}

private theorem exists_boundary_eval (v : TV) (i : Fin 4) (second : Bool) :
    ∃ e : RB v, ∀ θ : RB v → KitaevBit,
      θ e = if second then (kitaevNativeBlockBoundary v θ i).2
        else (kitaevNativeBlockBoundary v θ i).1 := by
  unfold kitaevNativeBlockBoundary
  cases second <;> exact ⟨_,fun _ => rfl⟩

/-- The actual crossing bond in a clockwise boundary pair. Source: SCP10,
lines 2755–2794. The bond is characterized by its already derived native label read. -/
def kitaevNativeBoundaryEdge (v : TV) (i : Fin 4) (second : Bool) : RB v :=
  Classical.choose (exists_boundary_eval v i second)

private theorem edge_read (v : TV) (i : Fin 4) (second : Bool)
    (θ : RB v → KitaevBit) :
    θ (kitaevNativeBoundaryEdge v i second) =
      if second then (kitaevNativeBlockBoundary v θ i).2
        else (kitaevNativeBlockBoundary v θ i).1 :=
  Classical.choose_spec (exists_boundary_eval v i second) θ

/-- The eight enumerated bonds are the literal native right and up edges,
including both seams. Source: SCP10, boundary pairs in lines 2755–2794. -/
theorem kitaevNativeBoundaryEdge_val (v : TV) (i : Fin 4) (second : Bool) :
    (kitaevNativeBoundaryEdge v i second).val =
      ![torusUpEdge (v.1 + (if second then 1 else 0),v.2 + 1),
        torusRightEdge (v.1 + 1,v.2 + (if second then 0 else 1)),
        torusUpEdge (v.1 + (if second then 0 else 1),v.2 - 1),
        torusRightEdge (v.1 - 1,v.2 + (if second then 1 else 0))] i := by
  let e := ![torusUpEdge (v.1 + (if second then 1 else 0),v.2 + 1),
    torusRightEdge (v.1 + 1,v.2 + (if second then 0 else 1)),
    torusUpEdge (v.1 + (if second then 0 else 1),v.2 - 1),
    torusRightEdge (v.1 - 1,v.2 + (if second then 1 else 0))] i
  have h := edge_read v i second (fun b => if b.val = e then 1 else 0)
  cases second <;>
    change (if (kitaevNativeBoundaryEdge v i _).val = e then (1 : KitaevBit) else 0) =
      (if e = e then 1 else 0) at h <;>
    simp only [ite_true] at h <;>
    split_ifs at h with he
  · exact he
  · exact (zero_ne_one h).elim
  · exact he
  · exact (zero_ne_one h).elim

private theorem edge_injective (v : TV) :
    Function.Injective (fun p : Fin 4 × Bool => kitaevNativeBoundaryEdge v p.1 p.2) := by
  rcases v with ⟨x,y⟩
  have hne {n : ℕ} [Fact (2 < n)] (z : ZMod n) : z - 1 ≠ z + 1 := by
    rw [sub_eq_add_neg,ne_eq,add_left_cancel_iff]
    have hd : ((1 : ℤ) - (-1)).natAbs < n := by norm_num; exact Fact.out
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (-1) 1 hd).not
  have hx := hne x
  have hy := hne y
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  have he := congrArg Subtype.val h
  simp only [kitaevNativeBoundaryEdge_val] at he
  fin_cases i <;> fin_cases j <;> cases b <;> cases c <;>
    simp_all [torusRightEdge_injective.eq_iff,torusUpEdge_injective.eq_iff,
      Ne.symm hx,Ne.symm hy,torusRightEdge_ne_torusUpEdge,
      Ne.symm (torusRightEdge_ne_torusUpEdge _ _)]

private theorem val_lt_two_iff {n : ℕ} [NeZero n] [Fact (2 < n)] (z : ZMod n) :
    z.val < 2 ↔ z = 0 ∨ z = 1 := by
  have h₀ : (0 : ZMod n).val = 0 := ZMod.val_zero
  have h₁ : (1 : ZMod n).val = 1 := by
    simpa using (ZMod.val_cast_of_lt (n := n) (a := 1)
      (by have := Fact.out (p := 2 < n); omega))
  constructor
  · intro h
    have hz : z.val = 0 ∨ z.val = 1 := by omega
    exact hz.imp (fun h => ZMod.val_injective n (h.trans h₀.symm))
      (fun h => ZMod.val_injective n (h.trans h₁.symm))
  · rintro (rfl | rfl) <;> omega

private theorem origin_region :
    torusPlaquetteRegion ((0,0) : TV) = torusContiguousRectangle 0 0 2 2 := by
  ext w
  rcases w with ⟨x,y⟩
  have hx : x.val ≤ 1 ↔ x = 0 ∨ x = 1 := by
    simpa only [Nat.lt_succ_iff] using val_lt_two_iff x
  have hy : y.val ≤ 1 ↔ y = 0 ∨ y = 1 := by
    simpa only [Nat.lt_succ_iff] using val_lt_two_iff y
  simp [torusPlaquetteRegion,torusPlaquetteWalk,SimpleGraph.Walk.support,
    mem_torusContiguousRectangle,Prod.mk.injEq]
  tauto

private theorem translated_region (v : TV) :
    Region.map (translate v.1 v.2) (torusPlaquetteRegion ((0,0) : TV)) =
      torusPlaquetteRegion v := by
  rcases v with ⟨x,y⟩
  simp [Region.map,torusPlaquetteRegion,torusPlaquetteWalk,SimpleGraph.Walk.support,
    Finset.map_insert,translate_apply,add_comm]

private theorem boundary_card (v : TV) : Fintype.card (RB v) = 8 := by
  have hc : Fintype.card (RB ((0,0) : TV)) = 8 := by
    change Fintype.card {e : Edge Γₜ // IsRegionBoundaryEdge
      (torusPlaquetteRegion ((0,0) : TV)) e} = 8
    rw [origin_region]
    exact card_regionBoundaryEdge_torusRectangle 0 0 2 2 (by omega) (by omega)
      (by have := Fact.out (p := 2 < width); omega)
      (by have := Fact.out (p := 2 < height); omega) Fact.out Fact.out
  rw [show Fintype.card (RB v) = Fintype.card (RB ((0,0) : TV)) from ?_]
  · exact hc
  · change Fintype.card {e : Edge Γₜ // IsRegionBoundaryEdge (torusPlaquetteRegion v) e} = _
    rw [← translated_region v]
    exact Fintype.card_congr (regionBoundaryEdgeMapEquiv
      (translate v.1 v.2) (torusPlaquetteRegion ((0,0) : TV)))

/-- The four pairs enumerate every actual crossing bond once. Source: SCP10,
lines 2755–2794. Both periods are at least three, including seam-crossing blocks. -/
def kitaevNativeBoundaryEdgeEquiv (v : TV) : Fin 4 × Bool ≃ RB v :=
  Equiv.ofBijective (fun p => kitaevNativeBoundaryEdge v p.1 p.2) <|
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨edge_injective v,by simp [boundary_card]⟩

/-- Every native boundary assignment is equivalent to four ordered binary pairs.
Source: SCP10, boundary registers of the block, lines 2755–2794. -/
def kitaevNativeBoundaryEquiv (v : TV) : (RB v → KitaevBit) ≃ KitaevBlockBoundary :=
  ((kitaevNativeBoundaryEdgeEquiv v).symm.arrowCongr (Equiv.refl KitaevBit)).trans
    ((Equiv.curry (Fin 4) Bool KitaevBit).trans
      (Equiv.piCongrRight fun _ => Equiv.boolArrowEquivProd KitaevBit))

/-- The boundary equivalence reads exactly the previously derived native pairs.
Source: SCP10, clockwise boundary labels in lines 2755–2794. -/
theorem kitaevNativeBoundaryEquiv_apply (v : TV) (θ : RB v → KitaevBit) :
    kitaevNativeBoundaryEquiv v θ = kitaevNativeBlockBoundary v θ := by
  funext i
  apply Prod.ext
  · change θ (kitaevNativeBoundaryEdge v i false) = _
    exact edge_read v i false θ
  · change θ (kitaevNativeBoundaryEdge v i true) = _
    exact edge_read v i true θ

/-- The actual native boundary CNOT, transported through the derived bijection.
Source: SCP10, boundary CNOTs in lines 2760–2794. -/
def kitaevNativeBoundaryCNOT (v : TV) : Equiv.Perm (RB v → KitaevBit) :=
  ((kitaevNativeBoundaryEquiv v).trans kitaevBoundaryCNOT).trans
    (kitaevNativeBoundaryEquiv v).symm

/-- Reading the native CNOT output gives the four actual pair CNOTs.
Source: SCP10, lines 2760–2794. -/
theorem kitaevNativeBoundaryCNOT_pairs (v : TV) (θ : RB v → KitaevBit) :
    kitaevNativeBoundaryEquiv v (kitaevNativeBoundaryCNOT v θ) =
      kitaevBoundaryCNOT (kitaevNativeBoundaryEquiv v θ) := by
  simp [kitaevNativeBoundaryCNOT]

/-- The native boundary-register permutation matrix is unitary on the full
boundary space. Source: SCP10, boundary CNOTs in lines 2760–2794. -/
theorem kitaevNativeBoundaryCNOT_permMatrix_mem_unitaryGroup (v : TV) :
    (kitaevNativeBoundaryCNOT v).permMatrix ℂ ∈
      Matrix.unitaryGroup (RB v → KitaevBit) ℂ :=
  (kitaevNativeBoundaryCNOT v).permMatrix_mem_unitaryGroup

/-- The actual native open coefficient as a tensor map from boundary registers
into the four original physical spins. Source: SCP10, lines 2755–2794. -/
def kitaevNativeCheckerboardMatrix (v : TV) :
    Matrix (RV v → KitaevBit) (RB v → KitaevBit) ℂ :=
  fun σ θ => graphOpenRegionNetwork (kitaevNativeCheckerboardSite v)
    (torusPlaquetteRegion v) θ σ

/-- The color-difference tensor with the original native physical rows.
Source: SCP10, `eq:ex:kitaev-colordiff-rep`, lines 2809–2827. -/
def kitaevNativeColorMatrix (v : TV) :
    Matrix (RV v → KitaevBit) (Fin 4 → KitaevBit) ℂ :=
  fun σ p => kitaevBlockColorMatrix (fun i => σ (kitaevNativeBlockVertexEquiv v i)) p

/-- Include the four colors into the native boundary space by setting the other
four transformed registers to zero. Source: SCP10, lines 2760–2794. -/
def kitaevNativeBoundaryZeroEmbedding (v : TV) : (Fin 4 → KitaevBit) ↪ (RB v → KitaevBit) :=
  { toFun := fun p => (kitaevNativeBoundaryEquiv v).symm (kitaevBoundaryZeroEmbedding p)
    inj' := (kitaevNativeBoundaryEquiv v).symm.injective.comp
      kitaevBoundaryZeroEmbedding.injective }

/-- Adding the four zero registers is an isometry into the full native boundary
space. Source: SCP10, lines 2760–2794. -/
theorem kitaevNativeBoundaryZeroEmbedding_isIsometry (v : TV) :
    Matrix.IsIsometry (endpointEmbeddingMatrix (kitaevNativeBoundaryZeroEmbedding v)) :=
  endpointEmbeddingMatrix_isIsometry (kitaevNativeBoundaryZeroEmbedding v)

private theorem native_permutation_matrix (v : TV) :
    (kitaevNativeBoundaryCNOT v).permMatrix ℂ =
      (kitaevBoundaryCNOT.permMatrix ℂ).submatrix
        (kitaevNativeBoundaryEquiv v) (kitaevNativeBoundaryEquiv v) := by
  ext θ ζ
  simp [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
    kitaevNativeBoundaryCNOT,Equiv.symm_apply_eq]

private theorem native_zero_matrix (v : TV) :
    endpointEmbeddingMatrix (kitaevNativeBoundaryZeroEmbedding v) =
      (endpointEmbeddingMatrix kitaevBoundaryZeroEmbedding).submatrix
        (kitaevNativeBoundaryEquiv v) id := by
  ext θ p
  simp [endpointEmbeddingMatrix,kitaevNativeBoundaryZeroEmbedding,Equiv.eq_symm_apply]

/-- After the native boundary unitary, the actual four-site tensor map is the
color-difference tensor followed by projection onto the four zero registers.
Source: SCP10, lines 2760–2827. This is a native open tensor-map identity, not a
physical renormalization operation or a globally tiled checkerboard equality. -/
theorem kitaevNativeCheckerboardMatrix_mul_boundaryCNOT (v : TV) :
    kitaevNativeCheckerboardMatrix v * (kitaevNativeBoundaryCNOT v).permMatrix ℂ =
      kitaevNativeColorMatrix v *
        (endpointEmbeddingMatrix (kitaevNativeBoundaryZeroEmbedding v))ᴴ := by
  let r : (RV v → KitaevBit) → KitaevBlockSpins :=
    fun σ i => σ (kitaevNativeBlockVertexEquiv v i)
  have hM : kitaevNativeCheckerboardMatrix v =
      kitaevCheckerboardBlockMatrix.submatrix r (kitaevNativeBoundaryEquiv v) := by
    ext σ θ
    simpa only [kitaevNativeCheckerboardMatrix,kitaevCheckerboardBlockMatrix,
      Matrix.submatrix_apply,kitaevNativeBoundaryEquiv_apply] using
      graphOpenRegionNetwork_kitaevNativeCheckerboardSite v θ σ
  rw [hM,native_permutation_matrix,Matrix.submatrix_mul_equiv,
    kitaevCheckerboardBlockMatrix_mul_boundaryCNOT,native_zero_matrix,
    Matrix.conjTranspose_submatrix]
  change _ = kitaevBlockColorMatrix.submatrix r id *
    (endpointEmbeddingMatrix kitaevBoundaryZeroEmbedding)ᴴ.submatrix id
      (kitaevNativeBoundaryEquiv v)
  exact (Matrix.submatrix_mul_equiv kitaevBlockColorMatrix
    (endpointEmbeddingMatrix kitaevBoundaryZeroEmbedding)ᴴ r
      (Equiv.refl _) (kitaevNativeBoundaryEquiv v)).symm

end TNLean.PEPS
