/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRectangleConnectivity
import TNLean.PEPS.TorusRegionRealization
import Mathlib.Analysis.Convex.Contractible

/-!
# Simply connected rectangular cell regions

A nonwrapping rectangle of native torus sites has a closed-cell realization
homeomorphic to the corresponding closed planar rectangle, provided that each
side length is strictly smaller than its torus period. Convexity then gives
simple connectedness of the actual realization.

This is auxiliary geometry for the reduction to horizontal and vertical stripes
in SCP10, Theorem 6.7 (arXiv:1001.3807, local source lines 1995–2011). It asserts
neither a physical disentangling identity nor a parent-Hamiltonian statement.
-/

open Set
noncomputable section
namespace TNLean.PEPS

private theorem exists_integer_center_in_interval (a b : ℤ) (hab : a ≤ b) (x : ℝ)
    (hx : (a : ℝ) - 1 / 2 ≤ x ∧ x ≤ (b : ℝ) + 1 / 2) :
    ∃ i : ℤ, a ≤ i ∧ i ≤ b ∧ |x - (i : ℝ)| ≤ 1 / 2 := by
  let i : ℤ := min ⌊x + 1 / 2⌋ b
  have haf : a ≤ ⌊x + 1 / 2⌋ := Int.le_floor.mpr (by linarith [hx.1])
  have hai : a ≤ i := le_min haf hab
  have hib : i ≤ b := min_le_right _ _
  have hf : (⌊x + 1 / 2⌋ : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have hf' : x + 1 / 2 < (⌊x + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  refine ⟨i, hai, hib, ?_⟩
  dsimp [i]
  rw [Int.cast_min, abs_le]
  constructor
  · have hm : min (⌊x + 1 / 2⌋ : ℝ) (b : ℝ) ≤ (⌊x + 1 / 2⌋ : ℝ) := min_le_left _ _
    linarith
  · rcases le_total ⌊x + 1 / 2⌋ b with h | h
    · rw [min_eq_left (by exact_mod_cast h)]
      linarith
    · rw [min_eq_right (by exact_mod_cast h)]
      linarith [hx.2]

private def planarRectangle (xStart yStart xLen yLen : ℕ) : Set (ℝ × ℝ) :=
  Icc ((xStart : ℝ) - 1 / 2) ((xStart + xLen : ℕ) - 1 / 2 : ℝ) ×ˢ
    Icc ((yStart : ℝ) - 1 / 2) ((yStart + yLen : ℕ) - 1 / 2 : ℝ)

private theorem projection_planarRectangle_eq
    {width height : ℕ} [NeZero width] [NeZero height]
    (xStart yStart xLen yLen : ℕ) (hx : 0 < xLen) (hy : 0 < yLen)
    (hxb : xStart + xLen ≤ width) (hyb : yStart + yLen ≤ height) :
    torusRealProjection width height '' planarRectangle xStart yStart xLen yLen =
      torusRegionRealization
        (torusContiguousRectangle (width := width) (height := height)
          xStart yStart xLen yLen) := by
  ext z
  unfold torusRegionRealization
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hxInt : (xStart : ℤ) ≤ (xStart + xLen : ℕ) - 1 := by omega
    have hyInt : (yStart : ℤ) ≤ (yStart + yLen : ℕ) - 1 := by omega
    obtain ⟨i, hi₁, hi₂, hip⟩ := exists_integer_center_in_interval
      (xStart : ℤ) ((xStart + xLen : ℕ) - 1) hxInt p.1 (by
        have hlo := hp.1.1
        have hhi := hp.1.2
        push_cast at hlo hhi ⊢
        constructor <;> linarith)
    obtain ⟨j, hj₁, hj₂, hjp⟩ := exists_integer_center_in_interval
      (yStart : ℤ) ((yStart + yLen : ℕ) - 1) hyInt p.2 (by
        have hlo := hp.2.1
        have hhi := hp.2.2
        push_cast at hlo hhi ⊢
        constructor <;> linarith)
    have hi₀ : 0 ≤ i := le_trans (by omega) hi₁
    have hj₀ : 0 ≤ j := le_trans (by omega) hj₁
    have hiw : i < (width : ℤ) := by omega
    have hjh : j < (height : ℤ) := by omega
    have hiv : (((i : ZMod width).val : ℕ) : ℤ) = i := by
      rw [ZMod.val_intCast, Int.emod_eq_of_lt hi₀ hiw]
    have hjv : (((j : ZMod height).val : ℕ) : ℤ) = j := by
      rw [ZMod.val_intCast, Int.emod_eq_of_lt hj₀ hjh]
    let v : TorusVertex width height := ((i : ZMod width), (j : ZMod height))
    have hv : v ∈ torusContiguousRectangle xStart yStart xLen yLen := by
      rw [mem_torusContiguousRectangle]
      change xStart ≤ (i : ZMod width).val ∧ (i : ZMod width).val < xStart + xLen ∧
        yStart ≤ (j : ZMod height).val ∧ (j : ZMod height).val < yStart + yLen
      omega
    apply mem_iUnion_of_mem v
    apply mem_iUnion_of_mem hv
    refine ⟨p - ((i : ℝ), (j : ℝ)), ?_, ?_⟩
    · simpa only [Prod.fst_sub, Prod.snd_sub, mem_prod, mem_Icc, ← abs_le, neg_div]
        using And.intro hip hjp
    · change torusVertexPoint v + torusRealProjection width height
        (p - ((i : ℝ), (j : ℝ))) = torusRealProjection width height p
      rw [show torusVertexPoint v = torusRealProjection width height ((i : ℝ), (j : ℝ))
        from torusVertexPoint_intCast (i, j), ← map_add, add_sub_cancel]
  · intro hz
    simp only [mem_iUnion, exists_prop] at hz
    obtain ⟨v, hv, d, hd, rfl⟩ := hz
    have hv' := (mem_torusContiguousRectangle xStart yStart xLen yLen v).mp hv
    have hx₁ : (xStart : ℝ) ≤ (v.1.val : ℝ) := by exact_mod_cast hv'.1
    have hx₂ : (v.1.val : ℝ) + 1 ≤ (xStart + xLen : ℕ) := by
      exact_mod_cast hv'.2.1
    have hy₁ : (yStart : ℝ) ≤ (v.2.val : ℝ) := by exact_mod_cast hv'.2.2.1
    have hy₂ : (v.2.val : ℝ) + 1 ≤ (yStart + yLen : ℕ) := by
      exact_mod_cast hv'.2.2.2
    refine ⟨((v.1.val : ℝ), (v.2.val : ℝ)) + d, ?_, ?_⟩
    · dsimp [planarRectangle]
      obtain ⟨⟨hd₁, hd₂⟩, ⟨hd₃, hd₄⟩⟩ := hd
      constructor <;> constructor <;> dsimp <;> linarith
    · rw [map_add, ← torusVertexPoint_eq_projection]

private theorem addCircle_injOn_short_interval (P a b : ℝ) (hP : 0 < P)
    (hb : b < a + P) : Set.InjOn (fun x : ℝ => (x : AddCircle P)) (Icc a b) := by
  let : Fact (0 < P) := ⟨hP⟩
  intro x hx y hy hxy
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show x ∈ Ico a (a + P) from ⟨hx.1, hx.2.trans_lt hb⟩)
    (show y ∈ Ico a (a + P) from ⟨hy.1, hy.2.trans_lt hb⟩)).mp hxy

private theorem projection_planarRectangle_injOn
    {width height : ℕ} [NeZero width] [NeZero height]
    (xStart yStart xLen yLen : ℕ) (hx : xLen < width) (hy : yLen < height) :
    Set.InjOn (torusRealProjection width height) (planarRectangle xStart yStart xLen yLen) := by
  have hxp : (0 : ℝ) < width := Nat.cast_pos.mpr (NeZero.pos width)
  have hyp : (0 : ℝ) < height := Nat.cast_pos.mpr (NeZero.pos height)
  have hxl : (xLen : ℝ) < width := by exact_mod_cast hx
  have hyl : (yLen : ℝ) < height := by exact_mod_cast hy
  intro p hp q hq he
  apply Prod.ext
  · exact addCircle_injOn_short_interval (width : ℝ) ((xStart : ℝ) - 1 / 2)
      ((xStart + xLen : ℕ) - 1 / 2 : ℝ) hxp (by push_cast; linarith)
      hp.1 hq.1 (congrArg Prod.fst he)
  · exact addCircle_injOn_short_interval (height : ℝ) ((yStart : ℝ) - 1 / 2)
      ((yStart + yLen : ℕ) - 1 / 2 : ℝ) hyp (by push_cast; linarith)
      hp.2 hq.2 (congrArg Prod.snd he)

/-- The actual closed-cell realization of a positive nonwrapping rectangle
with both side lengths shorter than the torus periods is simply connected.
Source: SCP10, Theorem 6.7, lines 1995–2011; auxiliary rectangle geometry. -/
theorem isSimplyConnected_torusRegionRealization_rectangle
    {width height : ℕ} [NeZero width] [NeZero height]
    (xStart yStart xLen yLen : ℕ) (hx : 0 < xLen) (hy : 0 < yLen)
    (hxl : xLen < width) (hyl : yLen < height)
    (hxb : xStart + xLen ≤ width) (hyb : yStart + yLen ≤ height) :
    IsSimplyConnected (torusRegionRealization
      (torusContiguousRectangle (width := width) (height := height)
        xStart yStart xLen yLen)) := by
  let S := planarRectangle xStart yStart xLen yLen
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hc : Convex ℝ S := (convex_Icc _ _).prod (convex_Icc _ _)
  have hn : S.Nonempty := by
    have hxr : (1 : ℝ) ≤ xLen := by exact_mod_cast hx
    have hyr : (1 : ℝ) ≤ yLen := by exact_mod_cast hy
    refine ⟨((xStart : ℝ), (yStart : ℝ)), ?_⟩
    dsimp [S, planarRectangle]
    push_cast
    constructor <;> constructor <;> linarith
  let : ContractibleSpace S := hc.contractibleSpace hn
  let f : S → AddCircle (width : ℝ) × AddCircle (height : ℝ) :=
    fun p => torusRealProjection width height p.1
  have hcont : Continuous f := continuous_torusRealProjection.comp continuous_subtype_val
  have hinj : Function.Injective f := by
    intro p q he
    exact Subtype.ext (projection_planarRectangle_injOn
      xStart yStart xLen yLen hxl hyl p.2 q.2 he)
  have hemb := hcont.isClosedEmbedding hinj
  have hSC : IsSimplyConnected (Set.range f) :=
    hemb.isEmbedding.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  have hrange : Set.range f = torusRegionRealization
      (torusContiguousRectangle (width := width) (height := height)
        xStart yStart xLen yLen) := by
    rw [← projection_planarRectangle_eq xStart yStart xLen yLen hx hy hxb hyb]
    exact Set.range_domRestrict _ _
  rwa [hrange] at hSC

end TNLean.PEPS
