/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GInjectiveStripIntersection

/-!
# Ground spaces of heterogeneous open strips

A finite strip may have a different tensor and physical alphabet at every
block. Its common local ground space consists of the vectors whose every
adjacent two-block slice belongs to the actual two-block boundary-map range.
For G-injective blocks and at least two blocks, this space is precisely the
range of the full open-strip boundary map.

Source: SCP10, arXiv:1001.3807, the iterated intersection argument of
Theorem 4.11, lines 1177–1195, and strip growth in Theorem 5.4,
lines 1373–1436. This is an open-strip statement; a graph PEPS application
requires a separate identification of the blocked graph contractions.
-/

open Module LinearMap Representation

namespace TNLean.PEPS

universe u v

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- A tensor block with its own finite physical alphabet. Source: SCP10,
Definition 4.2, lines 893–910, with independent physical spaces at each block. -/
structure StripBlock (V : Type v) [AddCommGroup V] [Module ℂ V] where
  Physical : Type u
  finitePhysical : Finite Physical
  tensor : Physical → Module.End ℂ V

instance (a : StripBlock V) : Finite a.Physical := a.finitePhysical

/-- Physical configurations along a strip, retaining the alphabet of every block. -/
def stripConfig : List (StripBlock V) → Type u
  | [] => PUnit
  | [a] => a.Physical
  | a :: b :: bs => a.Physical × stripConfig (b :: bs)

instance finite_stripConfig (bs : List (StripBlock V)) : Finite (stripConfig bs) := by
  induction bs with
  | nil => dsimp [stripConfig]; infer_instance
  | cons a bs ih =>
    cases bs with
    | nil => dsimp [stripConfig]; infer_instance
    | cons b bs => dsimp [stripConfig]; infer_instance

/-- The ordered product tensor of the strip. Source: concatenation in SCP10,
Lemma 4.7, lines 1036–1063, iterated in Theorem 4.11, lines 1177–1195. -/
def stripTensor : (bs : List (StripBlock V)) → stripConfig bs → Module.End ℂ V
  | [], _ => 1
  | [a], i => a.tensor i
  | a :: b :: bs, (i, x) => a.tensor i * stripTensor (b :: bs) x

/-- Fix the remaining physical configuration after the first adjacent pair. -/
def stripFirstPairSlice {ι κ ν : Type*} (k : ν) :
    (ι × (κ × ν) → ℂ) →ₗ[ℂ] (ι × κ → ℂ) where
  toFun ψ p := ψ (p.1, (p.2, k))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Fix the first physical configuration and retain the rest of the strip. -/
def stripTailSlice {ι κ : Type*} (i : ι) : (ι × κ → ℂ) →ₗ[ℂ] (κ → ℂ) where
  toFun ψ x := ψ (i, x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The common adjacent-pair ground space. There are no conditions on zero
or one block. On two blocks there is exactly their true boundary-range
condition. A longer strip imposes that first-pair condition on every remaining
physical configuration, together with every adjacent condition on the tail.
Source: the local parent conditions iterated in SCP10, Theorem 4.11,
lines 1177–1195, and Theorem 5.4, lines 1373–1436. -/
noncomputable def stripParentGroundSpace :
    (bs : List (StripBlock V)) → Submodule ℂ (stripConfig bs → ℂ)
  | [] => ⊤
  | [_] => ⊤
  | [a, b] => (mpsSiteMap (stripTensor [a, b])).range
  | a :: b :: c :: bs =>
      (⨅ k : stripConfig (c :: bs),
        (mpsSiteMap (concatTensor a.tensor b.tensor)).range.comap (stripFirstPairSlice k)) ⊓
      ⨅ i : a.Physical, (stripParentGroundSpace (b :: c :: bs)).comap (stripTailSlice i)

/-- On a strip with at least three blocks, the first-pair condition and the
remaining adjacent conditions are exactly the corresponding physical-slice
conditions. Source: SCP10, iterated local parent construction in Theorem 4.11,
lines 1177–1195, and Theorem 5.4, lines 1373–1436. -/
theorem mem_stripParentGroundSpace_cons_cons_cons_iff
    (a b c : StripBlock V) (bs : List (StripBlock V))
    (ψ : stripConfig (a :: b :: c :: bs) → ℂ) :
    ψ ∈ stripParentGroundSpace (a :: b :: c :: bs) ↔
      (∀ k : stripConfig (c :: bs),
        (fun p => ψ (p.1, (p.2, k))) ∈
          (mpsSiteMap (concatTensor a.tensor b.tensor)).range) ∧
      ∀ i : a.Physical, (fun x => ψ (i, x)) ∈ stripParentGroundSpace (b :: c :: bs) := by
  simp only [stripParentGroundSpace, Submodule.mem_inf, Submodule.mem_iInf]
  rfl

variable {G : Type*} [Group G] [Finite G] [FiniteDimensional ℂ V]
variable {ρ : Representation ℂ G V}

/-- Every nonempty ordered product of G-injective blocks is G-injective.
Source: SCP10, Lemma 4.7, lines 1036–1063. -/
theorem isGInjective_stripTensor (bs : List (StripBlock V)) (hne : bs ≠ [])
    (ha : ∀ a ∈ bs, IsGInjective (linHom ρ ρ) (mpsSiteMap a.tensor)) :
    IsGInjective (linHom ρ ρ) (mpsSiteMap (stripTensor bs)) := by
  induction bs with
  | nil => contradiction
  | cons a bs ih =>
    cases bs with
    | nil => exact ha a (by simp)
    | cons b bs =>
      change IsGInjective (linHom ρ ρ)
        (mpsSiteMap (concatTensor a.tensor (stripTensor (b :: bs))))
      exact (ha a (by simp)).mpsSiteMap_concatTensor
        (ih (by simp) (fun c hc => ha c (by simp [hc])))

/-- Every heterogeneous open strip of at least two G-injective blocks has
exactly the full boundary-map range as its common adjacent-pair ground space.
No intersection identity is assumed. Source: the iteration of SCP10,
Theorem 4.8, in Theorem 4.11, lines 1177–1195, and Theorem 5.4,
lines 1373–1436. -/
theorem stripParentGroundSpace_eq_range (bs : List (StripBlock V)) (hlen : 2 ≤ bs.length)
    (ha : ∀ a ∈ bs, IsGInjective (linHom ρ ρ) (mpsSiteMap a.tensor)) :
    stripParentGroundSpace bs = (mpsSiteMap (stripTensor bs)).range := by
  induction bs with
  | nil => simp at hlen
  | cons a bs ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      cases bs with
      | nil => rfl
      | cons c bs =>
        have htail := ih (by simp) (fun x hx => ha x (by simp [hx]))
        have hA := ha a (by simp)
        have hB := ha b (by simp)
        have hC := isGInjective_stripTensor (c :: bs) (by simp)
          (fun x hx => ha x (by simp [hx]))
        ext ψ
        let φ : (a.Physical × b.Physical) × stripConfig (c :: bs) → ℂ :=
          fun p => ψ (p.1.1, (p.1.2, p.2))
        have hspaces : ψ ∈ stripParentGroundSpace (a :: b :: c :: bs) ↔
            φ ∈ stripLeftGroundSpace a.tensor b.tensor ⊓
              stripRightGroundSpace b.tensor (stripTensor (c :: bs)) := by
          simp only [stripParentGroundSpace, Submodule.mem_inf, Submodule.mem_iInf,
            Submodule.mem_comap, htail, stripLeftGroundSpace, stripRightGroundSpace]
          rfl
        rw [hspaces, hA.strip_groundSpace_intersection hB hC]
        constructor
        · rintro ⟨X, hX⟩
          refine ⟨X, funext fun ⟨i, ⟨j, k⟩⟩ => ?_⟩
          change LinearMap.trace ℂ V
            (a.tensor i * (b.tensor j * stripTensor (c :: bs) k) * X) = ψ (i, (j, k))
          have h := congr_fun hX ((i, j), k)
          simpa only [mpsSiteMap_apply, concatTensor_apply, stripTensor, mul_assoc, φ] using h
        · rintro ⟨X, hX⟩
          refine ⟨X, funext fun ⟨⟨i, j⟩, k⟩ => ?_⟩
          have h := congr_fun hX (i, (j, k))
          change LinearMap.trace ℂ V
            (a.tensor i * (b.tensor j * stripTensor (c :: bs) k) * X) = ψ (i, (j, k)) at h
          simpa only [mpsSiteMap_apply, concatTensor_apply, stripTensor, mul_assoc, φ] using h

/-- Every vector satisfying all adjacent strip conditions has a unique
invariant boundary operator. Source: SCP10, Definition 4.2, lines 893–910,
and the open-boundary intersection iteration of Theorem 4.11, lines 1177–1195. -/
theorem existsUnique_invariant_boundary_of_mem_stripParentGroundSpace
    (bs : List (StripBlock V)) (hlen : 2 ≤ bs.length)
    (ha : ∀ a ∈ bs, IsGInjective (linHom ρ ρ) (mpsSiteMap a.tensor))
    {ψ : stripConfig bs → ℂ} (hψ : ψ ∈ stripParentGroundSpace bs) :
    ∃! X : (linHom ρ ρ).invariants, mpsSiteMap (stripTensor bs) X = ψ := by
  have hne : bs ≠ [] := by rintro rfl; simp at hlen
  have hT := isGInjective_stripTensor bs hne ha
  rw [stripParentGroundSpace_eq_range bs hlen ha] at hψ
  obtain ⟨X, hX, huniq⟩ := hT.bijective_invariants_rangeRestrict.existsUnique ⟨ψ, hψ⟩
  exact ⟨X, congrArg Subtype.val hX, fun Y hY => huniq Y (Subtype.ext hY)⟩

/-- The common adjacent-pair ground-space dimension is independent of the
strip length and equals the invariant virtual operator dimension.
Source: SCP10, Definition 4.2, lines 893–910, and the open-boundary
intersection iteration of Theorem 4.11, lines 1177–1195. -/
theorem finrank_stripParentGroundSpace (bs : List (StripBlock V)) (hlen : 2 ≤ bs.length)
    (ha : ∀ a ∈ bs, IsGInjective (linHom ρ ρ) (mpsSiteMap a.tensor)) :
    Module.finrank ℂ (stripParentGroundSpace bs) =
      Module.finrank ℂ (linHom ρ ρ).invariants := by
  have hne : bs ≠ [] := by rintro rfl; simp at hlen
  rw [stripParentGroundSpace_eq_range bs hlen ha]
  exact (isGInjective_stripTensor bs hne ha).finrank_range

end TNLean.PEPS
