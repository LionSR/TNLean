/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointActiveHamiltonian
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointEdgeCompression

/-!
# Placing the actual active-edge interactions with their spectators

For a nonempty bulk, each nonwrapping edge is a first edge, an interior
bulk edge, or a last edge. Explicit configuration equivalences separate its
active coordinates from the remaining coordinates. The corresponding
Euclidean isometries express the actual compressed physical interaction as
its actual cropped two-site constraint acting independently on every
spectator fiber.

The proof uses the original physical configuration encoding, its zero
extension, and the derived smaller-edge compression identities. No
identification of local kernels or reducing sectors is assumed.
Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped BigOperators ComplexOrder Matrix InnerProductSpace

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

variable {D₀ D₁ N : ℕ}

/-- An edge in a chain with `N + 1` bulk sites and two boundary sites. -/
inductive MixedEndpointActiveEdgeSite (N : ℕ) where
  | first
  | interior (i : NonwrappingStart 2 (N + 1))
  | last

/-- Which cropped two-site coordinate space is used at an active-chain edge. -/
def mixedEndpointActiveEdgePosition (p : MixedEndpointActiveEdgeSite N) :
    MixedEndpointEdgePosition :=
  match p with
  | .first => .first
  | .interior _ => .interior
  | .last => .last

/-- The actual nonwrapping start of a first, interior, or last edge. -/
def mixedEndpointActiveEdgeStart (p : MixedEndpointActiveEdgeSite N) :
    NonwrappingStart 2 (N + 1 + 1 + 1) :=
  match p with
  | .first => ⟨0, by simp⟩
  | .interior i => ⟨⟨i.1.val + 1, by have := i.1.isLt; omega⟩,
      by
        change i.1.val + 1 + 2 ≤ N + 1 + 1 + 1
        have := i.2
        omega⟩
  | .last => ⟨⟨N + 1, by omega⟩, by
      change N + 1 + 2 ≤ N + 1 + 1 + 1
      omega⟩

/-- Every actual nonwrapping edge has one of the three coordinate descriptions. -/
theorem mixedEndpointActiveEdgeStart_surjective :
    Function.Surjective (mixedEndpointActiveEdgeStart (N := N)) := by
  intro i
  by_cases hfirst : i.1.val = 0
  · refine ⟨.first, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    exact hfirst.symm
  · by_cases hlast : i.1.val = N + 1
    · refine ⟨.last, ?_⟩
      apply Subtype.ext
      apply Fin.ext
      exact hlast.symm
    · have hi := i.2
      let j : NonwrappingStart 2 (N + 1) :=
        ⟨⟨i.1.val - 1, by omega⟩, by
          change i.1.val - 1 + 2 ≤ N + 1
          omega⟩
      refine ⟨.interior j, ?_⟩
      apply Subtype.ext
      apply Fin.ext
      change i.1.val - 1 + 1 = i.1.val
      omega

/-- Separate the first boundary site and first bulk site from the remainder. -/
def mixedEndpointFirstEdgeConfigEquiv (D₀ D₁ N : ℕ) :
    endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ (N + 1) ≃
      endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ ×
        (Cfg (D₀ * D₀) N × Fin D₀ × (Fin D₀ ⊕ Fin D₁)) where
  toFun ξ := (((ξ.1, ξ.2.1.1), ξ.2.1.2.1 0),
    (Fin.tail ξ.2.1.2.1, ξ.2.1.2.2, ξ.2.2))
  invFun x := (x.1.1.1, (x.1.1.2, Fin.cons x.1.2 x.2.1, x.2.2.1), x.2.2.2)
  left_inv ξ := by
    rcases ξ with ⟨a, ⟨b, σ, c⟩, e⟩
    simp only [Fin.cons_self_tail]
  right_inv x := by
    rcases x with ⟨⟨⟨a, b⟩, q⟩, σ, c, e⟩
    simp only [Fin.cons_zero, Fin.tail_cons]

/-- Separate the last bulk site and last boundary site from the remainder. -/
def mixedEndpointLastEdgeConfigEquiv (D₀ D₁ N : ℕ) :
    endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ (N + 1) ≃
      endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ ×
        ((Fin D₀ ⊕ Fin D₁) × Fin D₀ × Cfg (D₀ * D₀) N) where
  toFun ξ := ((ξ.2.1.2.1 (Fin.last N), (ξ.2.1.2.2, ξ.2.2)),
    (ξ.1, ξ.2.1.1, Fin.init ξ.2.1.2.1))
  invFun x := (x.2.1, (x.2.2.1, Fin.snoc x.2.2.2 x.1.1, x.1.2.1), x.1.2.2)
  left_inv ξ := by
    rcases ξ with ⟨a, ⟨b, σ, c⟩, e⟩
    simp only [Fin.snoc_init_self]
  right_inv x := by
    rcases x with ⟨⟨q, c, e⟩, a, b, σ⟩
    simp only [Fin.snoc_last, Fin.init_snoc]

/-- Separate an interior bulk edge; both exterior registers and both exposed
boundary registers remain spectator coordinates. -/
def mixedEndpointInteriorEdgeConfigEquiv (D₀ D₁ : ℕ)
    (i : NonwrappingStart 2 (N + 1)) :
    endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ (N + 1) ≃
      Cfg (D₀ * D₀) 2 × endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ (N + 1 - 2) := by
  let e := cyclicActiveBlockConfigEquiv (D₀ * D₀) 2 (by have := i.2; omega) i.1
  exact
    { toFun := fun ξ => ((e ξ.2.1.2.1).1,
        (ξ.1, (ξ.2.1.1, (e ξ.2.1.2.1).2, ξ.2.1.2.2), ξ.2.2))
      invFun := fun x => (x.2.1,
        (x.2.2.1.1, e.symm (x.1, x.2.2.1.2.1), x.2.2.1.2.2), x.2.2.2)
      left_inv := by
        rintro ⟨a, ⟨b, σ, c⟩, f⟩
        simp only [Prod.mk.eta, Equiv.symm_apply_apply]
      right_inv := by
        rintro ⟨ω, a, ⟨b, σ, c⟩, f⟩
        simp only [Equiv.apply_symm_apply] }

/-- The explicit spectator index type for each active edge. -/
def mixedEndpointActiveEdgeSpectator (D₀ D₁ : ℕ)
    (p : MixedEndpointActiveEdgeSite N) : Type :=
  match p with
  | .first => Cfg (D₀ * D₀) N × Fin D₀ × (Fin D₀ ⊕ Fin D₁)
  | .interior _ => endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ (N + 1 - 2)
  | .last => (Fin D₀ ⊕ Fin D₁) × Fin D₀ × Cfg (D₀ * D₀) N

instance (p : MixedEndpointActiveEdgeSite N) :
    Fintype (mixedEndpointActiveEdgeSpectator D₀ D₁ p) := by
  cases p <;> dsimp [mixedEndpointActiveEdgeSpectator] <;> infer_instance

/-- The complete edge-and-spectator configuration split. -/
def mixedEndpointActiveEdgeConfigEquiv (D₀ D₁ : ℕ)
    (p : MixedEndpointActiveEdgeSite N) :
    endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ (N + 1) ≃
      mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p) ×
        mixedEndpointActiveEdgeSpectator D₀ D₁ p :=
  match p with
  | .first => mixedEndpointFirstEdgeConfigEquiv D₀ D₁ N
  | .interior i => mixedEndpointInteriorEdgeConfigEquiv D₀ D₁ i
  | .last => mixedEndpointLastEdgeConfigEquiv D₀ D₁ N

/-- The Euclidean coordinate isometry exposing the selected edge and all
remaining active coordinates. -/
def mixedEndpointActiveEdgeLinearIsometryEquiv (D₀ D₁ : ℕ)
    (p : MixedEndpointActiveEdgeSite N) :
    mixedEndpointActiveSpace D₀ D₁ (N + 1) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p) ×
          mixedEndpointActiveEdgeSpectator D₀ D₁ p) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p)

/-- The selected-edge fiber of an active-chain vector. -/
def mixedEndpointActiveEdgeFiber (p : MixedEndpointActiveEdgeSite N)
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1))
    (s : mixedEndpointActiveEdgeSpectator D₀ D₁ p) :
    EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p)) :=
  WithLp.toLp 2 fun η => v ((mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p).symm (η, s))

/-- Place an actual cropped edge operator independently on every spectator
fiber through the explicit configuration isometry. -/
def mixedEndpointActiveEdgePlacement (p : MixedEndpointActiveEdgeSite N)
    (T : EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p)) →ₗ[ℂ]
      EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p))) :
    mixedEndpointActiveSpace D₀ D₁ (N + 1) →ₗ[ℂ]
      mixedEndpointActiveSpace D₀ D₁ (N + 1) :=
  (mixedEndpointActiveEdgeLinearIsometryEquiv D₀ D₁ p).symm.toLinearEquiv.conj
    (ContinuousLinearMap.rightFiberwiseMap
      (S := mixedEndpointActiveEdgeSpectator D₀ D₁ p)
      (LinearMap.toContinuousLinearMap T)).toLinearMap

/-- The placed operator acts on the corresponding explicit edge fiber. -/
theorem mixedEndpointActiveEdgePlacement_apply (p : MixedEndpointActiveEdgeSite N)
    (T : EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p)) →ₗ[ℂ]
      EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p)))
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1))
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ (N + 1)) :
    mixedEndpointActiveEdgePlacement p T v ξ =
      T (mixedEndpointActiveEdgeFiber p v (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).2)
        (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).1 := by
  have hRF
      (x : EuclideanSpace ℂ
        (mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p) ×
          mixedEndpointActiveEdgeSpectator D₀ D₁ p))
      (z : mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p) ×
        mixedEndpointActiveEdgeSpectator D₀ D₁ p) :
      ContinuousLinearMap.rightFiberwiseMap
          (S := mixedEndpointActiveEdgeSpectator D₀ D₁ p) T.toContinuousLinearMap x z =
        T (ContinuousLinearMap.rightFiber x z.2) z.1 := by
    rcases z with ⟨η, s⟩
    exact ContinuousLinearMap.rightFiberwiseMap_apply_apply T.toContinuousLinearMap x η s
  simp [mixedEndpointActiveEdgePlacement, LinearEquiv.conj_apply,
    mixedEndpointActiveEdgeLinearIsometryEquiv,
    LinearIsometryEquiv.piLpCongrLeft_symm, LinearIsometryEquiv.piLpCongrLeft_apply,
    hRF, ContinuousLinearMap.rightFiber, mixedEndpointActiveEdgeFiber]

private theorem contiguousCfg_apply_mem {d L M s : ℕ}
    {ω : Cfg d M} {τ : Cfg d L} {k : Fin L}
    (hk : s ≤ k.val ∧ k.val < s + M) :
    contiguousCfg s M ω τ k = ω ⟨k.val - s, by omega⟩ :=
  dite_eq_left hk

private theorem contiguousCfg_apply_not_mem {d L M s : ℕ}
    {ω : Cfg d M} {τ : Cfg d L} {k : Fin L}
    (hk : ¬ (s ≤ k.val ∧ k.val < s + M)) :
    contiguousCfg s M ω τ k = τ k :=
  dite_eq_right hk

private theorem firstEdge_contiguousReplacement
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ (N + 1))
    (η : endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) :
    contiguousCfg 0 2 (mixedEndpointEdgePhysicalCfg .first η)
        (mixedEndpointActivePhysicalCfg ξ) =
      mixedEndpointActivePhysicalCfg
        ((mixedEndpointFirstEdgeConfigEquiv D₀ D₁ N).symm
          (η, (mixedEndpointFirstEdgeConfigEquiv D₀ D₁ N ξ).2)) := by
  rcases ξ with ⟨a, ⟨b, σ, c⟩, e⟩
  rcases η with ⟨⟨a', b'⟩, q⟩
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · rw [contiguousCfg_apply_mem (M := 2) (s := 0)
      (k := (0 : Fin (N + 1 + 1 + 1))) (by simp)]
    simp [mixedEndpointEdgePhysicalCfg, mixedEndpointActivePhysicalCfg,
      mixedEndpointFirstEdgeConfigEquiv]
  · refine Fin.lastCases ?_ (fun k => ?_) k
    · rw [contiguousCfg_apply_not_mem (M := 2) (s := 0)
        (k := (Fin.last (N + 1)).succ)
        (by simp only [Fin.val_succ, Fin.val_last]; omega)]
      simp [mixedEndpointActivePhysicalCfg, mixedEndpointFirstEdgeConfigEquiv]
    · refine Fin.cases ?_ (fun k => ?_) k
      · rw [contiguousCfg_apply_mem (M := 2) (s := 0)
          (k := (0 : Fin (N + 1)).castSucc.succ) (by simp)]
        simp [mixedEndpointEdgePhysicalCfg, mixedEndpointActivePhysicalCfg,
          mixedEndpointFirstEdgeConfigEquiv]
      · rw [contiguousCfg_apply_not_mem (M := 2) (s := 0)
          (k := k.succ.castSucc.succ)
          (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
        simp only [mixedEndpointActivePhysicalCfg, mixedEndpointFirstEdgeConfigEquiv,
          Fin.cons_succ, Fin.snoc_castSucc, Fin.tail]

private theorem lastEdge_contiguousReplacement
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ (N + 1))
    (η : endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) :
    contiguousCfg (N + 1) 2 (mixedEndpointEdgePhysicalCfg .last η)
        (mixedEndpointActivePhysicalCfg ξ) =
      mixedEndpointActivePhysicalCfg
        ((mixedEndpointLastEdgeConfigEquiv D₀ D₁ N).symm
          (η, (mixedEndpointLastEdgeConfigEquiv D₀ D₁ N ξ).2)) := by
  rcases ξ with ⟨a, ⟨b, σ, c⟩, e⟩
  rcases η with ⟨q, c', e'⟩
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · rw [contiguousCfg_apply_not_mem (M := 2) (s := N + 1)
      (k := (0 : Fin (N + 1 + 1 + 1))) (by simp)]
    simp [mixedEndpointActivePhysicalCfg, mixedEndpointLastEdgeConfigEquiv]
  · refine Fin.lastCases ?_ (fun k => ?_) k
    · rw [contiguousCfg_apply_mem (M := 2) (s := N + 1)
        (k := (Fin.last (N + 1)).succ)
        (by simp only [Fin.val_succ, Fin.val_last]; omega)]
      simp [mixedEndpointEdgePhysicalCfg, mixedEndpointActivePhysicalCfg,
        mixedEndpointLastEdgeConfigEquiv]
    · refine Fin.lastCases ?_ (fun k => ?_) k
      · rw [contiguousCfg_apply_mem (M := 2) (s := N + 1)
          (k := (Fin.last N).castSucc.succ)
          (by simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]; omega)]
        simp [mixedEndpointEdgePhysicalCfg, mixedEndpointActivePhysicalCfg,
          mixedEndpointLastEdgeConfigEquiv]
      · rw [contiguousCfg_apply_not_mem (M := 2) (s := N + 1)
          (k := k.castSucc.castSucc.succ)
          (by have hk := k.isLt; simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
        simp [mixedEndpointActivePhysicalCfg, mixedEndpointLastEdgeConfigEquiv, Fin.init]

private theorem interiorEdge_contiguousReplacement
    (i : NonwrappingStart 2 (N + 1))
    (a e : Fin D₀ ⊕ Fin D₁) (b c : Fin D₀)
    (σ : Cfg (D₀ * D₀) (N + 1)) (η : Cfg (D₀ * D₀) 2) :
    contiguousCfg (i.1.val + 1) 2 (mixedEndpointEdgePhysicalCfg .interior η)
        (mixedEndpointActivePhysicalCfg (a, (b, σ, c), e)) =
      mixedEndpointActivePhysicalCfg (a, (b, contiguousCfg i.1.val 2 η σ, c), e) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · rw [contiguousCfg_apply_not_mem (M := 2) (s := i.1.val + 1)
      (k := (0 : Fin (N + 1 + 1 + 1))) (by simp)]
    rfl
  · refine Fin.lastCases ?_ (fun k => ?_) k
    · rw [contiguousCfg_apply_not_mem (M := 2) (s := i.1.val + 1)
        (k := (Fin.last (N + 1)).succ)
        (by have hi := i.2; simp only [Fin.val_succ, Fin.val_last]; omega)]
      simp [mixedEndpointActivePhysicalCfg]
    · simp only [mixedEndpointActivePhysicalCfg, Fin.cons_succ, Fin.snoc_castSucc]
      by_cases hk : i.1.val ≤ k.val ∧ k.val < i.1.val + 2
      · have hglobal : i.1.val + 1 ≤ k.castSucc.succ.val ∧
            k.castSucc.succ.val < i.1.val + 1 + 2 := by
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        rw [contiguousCfg_apply_mem (M := 2) (s := i.1.val + 1)
            (k := k.castSucc.succ) hglobal,
          contiguousCfg_apply_mem (M := 2) (s := i.1.val) (k := k) hk]
        dsimp only [mixedEndpointEdgePhysicalCfg]
        apply congrArg (mixedEndpointFirstPhysicalIndex D₁)
        apply congrArg η
        apply Fin.ext
        change k.val + 1 - (i.1.val + 1) = k.val - i.1.val
        omega
      · have hglobal : ¬ (i.1.val + 1 ≤ k.castSucc.succ.val ∧
            k.castSucc.succ.val < i.1.val + 1 + 2) := by
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        rw [contiguousCfg_apply_not_mem (M := 2) (s := i.1.val + 1)
            (k := k.castSucc.succ) hglobal,
          contiguousCfg_apply_not_mem (M := 2) (s := i.1.val) (k := k) hk]
        simp only [Fin.cons_succ, Fin.snoc_castSucc]

/-- Replacing the actual physical edge by an encoded cropped configuration
is exactly replacement of the selected edge coordinate in the active split. -/
theorem mixedEndpointActivePhysicalCfg_edgeReplacement
    (p : MixedEndpointActiveEdgeSite N)
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ (N + 1))
    (η : mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p)) :
    cyclicCfg (Fin.pos (mixedEndpointActiveEdgeStart p).1) 2
        (mixedEndpointActiveEdgeStart p).1
        (mixedEndpointEdgePhysicalCfg (mixedEndpointActiveEdgePosition p) η)
        (mixedEndpointActivePhysicalCfg ξ) =
      mixedEndpointActivePhysicalCfg
        ((mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p).symm
          (η, (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).2)) := by
  rw [cyclicCfg_eq_contiguousCfg _ (by omega) (mixedEndpointActiveEdgeStart p).2]
  cases p with
  | first => exact firstEdge_contiguousReplacement ξ η
  | last => exact lastEdge_contiguousReplacement ξ η
  | interior i =>
    change Cfg (D₀ * D₀) 2 at η
    rcases ξ with ⟨a, ⟨b, σ, c⟩, e⟩
    have hbulk : 2 ≤ N + 1 := by have := i.2; omega
    change contiguousCfg (i.1.val + 1) 2 (mixedEndpointEdgePhysicalCfg .interior η)
      (mixedEndpointActivePhysicalCfg (a, (b, σ, c), e)) =
        mixedEndpointActivePhysicalCfg (a,
          (b, (cyclicActiveBlockConfigEquiv (D₀ * D₀) 2 hbulk i.1).symm
            (η, (cyclicActiveBlockConfigEquiv (D₀ * D₀) 2 hbulk i.1 σ).2), c), e)
    have hjoin :
        (cyclicActiveBlockConfigEquiv (D₀ * D₀) 2 hbulk i.1).symm
            (η, (cyclicActiveBlockConfigEquiv (D₀ * D₀) 2 hbulk i.1 σ).2) =
          contiguousCfg i.1.val 2 η σ :=
      (cyclicCfg_eq_join_cyclicActiveBlock hbulk i.1 η σ).symm.trans
        (cyclicCfg_eq_contiguousCfg (Fin.pos i.1) hbulk i.2 η σ)
    exact (interiorEdge_contiguousReplacement i a e b c σ η).trans
      (congrArg (fun τ : Cfg (D₀ * D₀) (N + 1) =>
        mixedEndpointActivePhysicalCfg (a, (b, τ, c), e)) hjoin.symm)

private theorem extractWindow_cyclicCfg_two {d L : ℕ} (hL : 2 ≤ L)
    (i : Fin L) (ω : Cfg d 2) (τ : Cfg d L) :
    extractWindow 2 i (cyclicCfg (Fin.pos i) 2 i ω τ) = ω := by
  funext r
  exact cyclicCfg_cyclicForwardSite_apply (Fin.pos i) hL i ω τ r

/-- Extracting an actual physical edge reads exactly the edge coordinate
of the explicit active configuration split. -/
theorem extractWindow_mixedEndpointActivePhysicalCfg
    (p : MixedEndpointActiveEdgeSite N)
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ (N + 1)) :
    extractWindow 2 (mixedEndpointActiveEdgeStart p).1 (mixedEndpointActivePhysicalCfg ξ) =
      mixedEndpointEdgePhysicalCfg (mixedEndpointActiveEdgePosition p)
        (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).1 := by
  have h := mixedEndpointActivePhysicalCfg_edgeReplacement p ξ
    (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).1
  simp only [Prod.mk.eta, Equiv.symm_apply_apply] at h
  have he := congrArg (extractWindow 2 (mixedEndpointActiveEdgeStart p).1) h
  rw [extractWindow_cyclicCfg_two (by omega)] at he
  exact he.symm

/-- A physical replacement outside the cropped edge encoding cannot be an
active full-chain configuration. This follows from the actual active
configuration range, rather than an assumed local support condition. -/
theorem not_active_edgeReplacement_of_not_mem_range
    (p : MixedEndpointActiveEdgeSite N)
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ (N + 1))
    (ω : Cfg ((D₀ + D₁) * (D₀ + D₁)) 2)
    (hω : ω ∉ Set.range (mixedEndpointEdgePhysicalCfg
      (D₀ := D₀) (D₁ := D₁) (mixedEndpointActiveEdgePosition p))) :
    ¬ MixedEndpointOpenInnerActive
      (cyclicCfg (Fin.pos (mixedEndpointActiveEdgeStart p).1) 2
        (mixedEndpointActiveEdgeStart p).1 ω (mixedEndpointActivePhysicalCfg ξ)) := by
  intro hactive
  obtain ⟨ζ, hζ⟩ := (mem_range_mixedEndpointActivePhysicalCfg_iff _).mpr hactive
  apply hω
  refine ⟨(mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ζ).1, ?_⟩
  rw [← extractWindow_mixedEndpointActivePhysicalCfg, hζ,
    extractWindow_cyclicCfg_two (by omega)]

/-- The original physical two-site fiber of the zero-extended active vector
is the smaller-edge isometry applied to the explicit active edge fiber. -/
theorem mixedEndpointActive_edgeFiber_eq_edgeIsometry
    (p : MixedEndpointActiveEdgeSite N)
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1))
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ (N + 1)) :
    cyclicRestrictES (Fin.pos (mixedEndpointActiveEdgeStart p).1) 2
        (mixedEndpointActiveEdgeStart p).1 (mixedEndpointActivePhysicalCfg ξ)
        (mixedEndpointActiveLinearIsometry D₀ D₁ (N + 1) v) =
      mixedEndpointEdgeLinearIsometry D₀ D₁ (mixedEndpointActiveEdgePosition p)
        (mixedEndpointActiveEdgeFiber p v (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).2) := by
  classical
  apply PiLp.ext
  intro ω
  change mixedEndpointActiveLinearIsometry D₀ D₁ (N + 1) v
    (cyclicCfg (Fin.pos (mixedEndpointActiveEdgeStart p).1) 2
      (mixedEndpointActiveEdgeStart p).1 ω (mixedEndpointActivePhysicalCfg ξ)) = _
  by_cases hω : ω ∈ Set.range (mixedEndpointEdgePhysicalCfg
      (D₀ := D₀) (D₁ := D₁) (mixedEndpointActiveEdgePosition p))
  · obtain ⟨η, rfl⟩ := hω
    rw [mixedEndpointActivePhysicalCfg_edgeReplacement,
      mixedEndpointEdgeLinearIsometry_apply_active]
    exact mixedEndpointActiveInclusion_apply_active v _
  · rw [mixedEndpointEdgeLinearIsometry_apply_of_not_mem_range _ _ _ hω]
    exact mixedEndpointActiveInclusion_apply_inactive v _
      (not_active_edgeReplacement_of_not_mem_range p ξ ω hω)

private theorem localInteraction_apply_restriction {d L : ℕ}
    (h : EuclideanSpace ℂ (Cfg d 2) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d 2))
    (hL : 2 ≤ L) (i : Fin L) (v : EuclideanSpace ℂ (Cfg d L)) (σ : Cfg d L) :
    periodicLocalInteractionES h i v σ =
      h (cyclicRestrictES (Fin.pos i) 2 i σ v) (extractWindow 2 i σ) := by
  rw [periodicLocalInteractionES_apply_fiber h hL]
  change h (WithLp.toLp 2 fun ω => v
    ((cyclicActiveBlockConfigEquiv d 2 hL i).symm
      (ω, (cyclicActiveBlockConfigEquiv d 2 hL i σ).2))) (extractWindow 2 i σ) = _
  apply congrArg (fun w : EuclideanSpace ℂ (Cfg d 2) => h w (extractWindow 2 i σ))
  apply PiLp.ext
  intro ω
  change v ((cyclicActiveBlockConfigEquiv d 2 hL i).symm
    (ω, (cyclicActiveBlockConfigEquiv d 2 hL i σ).2)) =
      v (cyclicCfg (Fin.pos i) 2 i ω σ)
  rw [cyclicCfg_eq_join_cyclicActiveBlock hL]

/-- The actual compressed physical term acts by the derived smaller-edge
constraint on the explicit edge fiber, with every other coordinate fixed. -/
theorem mixedEndpointActiveLocalInteraction_apply_edgeFiber
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (p : MixedEndpointActiveEdgeSite N)
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1))
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ (N + 1)) :
    mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p) v ξ =
      mixedEndpointEdgeConstraintES A₀ A₁ (mixedEndpointActiveEdgePosition p)
        (mixedEndpointActiveEdgeFiber p v (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).2)
        (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).1 := by
  rw [mixedEndpointActiveLocalInteraction_apply, localInteraction_apply_restriction _ (by omega),
    extractWindow_mixedEndpointActivePhysicalCfg,
    mixedEndpointActive_edgeFiber_eq_edgeIsometry]
  rw [← mixedEndpointEdgeLinearIsometry_adjoint_apply]
  exact congrArg (fun T =>
    T (mixedEndpointActiveEdgeFiber p v (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).2)
      (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).1)
    (mixedEndpointEdge_compression_eq_constraint A₀ A₁ (mixedEndpointActiveEdgePosition p))

/-- Concrete operator identification: every actual compressed nonwrapping
term is its actual first, interior, or last cropped constraint tensored
with the identity on the explicitly identified spectator coordinates. -/
theorem mixedEndpointActiveLocalInteraction_eq_edgePlacement
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (p : MixedEndpointActiveEdgeSite N) :
    mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p) =
      mixedEndpointActiveEdgePlacement p
        (mixedEndpointEdgeConstraintES A₀ A₁ (mixedEndpointActiveEdgePosition p)) := by
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro ξ
  rw [mixedEndpointActiveLocalInteraction_apply_edgeFiber,
    mixedEndpointActiveEdgePlacement_apply]

/-- The exact coordinate kernel condition for every actual compressed edge.
All edge support spaces are the derived ranges of the cropped actual
boundary maps. -/
theorem mem_ker_mixedEndpointActiveLocalInteraction_iff_edgeFibers
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (p : MixedEndpointActiveEdgeSite N) (v : mixedEndpointActiveSpace D₀ D₁ (N + 1)) :
    v ∈ LinearMap.ker
        (mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p)) ↔
      ∀ s, mixedEndpointActiveEdgeFiber p v s ∈
        mixedEndpointEdgeSupportES A₀ A₁ (mixedEndpointActiveEdgePosition p) := by
  rw [← ker_mixedEndpointEdgeCompression, mixedEndpointEdge_compression_eq_constraint]
  change mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p) v = 0 ↔ _
  constructor
  · intro hv s
    apply PiLp.ext
    intro η
    have h := congrArg (fun w =>
      w ((mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p).symm (η, s))) hv
    rw [mixedEndpointActiveLocalInteraction_apply_edgeFiber] at h
    simpa only [Equiv.apply_symm_apply, PiLp.zero_apply] using h
  · intro hv
    apply PiLp.ext
    intro ξ
    rw [mixedEndpointActiveLocalInteraction_apply_edgeFiber]
    exact congrArg (fun w => w (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).1)
      (hv (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).2)

end

end MPOSymmetry
end MPSTensor
