/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.QuantumDoubleGlobalCheckerboardBlocking
import TNLean.PEPS.KitaevNativeGlobalBlocking

/-!
# Native periodic checkerboard blocking

The elementary tensors on the doubled-period torus are contracted through the
existing torus network. A bijection of the actual fine bonds with four internal
and four crossing bonds per block derives the global blocking identity.
Source: SCP10, arXiv:1001.3807, Section 7.2, lines 2880–2911.

**Scope restriction (untwisted finite-group checkerboard):** The coarse periods are
positive and the fine periods are even. Every bond matrix is the identity.
The physical map below regroups spins; it is not a physical CNOT disentangler.
No statement about twisted sectors or the general-group Bell-pair fixed-point
claim is made. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {G : Type*} [Group G] [DecidableEq G] [Fintype G]
variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "TV" => TorusVertex width height
local notation "FV" => TorusVertex (width * 2) (height * 2)
local notation "PairConfig" => (TV → G × G)
local notation "InnerConfig" => (TV → Fin 4 → G)
local notation "TiledConfig" => (TV × Fin 4 → G)

private def tiledBondEquiv :
    ((PairConfig × PairConfig) × InnerConfig) ≃
      (TiledConfig × TiledConfig) where
  toFun p :=
    (fun q => ![(p.1.1 q.1).1, (p.1.1 q.1).2, p.2 q.1 2, p.2 q.1 0] q.2,
     fun q => ![(p.1.2 q.1).2, p.2 q.1 1, p.2 q.1 3, (p.1.2 q.1).1] q.2)
  invFun q :=
    ((fun v => (q.1 (v, 0), q.1 (v, 1)), fun v => (q.2 (v, 3), q.2 (v, 0))),
      fun v => ![q.1 (v, 3), q.2 (v, 1), q.1 (v, 2), q.2 (v, 2)])
  left_inv p := by
    apply Prod.ext
    · apply Prod.ext <;> funext v <;> rfl
    · funext v i
      fin_cases i <;> rfl
  right_inv q := by
    apply Prod.ext
    · funext p
      rcases p with ⟨v, i⟩
      fin_cases i <;> rfl
    · funext p
      rcases p with ⟨v, i⟩
      fin_cases i <;> rfl

omit [NeZero width] [NeZero height] [Group G] [DecidableEq G] [Fintype G] in
private theorem siteLegs_eq_tiledBonds
    (p : (PairConfig × PairConfig) × InnerConfig)
    (v : TV × Fin 4) :
    quantumDoublePeriodicSiteLegs p.1.1 p.1.2 p.2 v.1 v.2 =
      ![(tiledBondEquiv p).2 v, (tiledBondEquiv p).1 v,
        (tiledBondEquiv p).2 (kitaevTiledDown v),
        (tiledBondEquiv p).1 (kitaevTiledLeft v)] := by
  rcases v with ⟨v, i⟩
  fin_cases i <;> rfl

/-- Clockwise spin orientation: the lower-left and upper-left corners reverse
`r s⁻¹`. Source: SCP10, Section 7.2, lines 2890–2911. -/
def quantumDoublePeriodicReversed (v : FV) : Bool :=
  decide (((kitaevPeriodicTilingEquiv (width := width) (height := height)).symm v).2 = 2 ∨
    ((kitaevPeriodicTilingEquiv (width := width) (height := height)).symm v).2 = 3)

/-- The source's globally alternating elementary tensor on the fine torus.
Both fine periods are even, and the corner orientation is obtained from the
actual disjoint tiling. Source: SCP10, the elementary tensor, lines 2890–2895. -/
def quantumDoublePeriodicElementarySite (σ : FV → G) (v : FV)
    (c : G × G × G × G) : ℂ :=
  quantumDoubleElementaryTensor
    (kitaevPeriodicTurned (width := width) (height := height) v)
    (quantumDoublePeriodicReversed (width := width) (height := height) v)
    ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v)

private theorem nativeNetwork_eq_tiledSum (σ : FV → G) :
    torusBondNetwork
      (quantumDoublePeriodicElementarySite (width := width) (height := height) σ) 1 1 =
      ∑ q : TiledConfig × TiledConfig,
        ∏ p : TV × Fin 4, quantumDoubleElementaryTensor
          (decide (p.2 = 0 ∨ p.2 = 2)) (decide (p.2 = 2 ∨ p.2 = 3))
          ![q.2 p, q.1 p, q.2 (kitaevTiledDown p), q.1 (kitaevTiledLeft p)]
          (σ (kitaevPeriodicTilingEquiv p)) := by
  let E := kitaevPeriodicTilingEquiv (width := width) (height := height)
  let C := E.arrowCongr (Equiv.refl G)
  rw [torusBondNetwork_one, ← Fintype.sum_prod_type', ← (C.prodCongr C).sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  rw [← E.prod_comp]
  apply Finset.prod_congr rfl
  intro p _
  simp [quantumDoublePeriodicElementarySite, kitaevPeriodicTurned,
    quantumDoublePeriodicReversed, C, E, Equiv.arrowCongr_apply,
    ← kitaevPeriodicTilingEquiv_down, ← kitaevPeriodicTilingEquiv_left]

/-- The native fine-torus contraction is the fully expanded elementary
checkerboard contraction in tile coordinates. This equality is derived by a
bijection of all fine bonds, rather than a global-blocking hypothesis.
Source: SCP10, Section 7.2, lines 2890–2904. -/
theorem torusBondNetwork_quantumDoublePeriodicElementarySite_eq_fineCoeff
    (σ : FV → G) :
    torusBondNetwork
      (quantumDoublePeriodicElementarySite (width := width) (height := height) σ) 1 1 =
      quantumDoublePeriodicFineCoeff (fun p => σ (kitaevPeriodicTilingEquiv p)) := by
  rw [nativeNetwork_eq_tiledSum, ← tiledBondEquiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  unfold quantumDoublePeriodicFineCoeff
  apply Finset.sum_congr₂
  intro hb _ vb _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.prod_congr rfl
  intro p _
  rw [siteLegs_eq_tiledBonds ((hb, vb), x) p]

/-- The actual elementary checkerboard PEPS on the doubled-period torus equals
the color-difference PEPS on the coarse torus after grouping its physical spins.
Every internal and crossing bond has been contracted, and no extra scalar or
independence premise is used. Source: SCP10, Section 7.2, lines 2890–2911.
This is the Section 7.2 source example; the Bell-pair fixed-point claim of
Section 6.4 is a separate construction. -/
theorem torusBondNetwork_quantumDoublePeriodicElementarySite_eq_colorNetwork
    (σ : FV → G) :
    torusBondNetwork
      (quantumDoublePeriodicElementarySite (width := width) (height := height) σ) 1 1 =
      torusBondNetwork (fun v c => quantumDoubleBlockColorMatrix
        (fun i => σ (kitaevPeriodicTilingEquiv (v, i)))
        ![c.1, c.2.1, c.2.2.1, c.2.2.2]) 1 1 := by
  rw [torusBondNetwork_quantumDoublePeriodicElementarySite_eq_fineCoeff,
    quantumDoublePeriodicFineCoeff_eq_colorNetwork]

/-- Identify the complete native T network with the source's clockwise K
network, in the exact source tuple ordering. Source: SCP10, lines 2890–2911. -/
theorem torusBondNetwork_quantumDoublePeriodicElementarySite_eq_KNetwork
    (σ : FV → G) :
    torusBondNetwork (quantumDoublePeriodicElementarySite σ) 1 1 =
      torusBondNetwork (fun v c => quantumDoubleKTensor G c.1 c.2.1 c.2.2.1 c.2.2.2
        (finFourArrowEquiv G (fun i => σ (kitaevPeriodicTilingEquiv (v, i))))) 1 1 := by
  rw [torusBondNetwork_quantumDoublePeriodicElementarySite_eq_colorNetwork]
  congr 1
  funext v c
  exact quantumDoubleBlockColorMatrix_eq_KTensor _ _

/-- Regroup the original spins into the exact four-spin physical alphabet of K.
The disjoint periodic tiling, followed by the ordered tuple equivalence, makes
this bijective on the entire ambient physical space. Source: SCP10, lines 2896–2911. -/
def quantumDoublePhysicalBlockingEquiv : (FV → G) ≃ (TV → G × G × G × G) where
  toFun σ v := finFourArrowEquiv G (fun i => σ (kitaevPeriodicTilingEquiv (v, i)))
  invFun τ p :=
    (finFourArrowEquiv G).symm
      (τ ((kitaevPeriodicTilingEquiv (width := width) (height := height)).symm p).1)
      ((kitaevPeriodicTilingEquiv (width := width) (height := height)).symm p).2
  left_inv σ := by
    funext p
    simp only [Equiv.symm_apply_apply, Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv τ := by
    funext v
    apply (finFourArrowEquiv G).symm.injective
    funext i
    simp

/-- The physical Hilbert-space change from fine spins to coarse four-spin
registers. Source: SCP10, physical regrouping in lines 2896–2911. -/
def quantumDoublePhysicalBlockingMatrix : Matrix (TV → G × G × G × G) (FV → G) ℂ :=
  endpointEmbeddingMatrix
    (quantumDoublePhysicalBlockingEquiv (G := G) (width := width) (height := height)).toEmbedding

omit [Group G] in
/-- Physical regrouping preserves inner products on the full Hilbert space. -/
theorem quantumDoublePhysicalBlockingMatrix_isUnitaryBetween :
    Matrix.IsUnitaryBetween
      (quantumDoublePhysicalBlockingMatrix (G := G) (width := width) (height := height)) := by
  apply (endpointEmbeddingMatrix_isIsometry _).isUnitaryBetween_of_card_eq
  exact Fintype.card_congr (quantumDoublePhysicalBlockingEquiv (G := G)).symm

/-- The concrete physical unitary sends the original T network to the actual
clockwise K network, with scalar one. This is a physical transport theorem,
not merely a virtual-boundary permutation. Source: SCP10, lines 2896–2911. -/
theorem quantumDoublePhysicalBlockingMatrix_mulVec_checkerboard :
    (quantumDoublePhysicalBlockingMatrix (G := G) (width := width) (height := height)) *ᵥ
        (fun σ => torusBondNetwork (quantumDoublePeriodicElementarySite σ) 1 1) =
      fun τ => torusBondNetwork (fun v c =>
        quantumDoubleKTensor G c.1 c.2.1 c.2.2.1 c.2.2.2 (τ v)) 1 1 := by
  funext τ
  let E := quantumDoublePhysicalBlockingEquiv (G := G) (width := width) (height := height)
  rw [Matrix.mulVec, dotProduct, ← E.symm.sum_comp]
  simp only [quantumDoublePhysicalBlockingMatrix, endpointEmbeddingMatrix,
    Equiv.toEmbedding_apply, E, Equiv.apply_symm_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [torusBondNetwork_quantumDoublePeriodicElementarySite_eq_KNetwork]
  congr 1
  funext v c
  congr 1
  apply (finFourArrowEquiv G).symm.injective
  funext i
  simp [quantumDoublePhysicalBlockingEquiv]

end TNLean.PEPS
