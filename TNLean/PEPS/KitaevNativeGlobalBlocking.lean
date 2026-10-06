/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.KitaevGlobalCheckerboardBlocking

/-!
# Native periodic checkerboard blocking

The elementary tensors on the doubled-period torus are contracted through the
existing torus network. A bijection of the actual fine bonds with four internal
and four crossing bonds per block derives the global blocking identity.
Source: SCP10, arXiv:1001.3807, Section 7.1, lines 2718–2827.

**Scope restriction (untwisted binary checkerboard):** The coarse periods are
positive and the fine periods are even. Every bond matrix is the identity.
The physical map below regroups spins; it is not a physical CNOT disentangler.
No statement about twisted sectors or the general-group Bell-pair fixed-point
claim is made. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "TV" => TorusVertex width height
local notation "FV" => TorusVertex (width * 2) (height * 2)
local notation "PairConfig" => (TV → KitaevBit × KitaevBit)
local notation "InnerConfig" => (TV → Fin 4 → KitaevBit)
local notation "TiledConfig" => (TV × Fin 4 → KitaevBit)

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

omit [NeZero width] [NeZero height] in
private theorem siteLegs_eq_tiledBonds
    (p : (PairConfig × PairConfig) × InnerConfig)
    (v : TV × Fin 4) :
    kitaevPeriodicSiteLegs p.1.1 p.1.2 p.2 v.1 v.2 =
      ![(tiledBondEquiv p).2 v, (tiledBondEquiv p).1 v,
        (tiledBondEquiv p).2 (kitaevTiledDown v),
        (tiledBondEquiv p).1 (kitaevTiledLeft v)] := by
  rcases v with ⟨v, i⟩
  fin_cases i <;> rfl

/-- The alternating checkerboard orientation on the even-period fine torus.
Source: SCP10, elementary tensor orientations in Section 7.1. -/
def kitaevPeriodicTurned (v : FV) : Bool :=
  decide (((kitaevPeriodicTilingEquiv (width := width) (height := height)).symm v).2 = 0 ∨
    ((kitaevPeriodicTilingEquiv (width := width) (height := height)).symm v).2 = 2)

/-- Horizontal fine-lattice neighbors have opposite orientations, including
at the periodic seam. -/
theorem kitaevPeriodicTurned_right (v : FV) :
    kitaevPeriodicTurned (width := width) (height := height) (v.1 + 1, v.2) =
      !kitaevPeriodicTurned (width := width) (height := height) v := by
  obtain ⟨p, rfl⟩ := (kitaevPeriodicTilingEquiv (width := width) (height := height)).surjective v
  rw [← kitaevPeriodicTilingEquiv_right]
  simp only [kitaevPeriodicTurned, Equiv.symm_apply_apply]
  rcases p with ⟨v, i⟩
  fin_cases i <;> rfl

/-- Vertical fine-lattice neighbors have opposite orientations, including
at the periodic seam. -/
theorem kitaevPeriodicTurned_up (v : FV) :
    kitaevPeriodicTurned (width := width) (height := height) (v.1, v.2 + 1) =
      !kitaevPeriodicTurned (width := width) (height := height) v := by
  obtain ⟨p, rfl⟩ := (kitaevPeriodicTilingEquiv (width := width) (height := height)).surjective v
  rw [← kitaevPeriodicTilingEquiv_up]
  simp only [kitaevPeriodicTurned, Equiv.symm_apply_apply]
  rcases p with ⟨v, i⟩
  fin_cases i <;> rfl

/-- The source's globally alternating elementary tensor on the fine torus.
Both fine periods are even, and the corner orientation is obtained from the
actual disjoint tiling. Source: SCP10, `eq:ex:kitaev-tens`, lines 2718–2748. -/
def kitaevPeriodicElementarySite (σ : FV → KitaevBit) (v : FV)
    (c : KitaevBit × KitaevBit × KitaevBit × KitaevBit) : ℂ :=
  kitaevElementaryTensor
    (kitaevPeriodicTurned (width := width) (height := height) v)
    ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v)

private theorem nativeNetwork_eq_tiledSum (σ : FV → KitaevBit) :
    torusBondNetwork (kitaevPeriodicElementarySite (width := width) (height := height) σ) 1 1 =
      ∑ q : TiledConfig × TiledConfig,
        ∏ p : TV × Fin 4, kitaevElementaryTensor (decide (p.2 = 0 ∨ p.2 = 2))
          ![q.2 p, q.1 p, q.2 (kitaevTiledDown p), q.1 (kitaevTiledLeft p)]
          (σ (kitaevPeriodicTilingEquiv p)) := by
  let E := kitaevPeriodicTilingEquiv (width := width) (height := height)
  let C := E.arrowCongr (Equiv.refl KitaevBit)
  rw [torusBondNetwork_one, ← Fintype.sum_prod_type', ← (C.prodCongr C).sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  rw [← E.prod_comp]
  apply Finset.prod_congr rfl
  intro p _
  simp [kitaevPeriodicElementarySite, kitaevPeriodicTurned, C, E, Equiv.arrowCongr_apply,
    ← kitaevPeriodicTilingEquiv_down, ← kitaevPeriodicTilingEquiv_left]

/-- The native fine-torus contraction is the fully expanded elementary
checkerboard contraction in tile coordinates. This equality is derived by a
bijection of all fine bonds, rather than a global-blocking hypothesis.
Source: SCP10, Section 7.1, lines 2755–2794. -/
theorem torusBondNetwork_kitaevPeriodicElementarySite_eq_fineCoeff
    (σ : FV → KitaevBit) :
    torusBondNetwork (kitaevPeriodicElementarySite (width := width) (height := height) σ) 1 1 =
      kitaevPeriodicFineCoeff (fun p => σ (kitaevPeriodicTilingEquiv p)) := by
  rw [nativeNetwork_eq_tiledSum, ← tiledBondEquiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  unfold kitaevPeriodicFineCoeff
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
independence premise is used. Source: SCP10, Section 7.1, lines 2755–2827.
This is the binary example, not the general-group Bell-pair fixed-point claim. -/
theorem torusBondNetwork_kitaevPeriodicElementarySite_eq_colorNetwork
    (σ : FV → KitaevBit) :
    torusBondNetwork (kitaevPeriodicElementarySite (width := width) (height := height) σ) 1 1 =
      torusBondNetwork (fun v c => kitaevBlockColorMatrix
        (fun i => σ (kitaevPeriodicTilingEquiv (v, i)))
        ![c.1, c.2.1, c.2.2.1, c.2.2.2]) 1 1 := by
  rw [torusBondNetwork_kitaevPeriodicElementarySite_eq_fineCoeff,
    kitaevPeriodicFineCoeff_eq_colorNetwork]

/-- Identify the global coarse state with the existing dual toric-code tensor,
including its cyclic physical ordering. Source: SCP10, equation
`eq:ex:kitaev-colordiff-rep`, lines 2809–2827. -/
theorem torusBondNetwork_kitaevPeriodicElementarySite_eq_quantumDoubleNetwork
    (σ : FV → KitaevBit) :
    torusBondNetwork (kitaevPeriodicElementarySite (width := width) (height := height) σ) 1 1 =
      torusBondNetwork (fun v (c : ToricCodeGroup × ToricCodeGroup ×
          ToricCodeGroup × ToricCodeGroup) =>
        quantumDoubleDualTensor ToricCodeGroup c.1 c.2.1 c.2.2.1 c.2.2.2
          (Multiplicative.ofAdd (σ (kitaevPeriodicTilingEquiv (v, 3))),
           Multiplicative.ofAdd (σ (kitaevPeriodicTilingEquiv (v, 0))),
           Multiplicative.ofAdd (σ (kitaevPeriodicTilingEquiv (v, 1))),
           Multiplicative.ofAdd (σ (kitaevPeriodicTilingEquiv (v, 2))))) 1 1 := by
  rw [torusBondNetwork_kitaevPeriodicElementarySite_eq_colorNetwork,
    torusBondNetwork_one, torusBondNetwork_one]
  apply Finset.sum_congr₂
  intro hb _ vb _
  apply Finset.prod_congr rfl
  intro v _
  exact kitaevBlockColorMatrix_eq_quantumDoubleDualTensor
    (fun i => σ (kitaevPeriodicTilingEquiv (v, i)))
    ![vb v, hb v, vb (v.1, v.2 - 1), hb (v.1 - 1, v.2)]

/-- Regroup fine physical spins into one four-spin register per coarse site.
This is bijective because the 2×2 blocks form a disjoint covering of the fine
torus. Source: SCP10, Section 7.1, lines 2755–2827. -/
def kitaevPhysicalBlockingEquiv : (FV → KitaevBit) ≃ (TV → KitaevBlockSpins) where
  toFun σ v i := σ (kitaevPeriodicTilingEquiv (v, i))
  invFun τ p :=
    τ ((kitaevPeriodicTilingEquiv (width := width) (height := height)).symm p).1
      ((kitaevPeriodicTilingEquiv (width := width) (height := height)).symm p).2
  left_inv σ := by funext p; simp
  right_inv τ := by funext v i; simp

/-- The physical change of coordinates from fine spins to coarse four-spin
registers. Source: SCP10, physical regrouping in the four-site blocking of Section 7.1,
lines 2755–2827. -/
def kitaevPhysicalBlockingMatrix : Matrix (TV → KitaevBlockSpins) (FV → KitaevBit) ℂ :=
  endpointEmbeddingMatrix
    (kitaevPhysicalBlockingEquiv (width := width) (height := height)).toEmbedding

/-- Physical regrouping preserves the complete Hilbert-space inner product,
not just the one checkerboard state. -/
theorem kitaevPhysicalBlockingMatrix_isIsometry :
    Matrix.IsIsometry (kitaevPhysicalBlockingMatrix (width := width) (height := height)) :=
  endpointEmbeddingMatrix_isIsometry _

/-- The adjoint physical regrouping also preserves inner products; the map
therefore is a unitary identification of the fine and blocked physical spaces. -/
theorem kitaevPhysicalBlockingMatrix_conjTranspose_isIsometry :
    Matrix.IsIsometry
      (kitaevPhysicalBlockingMatrix (width := width) (height := height)).conjTranspose := by
  have h : (kitaevPhysicalBlockingMatrix (width := width) (height := height)).conjTranspose =
      endpointEmbeddingMatrix
        (kitaevPhysicalBlockingEquiv (width := width) (height := height)).symm.toEmbedding := by
    ext σ τ
    simp [kitaevPhysicalBlockingMatrix, endpointEmbeddingMatrix, Matrix.conjTranspose_apply,
      Equiv.eq_symm_apply, eq_comm]
  rw [h]
  exact endpointEmbeddingMatrix_isIsometry _

/-- A unitary physical regrouping sends the complete fine checkerboard state
to the coarse color-difference PEPS, with all coefficients determined by the
native fine-torus contraction. Source: SCP10, Section 7.1, lines 2755–2827.
The binary product-register reduction is distinct from the general-group
Bell-pair fixed-point statement of Observation 6.6. -/
theorem kitaevPhysicalBlockingMatrix_mulVec_checkerboard :
    (kitaevPhysicalBlockingMatrix (width := width) (height := height)) *ᵥ
        (fun σ => torusBondNetwork
          (kitaevPeriodicElementarySite (width := width) (height := height) σ) 1 1) =
      fun τ => torusBondNetwork (fun v c => kitaevBlockColorMatrix (τ v)
        ![c.1, c.2.1, c.2.2.1, c.2.2.2]) 1 1 := by
  funext τ
  let E := kitaevPhysicalBlockingEquiv (width := width) (height := height)
  rw [Matrix.mulVec, dotProduct]
  rw [← E.symm.sum_comp]
  simp only [kitaevPhysicalBlockingMatrix, endpointEmbeddingMatrix,
    Equiv.toEmbedding_apply, E, Equiv.apply_symm_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [torusBondNetwork_kitaevPeriodicElementarySite_eq_colorNetwork]
  simp [kitaevPhysicalBlockingEquiv]

end TNLean.PEPS
