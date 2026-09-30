/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.ProportionalOverlap
import TNLean.MPS.CanonicalForm.PhaseCover
import TNLean.MPS.CanonicalForm.BNTGrouping
import TNLean.MPS.FundamentalTheorem.UnitaryGauge

/-!
# Periodic blocks in matrix-product-vector phase classes

The proportional fundamental theorem identifies periodic blocks in the same
matrix-product-vector phase class. The existing finite class enumeration thus
retains each original block with its bond dimension, period, unit phase, and
unitary similarity to its representative when the blocks are left-canonical.
These are the blockwise data for the grouping in arXiv:1708.00029,
`def:repeated` and `eq:bdnr`, lines 276–305.
-/

open scoped BigOperators Matrix

namespace MPSTensor

/-- Proportional periodic blocks are repeated, without requiring a prescribed
power law for the proportionality scalars. This is the one-block case of
arXiv:1708.00029, `thm:bd`, lines 613–623. -/
theorem hetRepeatedBlocks_of_nonzeroProportionalMPV₂ {d D E m n : ℕ}
    {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : IsSpectrallyPeriodic m A) (hB : IsSpectrallyPeriodic n B)
    (hProp : NonzeroProportionalMPV₂ A B) : HetRepeatedBlocks A B := by
  let P := trivialSectorDecomp (fun _ : Fin 1 ↦ (1 : ℂ)) (fun _ ↦ A) (fun _ ↦ one_ne_zero)
  let Q := trivialSectorDecomp (fun _ : Fin 1 ↦ (1 : ℂ)) (fun _ ↦ B) (fun _ ↦ one_ne_zero)
  have hP (N : ℕ) (σ : Fin N → Fin d) : mpv P.toTensor σ = mpv A σ := by
    rw [P.mpv_toTensor_eq_sum_coeff]
    change (∑ _ : Fin 1, (∑ _ : Fin 1, (1 : ℂ) ^ N) * mpv A σ) = _
    simp
  have hQ (N : ℕ) (σ : Fin N → Fin d) : mpv Q.toTensor σ = mpv B σ := by
    rw [Q.mpv_toTensor_eq_sum_coeff]
    change (∑ _ : Fin 1, (∑ _ : Fin 1, (1 : ℂ) ^ N) * mpv B σ) = _
    simp
  have hm := fundamentalTheorem_periodic_proportional_sectorDecomposition P Q
    (fun _ ↦ m) (fun _ ↦ n) (fun _ ↦ hA) (fun _ ↦ hB)
    (fun i j hij ↦ (hij (Subsingleton.elim (α := Fin 1) i j)).elim)
    (fun i j hij ↦ (hij (Subsingleton.elim (α := Fin 1) i j)).elim) ?_
  · obtain ⟨_, _, he⟩ := hm
    exact (he (0 : Fin 1)).2
  · intro N hN
    obtain ⟨c, hc, he⟩ := hProp N hN
    exact ⟨c, hc, fun σ ↦ by simpa only [hP, hQ] using he σ⟩

/-- Periodic blocks in one matrix-product-vector phase class are repeated.
Source: arXiv:1708.00029, `thm:bd`, lines 613–623. -/
theorem MPVBlockPhaseEquiv.hetRepeatedBlocks_of_isSpectrallyPeriodic {d D E m n : ℕ}
    {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : IsSpectrallyPeriodic m A) (hB : IsSpectrallyPeriodic n B)
    (h : MPVBlockPhaseEquiv A B) : HetRepeatedBlocks A B := by
  obtain ⟨ζ, hζ, he⟩ := h
  exact (hetRepeatedBlocks_of_nonzeroProportionalMPV₂ hB hA (fun N hN ↦
    ⟨ζ ^ N, pow_ne_zero N hζ, he N hN⟩)).symm

/-- Left-canonical periodic blocks have spectral radius one, as used in
arXiv:1708.00029, lines 248–261 and 313–332. -/
theorem IsPeriodic.isSpectrallyPeriodic {d D m : ℕ} {A : MPSTensor d D} (hA : IsPeriodic m A) :
    IsSpectrallyPeriodic m A := by
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  have hC := Kraus.isChannel_mapLM A hA.leftCanonical
  exact ⟨hA.irreducible, hC.pos.spectralRadius_eq_one_of_tracePreserving hC.tp,
    hA.period_pos, hA.peripheral_eq⟩

/-- Repeated left-canonical periodic blocks admit a unitary bond similarity.
Source: arXiv:1708.00029, the paragraph after `thm:bd`, line 625. -/
theorem exists_unitary_conj_of_isPeriodic_of_hetRepeatedBlocks {d D E m n : ℕ}
    {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : IsPeriodic m A) (hB : IsPeriodic n B) (h : HetRepeatedBlocks A B) :
    ∃ hd : D = E, ∃ ξ : ℂ, ∃ U : Matrix.unitaryGroup (Fin E) ℂ,
      ‖ξ‖ = 1 ∧ ∀ i, (cast (congr_arg (MPSTensor d) hd) A) i =
        ξ • ((U : Matrix (Fin E) (Fin E) ℂ) * B i * (U : Matrix (Fin E) (Fin E) ℂ)ᴴ) := by
  obtain ⟨hd, ξ, X, hξ, hrel⟩ := h
  subst E
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨U, _, hU⟩ :=
    exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible X ξ
      (Complex.ne_zero_of_norm_eq_one hξ) hrel hB.leftCanonical hA.leftCanonical
      hB.irreducible hA.irreducible
  exact ⟨rfl, ξ, U, hξ, hU⟩

/-- Representatives of different matrix-product-vector phase classes are not
repeated blocks, as required by arXiv:1708.00029, `eq:bdnr`, lines 286–305. -/
theorem MPVPhaseClassData.not_hetRepeatedBlocks {d r : ℕ} {dim : Fin r → ℕ}
    {blocks : (k : Fin r) → MPSTensor d (dim k)} (classes : MPVPhaseClassData blocks)
    (i j : Fin classes.g) (hij : i ≠ j) :
    ¬ HetRepeatedBlocks (blocks (classes.repr i)) (blocks (classes.repr j)) := by
  rintro ⟨hd, hrep⟩
  obtain ⟨ξ, Y, hξ, hrel⟩ := hrep
  exact classes.blocks_not_equiv i j hij hd
    (gaugePhaseEquiv_symm_same_dim ⟨Y, ξ, Complex.ne_zero_of_norm_eq_one hξ, hrel⟩)

/-- Every enumerated periodic block has the dimension and period of its
representative and is a unit phase times a unitary conjugate of it. The original
block remains identified by `classes.enum j q`.
Source: arXiv:1708.00029, `eq:bdnr`, lines 286–305, and line 625. -/
theorem MPVPhaseClassData.periodic_unitary_match {d r : ℕ} {dim : Fin r → ℕ}
    {blocks : (k : Fin r) → MPSTensor d (dim k)} (classes : MPVPhaseClassData blocks)
    (period : Fin r → ℕ) (hper : ∀ k, IsPeriodic (period k) (blocks k))
    (j : Fin classes.g) (q : Fin (classes.copies j)) :
    period (classes.enum j q) = period (classes.repr j) ∧
    ∃ hd : dim (classes.enum j q) = dim (classes.repr j),
      ∃ ξ : ℂ, ∃ U : Matrix.unitaryGroup (Fin (dim (classes.repr j))) ℂ,
        ‖ξ‖ = 1 ∧ ∀ i,
          (cast (congr_arg (MPSTensor d) hd) (blocks (classes.enum j q))) i =
            ξ • ((U : Matrix _ _ ℂ) * blocks (classes.repr j) i * (U : Matrix _ _ ℂ)ᴴ) := by
  have hrep := (MPVBlockPhaseEquiv.hetRepeatedBlocks_of_isSpectrallyPeriodic
    (hper _).isSpectrallyPeriodic (hper _).isSpectrallyPeriodic (classes.enum_phase j q)).symm
  exact ⟨(hper _).isSpectrallyPeriodic.period_eq_of_hetRepeatedBlocks
    (hper _).isSpectrallyPeriodic hrep,
    exists_unitary_conj_of_isPeriodic_of_hetRepeatedBlocks (hper _) (hper _) hrep⟩

end MPSTensor
