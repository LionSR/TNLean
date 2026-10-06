/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.RectangularWindowMixing

/-!
# Actual varying-bond local-window regression

The actual original tensor ring has bond dimensions `1,2,1` and a singular density
on its two-dimensional cut. Width-two windows on the three-site ring leave a
nonempty remainder. Compatible references and the block estimate are derived,
not supplied. This uses the same elementary tensor as the rectangular compiler
regression, but has only the lightweight local-window imports.
-/

open Matrix MPSTensor VaryingBondChain MPSPreparation Fin.NatCast
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace RectangularWindowMixingRegression

/-- A genuinely varying ring with dimensions `1,2,1`, including a one-dimensional cut. -/
abbrev ring : VaryingBondChain 2 2 3 where
  bondDim := ![1, 2, 1]
  bondDim_le := by decide
  tensor _ s a b := if a.val = 0 ∧ b.val = s.val then 1 else 0

abbrev density (i : Fin 3) : Matrix (Fin (ring.bondDim i)) (Fin (ring.bondDim i)) ℂ :=
  Matrix.of fun a b => if a.val = 0 ∧ b.val = 0 then 1 else 0

theorem density_pos (i : Fin 3) : (density i).PosSemidef := by
  have h : density i = Matrix.vecMulVec (fun a => if a.val = 0 then (1 : ℂ) else 0)
      (star (fun a => if a.val = 0 then (1 : ℂ) else 0)) := by
    ext a b
    simp [density, Matrix.vecMulVec, ite_and]
    split_ifs <;> rfl
  rw [h]
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem density_trace (i : Fin 3) : (density i).trace = 1 := by
  have hpos : 0 < ring.bondDim i := by fin_cases i <;> decide
  let z : Fin (ring.bondDim i) := ⟨0, hpos⟩
  simp only [density, Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [Finset.sum_eq_single z]
  · simp [z]
  · intro j _ hj
    have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simp [hj0]
  · simp

/-- All three actual rectangular site maps are exact reset maps. -/
theorem site_reset (i : Fin 3) :
    Matrix.rectangularKrausMap (ring.tensor i) = Matrix.tracePrepareMap (density i) := by
  fin_cases i <;> first
    | change Matrix.rectangularKrausMap
        (fun (s : Fin 2) => Matrix.of fun (a : Fin 1) (b : Fin 2) =>
          if a.val = 0 ∧ b.val = s.val then (1 : ℂ) else 0) =
          Matrix.tracePrepareMap (Matrix.of fun (a b : Fin 1) =>
            if a.val = 0 ∧ b.val = 0 then (1 : ℂ) else 0)
    | change Matrix.rectangularKrausMap
        (fun (s : Fin 2) => Matrix.of fun (a : Fin 2) (b : Fin 1) =>
          if a.val = 0 ∧ b.val = s.val then (1 : ℂ) else 0) =
          Matrix.tracePrepareMap (Matrix.of fun (a b : Fin 2) =>
            if a.val = 0 ∧ b.val = 0 then (1 : ℂ) else 0)
    | change Matrix.rectangularKrausMap
        (fun (s : Fin 2) => Matrix.of fun (a : Fin 1) (b : Fin 1) =>
          if a.val = 0 ∧ b.val = s.val then (1 : ℂ) else 0) =
          Matrix.tracePrepareMap (Matrix.of fun (a b : Fin 1) =>
            if a.val = 0 ∧ b.val = 0 then (1 : ℂ) else 0)
  all_goals
    apply LinearMap.ext
    intro X
    erw [Matrix.tracePrepareMap_apply]
    dsimp only [Matrix.rectangularKrausMap, LinearMap.coe_mk, AddHom.coe_mk]
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [ring, density, Matrix.vecMulVec, Matrix.of_apply, Pi.smul_apply,
        smul_eq_mul, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]


theorem site_cptp (i : Fin 3) : IsKrausCPTP (Matrix.rectangularKrausMap (ring.tensor i)) := by
  rw [site_reset]
  exact Matrix.tracePrepareMap_isKrausCPTP _ (density_pos i) (density_trace i)

theorem window_minorization (a : ℕ) (ha : a + 2 ≤ 3) :
    ∃ τ : Matrix (Fin (bondDimAt ring a)) (Fin (bondDimAt ring a)) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
      ChoiRectangular.choiMatrix
        (Matrix.channelInterval (siteTransferAt ring) a (a + 2) (Nat.le_add_right a 2)) ≥
          ((1 : ℂ) / bondDimAt ring (a + 2)) •
            (τ ⊗ₖ (1 : Matrix (Fin (bondDimAt ring (a + 2)))
              (Fin (bondDimAt ring (a + 2))) ℂ)) := by
  refine ⟨density (a : Fin 3), density_pos _, density_trace _, ?_⟩
  have heq : Matrix.channelInterval (siteTransferAt ring) a (a + 2)
      (Nat.le_add_right a 2) =
        Matrix.tracePrepareMap (α := Fin (bondDimAt ring (a + 2)))
          (β := Fin (bondDimAt ring a)) (density (a : Fin 3)) := by
    rw [Matrix.channelInterval_succ _ (Nat.le_add_right a 1), Matrix.channelInterval_single]
    have ha' : a = 0 ∨ a = 1 := by omega
    rcases ha' with rfl | rfl
    · ext X : 1
      change Matrix.rectangularKrausMap (ring.tensor 0)
        (Matrix.rectangularKrausMap (ring.tensor 1) X) =
          Matrix.tracePrepareMap (density 0) X
      rw [site_reset, site_reset]
      erw [Matrix.tracePrepareMap_apply, Matrix.tracePrepareMap_apply,
        Matrix.tracePrepareMap_apply, Matrix.trace_smul, density_trace, smul_eq_mul, mul_one]
      rfl
    · ext X : 1
      change Matrix.rectangularKrausMap (ring.tensor 1)
        (Matrix.rectangularKrausMap (ring.tensor 2) X) =
          Matrix.tracePrepareMap (density 1) X
      rw [site_reset, site_reset]
      erw [Matrix.tracePrepareMap_apply, Matrix.tracePrepareMap_apply,
        Matrix.tracePrepareMap_apply, Matrix.trace_smul, density_trace, smul_eq_mul, mul_one]
      rfl
  rw [heq]
  exact le_of_eq (Matrix.choiMatrix_tracePrepareMap
    (bondDimAt ring (a + 2)) (bondDimAt ring a) (density (a : Fin 3))).symm

example : ring.bondDim 0 = 1 ∧ ring.bondDim 1 = 2 ∧ ring.bondDim 2 = 1 := by decide

example : (density 1).det = 0 := by
  change ( (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)).det = 0
  norm_num [Matrix.det_fin_two]

/-- A whole-ring block retains the shorter remainder and has zero residual error. -/
example : ∃ σ : ∀ i : Fin 3, Matrix (Fin (ring.bondDim i)) (Fin (ring.bondDim i)) ℂ,
    (∀ i, (σ i).PosSemidef ∧ (σ i).trace = 1) ∧
    ‖Matrix.linearMapMatrix (Matrix.rectangularKrausMap
        (rectangularBlockTensor ring (by simp : ∑ _ : Fin 1, 3 = 3) 0) -
      Matrix.tracePrepareMap (α := Fin (rightBond ring (fun _ : Fin 1 => 3) 0))
        (β := Fin (blockBondDim ring (fun _ : Fin 1 => 3) 0 0))
        (σ (blockOffset (fun _ : Fin 1 => 3) (0 : Fin 1).val : Fin 3)))‖ ≤ 0 := by
  obtain ⟨σ, hσ, hm⟩ := exists_rectangular_block_mixing_of_window_domination ring
    (by intro i; fin_cases i <;> decide) site_cptp 2 (by decide) 1 le_rfl
    (fun a ha => by simpa only [Complex.ofReal_one] using window_minorization a ha)
  refine ⟨σ, hσ, ?_⟩
  simpa only [sub_self, pow_one, mul_zero,
    show 3 / 2 = 1 by decide] using hm (fun _ : Fin 1 => 3) (by simp) 0 (by decide)

end RectangularWindowMixingRegression

/-!
## Two-site mixing without one-site minorization

The actual three-site tensor ring has bond dimensions `2,3,2` and physical dimension
three. Its middle site is the isometry `|0⟩ ↦ |1⟩`, `|1⟩ ↦ |2⟩`; the other sites
reset to `|0⟩`. Both nonwrapping two-site windows are exact resets, with distinct
singular output references, although the isometric site admits no positive
trace-reset minorization. The whole-ring block exercises a one-site remainder.
-/

namespace RectangularTwoSiteWindowRegression

/-- Three original rectangular tensors, including an isometric middle site. -/
abbrev ring : VaryingBondChain 3 3 3 where
  bondDim := ![2, 3, 2]
  bondDim_le := by decide
  tensor i s a b := if i.val = 1 then
      if s.val = 0 ∧ a.val = b.val + 1 then 1 else 0
    else if a.val = 0 ∧ b.val = s.val then 1 else 0

abbrev density (i : Fin 3) : Matrix (Fin (ring.bondDim i)) (Fin (ring.bondDim i)) ℂ :=
  Matrix.diagonal (fun a => if a.val = (if i.val = 1 then 1 else 0) then 1 else 0)

theorem density_pos (i : Fin 3) : (density i).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro j
  dsimp
  split_ifs <;> positivity

theorem density_trace (i : Fin 3) : (density i).trace = 1 := by
  rw [Matrix.trace_diagonal]
  let z : Fin (ring.bondDim i) := ⟨if i.val = 1 then 1 else 0, by
    fin_cases i <;> decide⟩
  rw [Finset.sum_eq_single z]
  · simp [z]
  · intro j _ hj
    have hjv : j.val ≠ (if i.val = 1 then 1 else 0) := fun h => hj (Fin.ext h)
    simp [hjv]
  · simp

/-- The middle-site isometry preserves the two orthogonal input basis vectors. -/
abbrev embedding : Matrix (Fin 3) (Fin 2) ℂ :=
  Matrix.of fun a b => if a.val = b.val + 1 then 1 else 0

theorem embedding_isometry : embeddingᴴ * embedding = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

/-- The other two sites are reset channels on their actual input spaces. -/
theorem site_reset (i : Fin 3) (hi : i = 0 ∨ i = 2) :
    Matrix.rectangularKrausMap (ring.tensor i) = Matrix.tracePrepareMap (density i) := by
  rcases hi with rfl | rfl <;> first
    | change Matrix.rectangularKrausMap
        (fun (s : Fin 3) => Matrix.of fun (a : Fin 2) (b : Fin 3) =>
          if a.val = 0 ∧ b.val = s.val then (1 : ℂ) else 0) =
          Matrix.tracePrepareMap (Matrix.diagonal (fun (a : Fin 2) =>
            if a.val = 0 then (1 : ℂ) else 0))
    | change Matrix.rectangularKrausMap
        (fun (s : Fin 3) => Matrix.of fun (a : Fin 2) (b : Fin 2) =>
          if a.val = 0 ∧ b.val = s.val then (1 : ℂ) else 0) =
          Matrix.tracePrepareMap (Matrix.diagonal (fun (a : Fin 2) =>
            if a.val = 0 then (1 : ℂ) else 0))
  all_goals
    apply LinearMap.ext
    intro X
    erw [Matrix.tracePrepareMap_apply]
    dsimp only [Matrix.rectangularKrausMap, LinearMap.coe_mk, AddHom.coe_mk]
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [Matrix.diagonal, Matrix.of_apply, Pi.smul_apply,
        smul_eq_mul, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

theorem site_one_isometry :
    Matrix.rectangularKrausMap (ring.tensor 1) = singleKrausMap embedding := by
  change Matrix.rectangularKrausMap
    (fun (s : Fin 3) => Matrix.of fun (a : Fin 3) (b : Fin 2) =>
      if s.val = 0 ∧ a.val = b.val + 1 then (1 : ℂ) else 0) = singleKrausMap embedding
  apply LinearMap.ext
  intro X
  rw [singleKrausMap_apply]
  dsimp only [Matrix.rectangularKrausMap, LinearMap.coe_mk, AddHom.coe_mk]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [ring, embedding, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem site_cptp (i : Fin 3) : IsKrausCPTP (Matrix.rectangularKrausMap (ring.tensor i)) := by
  by_cases hi : i = 1
  · subst i
    rw [site_one_isometry]
    exact singleKrausMap_isKrausCPTP embedding embedding_isometry
  · rw [site_reset i (by fin_cases i <;> simp_all)]
    exact Matrix.tracePrepareMap_isKrausCPTP _ (density_pos i) (density_trace i)

theorem embedding_density : singleKrausMap embedding (density 2) = density 1 := by
  change singleKrausMap embedding
    (Matrix.diagonal (fun (a : Fin 2) => if a.val = 0 then (1 : ℂ) else 0)) =
    Matrix.diagonal (fun (a : Fin 3) => if a.val = 1 then (1 : ℂ) else 0)
  rw [singleKrausMap_apply]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [embedding, Matrix.of_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal, Fin.sum_univ_succ]

/-- Both nonwrapping two-site windows reset exactly, even though one site is isometric. -/
theorem window_reset (a : ℕ) (ha : a + 2 ≤ 3) :
    Matrix.channelInterval (siteTransferAt ring) a (a + 2) (Nat.le_add_right a 2) =
      Matrix.tracePrepareMap (α := Fin (bondDimAt ring (a + 2)))
        (β := Fin (bondDimAt ring a)) (density (a : Fin 3)) := by
  rw [Matrix.channelInterval_succ _ (Nat.le_add_right a 1), Matrix.channelInterval_single]
  have ha' : a = 0 ∨ a = 1 := by omega
  rcases ha' with rfl | rfl
  · ext X : 1
    change Matrix.rectangularKrausMap (ring.tensor 0)
      (Matrix.rectangularKrausMap (ring.tensor 1) X) = Matrix.tracePrepareMap (density 0) X
    rw [site_reset 0 (Or.inl rfl)]
    erw [Matrix.tracePrepareMap_apply, Matrix.tracePrepareMap_apply, (site_cptp 1).trace_map]
    rfl
  · ext X : 1
    change Matrix.rectangularKrausMap (ring.tensor 1)
      (Matrix.rectangularKrausMap (ring.tensor 2) X) = Matrix.tracePrepareMap (density 1) X
    rw [site_one_isometry, site_reset 2 (Or.inr rfl)]
    erw [Matrix.tracePrepareMap_apply, Matrix.tracePrepareMap_apply, map_smul,
      embedding_density]
    rfl

theorem window_minorization (a : ℕ) (ha : a + 2 ≤ 3) :
    ∃ τ : Matrix (Fin (bondDimAt ring a)) (Fin (bondDimAt ring a)) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
      ChoiRectangular.choiMatrix
        (Matrix.channelInterval (siteTransferAt ring) a (a + 2) (Nat.le_add_right a 2)) ≥
          ((1 : ℂ) / bondDimAt ring (a + 2)) •
            (τ ⊗ₖ (1 : Matrix (Fin (bondDimAt ring (a + 2)))
              (Fin (bondDimAt ring (a + 2))) ℂ)) := by
  refine ⟨density (a : Fin 3), density_pos _, density_trace _, ?_⟩
  rw [window_reset a ha]
  exact le_of_eq (Matrix.choiMatrix_tracePrepareMap
    (bondDimAt ring (a + 2)) (bondDimAt ring a) (density (a : Fin 3))).symm

/-- The isometric site has no positive reset minorization, for any density reference. -/
theorem no_one_site_minorization (τ : Matrix (Fin 3) (Fin 3) ℂ)
    (hτ : τ.PosSemidef) (hτtr : τ.trace = 1) (η : ℝ) (hη : 0 < η) :
    ¬ ChoiRectangular.choiMatrix (Matrix.rectangularKrausMap (ring.tensor 1)) ≥
      ((η : ℂ) / 2) • (τ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  intro h
  rw [site_one_isometry] at h
  have hR := Matrix.isKrausCP_sub_smul_tracePrepareMap_of_choi_domination
    (singleKrausMap embedding) τ η h
  have hdiag (a : Fin 3) : (τ a a).re = 0 := by
    have hnonneg : 0 ≤ (τ a a).re := (Complex.nonneg_iff.mp hτ.diag_nonneg).1
    let j : Fin 2 := if a = 1 then 1 else 0
    have hX : (Matrix.single j j (1 : ℂ)).PosSemidef := by
      rw [← Matrix.diagonal_single]
      apply Matrix.PosSemidef.diagonal
      intro k
      by_cases hkj : k = j <;> simp [hkj]
    have hd := (hR.map_posSemidef hX).diag_nonneg (i := a)
    have hre := (Complex.nonneg_iff.mp hd).1
    fin_cases a <;>
      norm_num [j, singleKrausMap_apply, embedding, Matrix.of_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_succ, Matrix.single,
        LinearMap.sub_apply, LinearMap.smul_apply, Matrix.tracePrepareMap_apply,
        Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
        Complex.mul_re] at hre hnonneg ⊢ <;> nlinarith
  have htr := congrArg Complex.re hτtr
  have h0 := hdiag 0
  have h1 := hdiag 1
  have h2 := hdiag 2
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_succ] at htr
  linarith

example : ring.bondDim 0 = 2 ∧ ring.bondDim 1 = 3 ∧ ring.bondDim 2 = 2 := by decide

example : (density 0).det = 0 ∧ (density 1).det = 0 := by
  change (Matrix.diagonal (fun (a : Fin 2) => if a.val = 0 then (1 : ℂ) else 0)).det = 0 ∧
    (Matrix.diagonal (fun (a : Fin 3) => if a.val = 1 then (1 : ℂ) else 0)).det = 0
  constructor <;> rw [Matrix.det_diagonal] <;> norm_num [Fin.prod_univ_succ]

/-- The whole-ring estimate derives compatible references and keeps the shorter remainder. -/
example : ∃ σ : ∀ i : Fin 3, Matrix (Fin (ring.bondDim i)) (Fin (ring.bondDim i)) ℂ,
    (∀ i, (σ i).PosSemidef ∧ (σ i).trace = 1) ∧
    ‖Matrix.linearMapMatrix (Matrix.rectangularKrausMap
        (rectangularBlockTensor ring (by simp : ∑ _ : Fin 1, 3 = 3) 0) -
      Matrix.tracePrepareMap (α := Fin (rightBond ring (fun _ : Fin 1 => 3) 0))
        (β := Fin (blockBondDim ring (fun _ : Fin 1 => 3) 0 0))
        (σ (blockOffset (fun _ : Fin 1 => 3) (0 : Fin 1).val : Fin 3)))‖ ≤ 0 := by
  obtain ⟨σ, hσ, hm⟩ := exists_rectangular_block_mixing_of_window_domination ring
    (by intro i; fin_cases i <;> decide) site_cptp 2 (by decide) 1 le_rfl
    (fun a ha => by simpa only [Complex.ofReal_one] using window_minorization a ha)
  refine ⟨σ, hσ, ?_⟩
  simpa only [sub_self, pow_one, mul_zero,
    show 3 / 2 = 1 by decide] using hm (fun _ : Fin 1 => 3) (by simp) 0 (by decide)

end RectangularTwoSiteWindowRegression
