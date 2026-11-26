/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Entropy.RegionalReset
import TNLean.PEPS.Approximation.DoubledHamiltonian.SwappedSquareHamiltonian
import TNLean.PEPS.AreaLaw.Operators.Interactions.RegionOperatorLocalization
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct

/-!
# A supported Gaussian buffer operator for the square Hamiltonian

The original square Hamiltonian and its actual partial swap determine the two
generators. The canonical regional split identifies the grouped buffer operator
with its lift from the physical complement. The resulting supported integral
uses the actual projected relative evolution and the original Gaussian measure.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `02-information.tex`, lines 498–564,
`eq:info-operator-localization` and `eq:info-local-two-sided`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open ManyBody (Edge SquareLatticeVertex squareLatticeGraph SquareInteraction)

open Matrix MeasureTheory ProbabilityTheory QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator NNReal

namespace TNLean.PEPS.Approximation

/-- The localization prefactor `2 C₀(1)` for the doubled square Hamiltonian: twice the
graph-ball prefactor at range one. Its value is `64 e^{3/2} / (1 - e^{-1/2})`
(`squareLocalizationPrefactor_eq`).
Source: the constant `C` of `eq:info-lr` and `eq:info-operator-localization`,
polynomial-PEPS `02-information.tex`, lines 486–508. -/
noncomputable def squareLocalizationPrefactor : ℝ :=
  2 * AreaLaw.graphBallLocalizationPrefactor 1

/-- The localization velocity of the doubled square Hamiltonian with interaction bound `J`:
the graph-ball velocity at range one and term-norm bound `2J`. Its value is `320 e² J`
(`squareLocalizationVelocity_eq`). The matching decay rate is `1/2`.
Source: the velocity `v` of `eq:info-lr`, polynomial-PEPS `02-information.tex`,
lines 486–496. -/
noncomputable def squareLocalizationVelocity (J : ℝ) : ℝ :=
  AreaLaw.graphBallLocalizationVelocity 1 (2 * J)

theorem squareLocalizationPrefactor_pos : 0 < squareLocalizationPrefactor :=
  mul_pos two_pos (AreaLaw.graphBallLocalizationPrefactor_pos 1)

theorem squareLocalizationVelocity_nonneg {J : ℝ} (hJ : 0 ≤ J) :
    0 ≤ squareLocalizationVelocity J :=
  AreaLaw.graphBallLocalizationVelocity_nonneg 1 (by linarith)

theorem squareLocalizationPrefactor_eq :
    squareLocalizationPrefactor = 64 * Real.exp (3 / 2) / (1 - Real.exp (-(1 / 2))) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.exp_add]
  simp only [squareLocalizationPrefactor, AreaLaw.graphBallLocalizationPrefactor, Nat.cast_one,
    Nat.factorial]
  ring

theorem squareLocalizationVelocity_eq (J : ℝ) :
    squareLocalizationVelocity J = 320 * Real.exp 2 * J := by
  simp only [squareLocalizationVelocity, AreaLaw.graphBallLocalizationVelocity]
  norm_num
  ring

/-- **The supported Gaussian approximation of the physical buffer, with explicit
constants.** The error of the supported integral is at most
`‖W‖ C L² (1 + 8 J L² T) e^{v T - l/2}` with `C = squareLocalizationPrefactor` and
`v = squareLocalizationVelocity J`, the constants of the doubled square Hamiltonian at local
dimension `q²`, range one and term-norm bound `2J`.
Source: polynomial-PEPS, Section 2, `eq:info-local-two-sided`, lines 513–562, with the
constants of `eq:info-lr` (lines 486–496). -/
theorem _root_.ManyBody.SquareInteraction.supported_buffer_gaussian_integral
    (q : ℕ) (hq : 1 ≤ q) (J : ℝ) (hJ : 0 ≤ J) :
    ∀ (L : ℕ) (h : SquareInteraction L q) (_ : h.hamiltonian.IsHermitian) (_ : ∀ i, ‖h.term i‖ ≤ J)
      (R C₀ : Finset (SquareLatticeVertex L L)) (hRC : Disjoint R C₀),
      let Q := (R ∪ C₀)ᶜ
      let P := Fin (Fintype.card (R → Fin q)) × Fin (Fintype.card (C₀ → Fin q))
      let s := ManyBody.splitTwoRegionsEquiv
        (fun _ : SquareLatticeVertex L L ↦ Fin q) R C₀ hRC
      let g := (s.prodCongr s).trans (Equiv.doubledRegroup P ({v // v ∉ R ∪ C₀} → Fin q))
      let pr := Equiv.arrowProdEquivProdArrow (SquareLatticeVertex L L) (fun _ ↦ Fin q)
        fun _ ↦ Fin q
      let p := pr.symm.trans
        (Equiv.arrowCongr (Equiv.refl (SquareLatticeVertex L L)) finProdFinEquiv)
      let Λ := ManyBody.rectangularDomain L L
      let a := ManyBody.rectangleSiteEquiv L L
      let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
      let K := reindex (p.trans e) (p.trans e) (doubledHamiltonian h.hamiltonian)
      let F := reindex (p.trans e) (p.trans e) (reindex pr pr (ManyBody.pairSwapOp R))
      let K' := F * K * Fᴴ
      let boundary : Finset (Edge (squareLatticeGraph L L)) :=
        Finset.univ.filter (ManyBody.IsRegionBoundaryEdge R)
      let Z := boundary.biUnion fun b ↦
        ({b.1.1, b.1.2} : Finset (SquareLatticeVertex L L))
      ∀ W : Matrix (({v // v ∉ R ∪ C₀} → Fin q) × ({v // v ∉ R ∪ C₀} → Fin q))
          (({v // v ∉ R ∪ C₀} → Fin q) × ({v // v ∉ R ∪ C₀} → Fin q)) ℂ,
        let V := reindex (g.symm.trans (p.trans e)) (g.symm.trans (p.trans e))
          ((1 : Matrix (P × P) (P × P) ℂ) ⊗ₖ W)
        ∀ l : ℕ,
          let B := ManyBody.graphNeighborhood (ManyBody.planeDomainGraph Λ)
            (Q.image a ∪ Z.image a) l
          ∃ U : ℝ → Matrix (↥Λ → Fin (q * q))
              (↥Λ → Fin (q * q)) ℂ,
            U 0 = 1 ∧
            (∀ t, HasDerivAt U
              ((Complex.I • ManyBody.regionExpectation B
                (ManyBody.heisenbergEvolution K' t (K' - K))) * U t) t) ∧
            (∀ t, U t ∈ unitaryGroup (↥Λ → Fin (q * q)) ℂ) ∧
            (∀ t, U t ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B) ∧
            ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
              let M := ∫ t : ℝ in Set.Icc (-T) T,
                ManyBody.regionExpectation B (ManyBody.heisenbergEvolution K' t V) * U t
                  ∂gaussianReal 0 η
              M ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B ∧
              ‖M‖ ≤ ‖W‖ ∧
              ‖M - GaussianFilter.gaussianIntertwinerTruncated η T K' K V‖ ≤
                ‖W‖ * squareLocalizationPrefactor * (L : ℝ) ^ 2 *
                  (1 + 8 * J * (L : ℝ) ^ 2 * T) *
                  Real.exp (squareLocalizationVelocity J * T - 1 / 2 * l) := by
  classical
  intro L h hh hhJ R C₀ hRC Q P s g pr p Λ a e K F K' boundary Z W V l B
  have hC : 0 < squareLocalizationPrefactor := squareLocalizationPrefactor_pos
  obtain ⟨gH, hgH, hgHJ, _, hgOperator⟩ := h.exists_swapped_doubled_planeInteraction hh hhJ hJ R
  have hconj (A B : Matrix (SquareLatticeVertex L L → Fin (q * q))
      (SquareLatticeVertex L L → Fin (q * q)) ℂ) :
      reindex e e (A * B * Aᴴ) = reindex e e A * reindex e e B * (reindex e e A)ᴴ := by
    simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  have hFe : F = reindex e e (reindex p p (reindex pr pr (ManyBody.pairSwapOp R))) := by
    ext x y
    rfl
  have hKe : K = reindex e e (reindex p p (doubledHamiltonian h.hamiltonian)) := by
    ext x y
    rfl
  have hK' : gH.hamiltonian = K' := by
    rw [hgOperator, hconj]
    change _ = F * K * Fᴴ
    rw [hFe, hKe]
  have hKK : K' - K = reindex e e (reindex p p (reindex pr pr (ManyBody.pairSwapOp R)) *
      reindex p p (doubledHamiltonian h.hamiltonian) *
        (reindex p p (reindex pr pr (ManyBody.pairSwapOp R)))ᴴ -
        reindex p p (doubledHamiltonian h.hamiltonian)) := by
    rw [show ∀ A B : Matrix (SquareLatticeVertex L L → Fin (q * q))
        (SquareLatticeVertex L L → Fin (q * q)) ℂ,
        reindex e e (A - B) = reindex e e A - reindex e e B from fun _ _ ↦ rfl, hconj]
    change F * K * Fᴴ - K = _
    rw [hFe, hKe]
  have hDK : (doubledHamiltonian h.hamiltonian).IsHermitian := by
    simp only [Matrix.IsHermitian, doubledHamiltonian, Matrix.conjTranspose_add,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      (show h.hamiltonian.IsHermitian from hh).eq]
  have hV₀ : reindex (g.symm.trans p) (g.symm.trans p)
      ((1 : Matrix (P × P) (P × P) ℂ) ⊗ₖ W) ∈
        ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) Q := by
    obtain ⟨A, hA⟩ : ∃ A, reindex (g.symm.trans p) (g.symm.trans p)
        ((1 : Matrix (P × P) (P × P) ℂ) ⊗ₖ W) = ManyBody.place (X := fun _ ↦ Fin (q * q)) Q A :=
      ⟨_, ManyBody.reindex_physicalBuffer_eq_place q R C₀ hRC W⟩
    rw [hA]
    exact ManyBody.place_mem_supportedOperators A
  have hV : V ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q))
      (Q.image a : Finset ↥Λ) := by
    have hs := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators
      (X := fun _ : SquareLatticeVertex L L ↦ Fin (q * q))
      (X' := fun _ : ↥(ManyBody.rectangularDomain L L) ↦ Fin (q * q))
      (ManyBody.rectangleSiteEquiv L L) (fun _ ↦ Equiv.refl (Fin (q * q)))
      (D := Q) (D' := Q.image (ManyBody.rectangleSiteEquiv L L))
      (fun _ ↦ (ManyBody.rectangleSiteEquiv L L).injective.mem_finset_image.symm) hV₀
    rw [AreaLaw.siteConfigurationEquiv_rectangleSiteEquiv] at hs
    simpa only [a, V, Matrix.reindex_apply, Matrix.submatrix_submatrix] using! hs
  have hD : gH.hamiltonian - K ∈
      ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) (Z.image a : Finset ↥Λ) := by
    have hs := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators
      (X := fun _ : SquareLatticeVertex L L ↦ Fin (q * q))
      (X' := fun _ : ↥(ManyBody.rectangularDomain L L) ↦ Fin (q * q))
      (ManyBody.rectangleSiteEquiv L L) (fun _ ↦ Equiv.refl (Fin (q * q)))
      (fun _ ↦ (ManyBody.rectangleSiteEquiv L L).injective.mem_finset_image.symm)
      (h.swapped_doubled_boundary_bound hhJ R).1
    rw [AreaLaw.siteConfigurationEquiv_rectangleSiteEquiv] at hs
    rw [hK', hKK]
    exact hs
  have hDn : ‖K' - K‖ ≤ 8 * J * (L : ℝ) ^ 2 := by
    rw [hKK, Matrix.l2_opNorm_reindex_equiv]
    exact (h.swapped_doubled_boundary_bound hhJ R).2
  have hVn : ‖V‖ ≤ ‖W‖ :=
    (Matrix.l2_opNorm_reindex_equiv (g.symm.trans (p.trans e)) _).trans_le
      (Matrix.l2_opNorm_one_kronecker_le W)
  have hcard : (Λ.card : ℝ) = (L : ℝ) ^ 2 := by
    simpa only [Λ,SquareLatticeVertex, Fintype.card_coe,
      Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using
      congrArg (fun n : ℕ ↦ (n : ℝ)) (Fintype.card_congr a).symm
  obtain ⟨U, hU0, hU, hunit, hsupport, hM⟩ :=
    AreaLaw.supported_gaussian_integral (q * q) (Nat.mul_le_mul hq hq) 1
      (by linarith : (0 : ℝ) ≤ 2 * J) Λ gH hgH hgHJ K V (hDK.reindex (p.trans e))
      (Q.image a) (Z.image a) hV hD l
  rw [hK'] at hU hM
  refine ⟨U, hU0, hU, hunit, hsupport, fun η T hT ↦ ?_⟩
  refine ⟨(hM η T hT).1, (hM η T hT).2.1.trans hVn, (hM η T hT).2.2.trans ?_⟩
  simpa only [hcard, squareLocalizationPrefactor, squareLocalizationVelocity] using
    mul_le_mul_of_nonneg_right
      (mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hVn hC.le) (sq_nonneg (L : ℝ)))
        (add_le_add_right (mul_le_mul_of_nonneg_right hDn hT) 1)
        (add_nonneg zero_le_one (mul_nonneg (norm_nonneg (K' - K)) hT))
        (mul_nonneg (mul_nonneg (norm_nonneg W) hC.le) (sq_nonneg (L : ℝ))))
      (Real.exp_pos _).le


/-- The actual square Hamiltonian and grouped buffer matrix construct a
supported Gaussian approximation. Both spatial support hypotheses are derived
from the original interactions and coordinate maps. The constants precede all
finite systems, and the same relative path precedes every variance and cutoff.
Source: polynomial-PEPS, Section 2, `eq:info-local-two-sided`, lines 513–562. -/
theorem _root_.ManyBody.SquareInteraction.exists_supported_buffer_gaussian_integral
    (q : ℕ) (hq : 1 ≤ q) (J : ℝ) (hJ : 0 ≤ J) :
    ∃ C v c : ℝ, 0 < C ∧ 0 < v ∧ 0 < c ∧
      ∀ (L : ℕ) (h : SquareInteraction L q) (_ : h.hamiltonian.IsHermitian)
          (_ : ∀ i, ‖h.term i‖ ≤ J)
        (R C₀ : Finset (SquareLatticeVertex L L)) (hRC : Disjoint R C₀),
        let Q := (R ∪ C₀)ᶜ
        let P := Fin (Fintype.card (R → Fin q)) × Fin (Fintype.card (C₀ → Fin q))
        let s := ManyBody.splitTwoRegionsEquiv
          (fun _ : SquareLatticeVertex L L ↦ Fin q) R C₀ hRC
        let g := (s.prodCongr s).trans (Equiv.doubledRegroup P ({v // v ∉ R ∪ C₀} → Fin q))
        let pr := Equiv.arrowProdEquivProdArrow (SquareLatticeVertex L L) (fun _ ↦ Fin q)
          fun _ ↦ Fin q
        let p := pr.symm.trans
          (Equiv.arrowCongr (Equiv.refl (SquareLatticeVertex L L)) finProdFinEquiv)
        let Λ := ManyBody.rectangularDomain L L
        let a := ManyBody.rectangleSiteEquiv L L
        let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
        let K := reindex (p.trans e) (p.trans e) (doubledHamiltonian h.hamiltonian)
        let F := reindex (p.trans e) (p.trans e) (reindex pr pr (ManyBody.pairSwapOp R))
        let K' := F * K * Fᴴ
        let boundary : Finset (Edge (squareLatticeGraph L L)) :=
          Finset.univ.filter (ManyBody.IsRegionBoundaryEdge R)
        let Z := boundary.biUnion fun b ↦
          ({b.1.1, b.1.2} : Finset (SquareLatticeVertex L L))
        ∀ W : Matrix (({v // v ∉ R ∪ C₀} → Fin q) × ({v // v ∉ R ∪ C₀} → Fin q))
            (({v // v ∉ R ∪ C₀} → Fin q) × ({v // v ∉ R ∪ C₀} → Fin q)) ℂ,
          let V := reindex (g.symm.trans (p.trans e)) (g.symm.trans (p.trans e))
            ((1 : Matrix (P × P) (P × P) ℂ) ⊗ₖ W)
          ∀ l : ℕ,
            let B := ManyBody.graphNeighborhood (ManyBody.planeDomainGraph Λ)
              (Q.image a ∪ Z.image a) l
            ∃ U : ℝ → Matrix (↥Λ → Fin (q * q))
                (↥Λ → Fin (q * q)) ℂ,
              U 0 = 1 ∧
              (∀ t, HasDerivAt U
                ((Complex.I • ManyBody.regionExpectation B
                  (ManyBody.heisenbergEvolution K' t (K' - K))) * U t) t) ∧
              (∀ t, U t ∈ unitaryGroup (↥Λ → Fin (q * q)) ℂ) ∧
              (∀ t, U t ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B) ∧
              ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
                let M := ∫ t : ℝ in Set.Icc (-T) T,
                  ManyBody.regionExpectation B (ManyBody.heisenbergEvolution K' t V) * U t
                    ∂gaussianReal 0 η
                M ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B ∧
                ‖M‖ ≤ ‖W‖ ∧
                ‖M - GaussianFilter.gaussianIntertwinerTruncated η T K' K V‖ ≤
                  ‖W‖ * C * (L : ℝ) ^ 2 * (1 + 8 * J * (L : ℝ) ^ 2 * T) *
                    Real.exp (v * T - c * l) := by
  refine ⟨squareLocalizationPrefactor, squareLocalizationVelocity J + 1, 1 / 2,
    squareLocalizationPrefactor_pos,
    by linarith [squareLocalizationVelocity_nonneg hJ], one_half_pos, fun L h hh hhJ R C₀ hRC ↦ ?_⟩
  intro Q P s g pr p Λ a e K F K' boundary Z W V l B
  obtain ⟨U, hU0, hU, hunit, hsupport, hM⟩ :=
    ManyBody.SquareInteraction.supported_buffer_gaussian_integral q hq J hJ L h hh hhJ R C₀ hRC W l
  refine ⟨U, hU0, hU, hunit, hsupport, fun η T hT ↦ ?_⟩
  obtain ⟨hMs, hMn, hMe⟩ := hM η T hT
  refine ⟨hMs, hMn, hMe.trans ?_⟩
  have hC := squareLocalizationPrefactor_pos
  gcongr
  linarith

end TNLean.PEPS.Approximation
