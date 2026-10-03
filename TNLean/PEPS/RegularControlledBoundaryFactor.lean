/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularCycleControlledBoundary
import TNLean.PEPS.RegularBoundaryState
import QICLean.Channel.MaximallyEntangled

/-!
# A common relative-boundary factor of actual controlled blocks

After the cycle-controlled permutation, a complementary canonical block has one
common boundary multiplier. Separating a reference boundary label from its
relative labels isolates the same normalized maximally entangled coefficient
for every sector and for every coherent finite sum of sectors. The remaining
coefficient retains the reference labels and the conjugated cycle residuals.
Contracting with the actual region block eliminates the reference labels and
leaves a fixed normalized region ancillary vector and a complementary cycle
orbit coefficient, also for coherent finite sums.

**Scope restriction (supplied complement walk identities):** The relative-word
identities for the actual complement walks are supplied. The canonical cut
factorization additionally requires identity residual cycles in the region.
These are explicit conditions on the actual bond operators, rather than assumed
Gram identities or assumed tensor decompositions. The geometric walks are
constructed in `TNLean.PEPS.TorusComplementPathReplacement`, and the transfer to
the original physical tensors is `TNLean.PEPS.RegularPhysicalCutTransfer`. The complementary-map factorization alone retains a virtual
reference label; the contracted-cut statement eliminates it.
See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
`Papers/1001.3807/paper_v3.tex`, lines 1935–1990 and 2043–2072.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

private theorem sum_boundary_cycle {C : Type*} [Fintype C] (n : ℕ)
    (A B : Fin (n + 1) → G) (m : G) (z ω : C → G) :
    (∑ x : G, if A = (x * m) • B ∧ z = (fun e => x * ω e * x⁻¹)
      then (1 : ℂ) else 0) =
      (if (regularBoundaryRelativeEquiv n A).2 =
        (regularBoundaryRelativeEquiv n B).2 then (1 : ℂ) else 0) *
      (if z = (fun e => (A 0 * (B 0)⁻¹ * m⁻¹) * ω e *
        (A 0 * (B 0)⁻¹ * m⁻¹)⁻¹) then 1 else 0) := by
  classical
  have hb (x : G) : A = (x * m) • B ↔
      x = A 0 * (B 0)⁻¹ * m⁻¹ ∧
        (regularBoundaryRelativeEquiv n A).2 = (regularBoundaryRelativeEquiv n B).2 := by
    rw [← (regularBoundaryRelativeEquiv n).injective.eq_iff,
      regularBoundaryRelativeEquiv_smul, Prod.ext_iff]
    change A 0 = x * m * B 0 ∧ _ ↔ _
    have he : A 0 = x * m * B 0 ↔ x = A 0 * (B 0)⁻¹ * m⁻¹ := by
      constructor <;> intro h
      · rw [h]; group
      · rw [h]; group
    rw [he]
  simp_rw [hb]
  rw [Finset.sum_eq_single (A 0 * (B 0)⁻¹ * m⁻¹)]
  · by_cases hr : (regularBoundaryRelativeEquiv n A).2 =
        (regularBoundaryRelativeEquiv n B).2 <;> simp [hr]
  · intro x _ hx
    simp only [hx, false_and, ↓reduceIte]
  · simp
private theorem sum_boundary_pair_cycle {C : Type*} [Fintype C] (n : ℕ)
    (A B : Fin (n + 1) → G) (m : G) (z ω : C → G) :
    (∑ θ : Fin (n + 1) → G,
      (∑ t : G, if A = t • θ then (1 : ℂ) else 0) *
      (∑ x : G, if B = (x * m) • θ ∧ z = (fun f => x * ω f * x⁻¹)
        then (1 : ℂ) else 0)) =
      (if (regularBoundaryRelativeEquiv n A).2 =
        (regularBoundaryRelativeEquiv n B).2 then (1 : ℂ) else 0) *
      ∑ x : G, if z = (fun f => x * ω f * x⁻¹) then 1 else 0 := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hb (θ : Fin (n + 1) → G) : B = (x * m) • θ ↔ θ = (x * m)⁻¹ • B := by
    rw [eq_comm, eq_inv_smul_iff]
  simp_rw [hb]
  rw [Finset.sum_eq_single ((x * m)⁻¹ • B)]
  · simp only [true_and]
    by_cases hz : z = (fun f => x * ω f * x⁻¹)
    · simp only [hz, ↓reduceIte, mul_one]
      have hs := sum_boundary_cycle n A ((x * m)⁻¹ • B) 1
        (fun _ : Unit => (1 : G)) (fun _ : Unit => (1 : G))
      simpa only [mul_one, mul_inv_cancel, ↓reduceIte, and_true, mul_one,
        regularBoundaryRelativeEquiv_smul] using hs
    · simp only [hz, ↓reduceIte, mul_zero]
  · intro θ _ hθ
    simp only [hθ, false_and, ↓reduceIte, mul_zero]
  · simp

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

private abbrev Boundary (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}

variable (R : Finset V)
variable (T : SimpleGraph {v : V // v ∈ Finset.univ \ R}) [DecidableRel T.Adj]
variable (hT : T ≤ Γ.induce ((Finset.univ \ R : Finset V) : Set V)) (htree : T.IsTree)
variable (o : {v : V // v ∈ Finset.univ \ R})
variable (v w : Boundary (Γ := Γ) R → {v : V // v ∈ Finset.univ \ R})
variable (p : (f : Boundary (Γ := Γ) R) →
  (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Walk (v f) (w f))

/-- The actual complementary canonical matrix after the fixed cycle-controlled
physical permutation and the inverse region boundary transport. The complement
and region crossing labels refer to the same native edges.
Source: SCP10, lines 1935–1990. -/
noncomputable def regularControlledComplementMatrix
    (kR : {v : V // v ∈ R} → G) (u : Edge Γ → G) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R)) (Boundary (Γ := Γ) R → G) ℂ :=
  fun α θ =>
    (regularComplementWalkControlMatrix (G := G) R T hT htree o v w p *
      regularProjectorTwistedRegionMatrix (Finset.univ \ R) u) α
        (fun f => (regularRegionBoundaryTransport R kR u).symm θ
          ((regionBoundaryEdgeComplEquiv (G := Γ) R).symm f))

/-- In reference boundary coordinates, the actual controlled complementary matrix
has a normalized maximally entangled factor on the relative labels. The remaining
coefficient depends only on the two reference labels and the cycle residuals.
Source: SCP10, the common boundary factor, lines 1935–1990 and 2043–2072. -/
theorem regularControlledComplementMatrix_factorization
    (kR : {v : V // v ∈ R} → G) (u : Edge Γ → G) {n : ℕ}
    (e : Boundary (Γ := Γ) R ≃ Fin (n + 1))
    (hrelative : ∀ f, FreeGroup.lift
        (regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o u)
        (regularRegionCycleWord (Finset.univ \ R) T (p f)) =
      regularCombinedBoundaryTransport R kR
          (regularRegionTreeGauge (Finset.univ \ R) T hT htree o u).1 u 1 f *
        (regularCombinedBoundaryTransport R kR
          (regularRegionTreeGauge (Finset.univ \ R) T hT htree o u).1 u 1 (e.symm 0))⁻¹)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) (Finset.univ \ R) T o)
    (θ : Boundary (Γ := Γ) R → G) :
    let A := fun i => c.1 (regionBoundaryEdgeComplEquiv (G := Γ) R (e.symm i))
    let B := fun i => θ (e.symm i)
    let m := regularCombinedBoundaryTransport R kR
      (regularRegionTreeGauge (Finset.univ \ R) T hT htree o u).1 u 1 (e.symm 0)
    let x := A 0 * (B 0)⁻¹ * m⁻¹
    regularControlledComplementMatrix R T hT htree o v w p kR u
        ((regularRegionCoordinatesEquiv (Finset.univ \ R) T hT htree o).symm c) θ =
      Matrix.omegaVec (Fintype.card (Fin n → G))
        (Fintype.equivFin (Fin n → G) (regularBoundaryRelativeEquiv n A).2,
          Fintype.equivFin (Fin n → G) (regularBoundaryRelativeEquiv n B).2) *
        ((Real.sqrt (Fintype.card (Fin n → G) : ℝ) : ℂ) *
          (Fintype.card G : ℂ)⁻¹ ^ (Finset.univ \ R).card *
          (if c.2.2.2 = (fun f => x *
            regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o u f * x⁻¹)
            then 1 else 0)) := by
  classical
  rw [regularControlledComplementMatrix,
    regularCycleControlledBoundaryMatrix_mul_coordinates_of_combined_relative_walk_words
      R kR T hT htree o v w p u (e.symm 0) hrelative]
  let E := regionBoundaryEdgeComplEquiv (G := Γ) R
  let A := fun i => c.1 (E (e.symm i))
  let B := fun i => θ (e.symm i)
  let m := regularCombinedBoundaryTransport R kR
    (regularRegionTreeGauge (Finset.univ \ R) T hT htree o u).1 u 1 (e.symm 0)
  have hb (x : G) : c.1 = (fun f => x * m * θ (E.symm f)) ↔ A = (x * m) • B := by
    constructor
    · intro h
      funext i
      simpa only [A, B, Pi.smul_apply, smul_eq_mul, E.symm_apply_apply] using
        congrFun h (E (e.symm i))
    · intro h
      funext f
      simpa only [A, B, Pi.smul_apply, smul_eq_mul, e.symm_apply_apply,
        E.apply_symm_apply] using congrFun h (e (E.symm f))
  change (Fintype.card G : ℂ)⁻¹ ^ (Finset.univ \ R).card *
    (∑ x : G, if c.1 = (fun f => x * m * θ (E.symm f)) ∧
      c.2.2.2 = (fun f => x *
        regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o u f * x⁻¹)
      then (1 : ℂ) else 0) = _
  simp_rw [hb]
  rw [sum_boundary_cycle]
  have hN : (Real.sqrt (Fintype.card (Fin n → G) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)).ne'
  change _ = Matrix.omegaVec _
    (Fintype.equivFin (Fin n → G) (regularBoundaryRelativeEquiv n A).2,
      Fintype.equivFin (Fin n → G) (regularBoundaryRelativeEquiv n B).2) * _
  rw [Matrix.omegaVec_apply]
  by_cases hr : (regularBoundaryRelativeEquiv n A).2 = (regularBoundaryRelativeEquiv n B).2
  · simp only [hr, ↓reduceIte, one_mul]
    simp only [one_div, inv_mul_cancel_left₀ hN, ← mul_assoc]
    rfl
  · simp only [(Fintype.equivFin (Fin n → G)).injective.eq_iff, hr, ↓reduceIte,
      zero_mul, mul_zero]

/-- A single relative-boundary factor separates from every coherent finite sum
of actual controlled complementary blocks. The trees, boundary numbering, and
control walks are fixed before the sector labels and coefficients.
Source: SCP10, coherent ground-state boundary factor, lines 1935–1990 and 2043–2072. -/
theorem regularControlledComplementMatrix_sum_factorization
    {I : Type*} [Fintype I] (kR : I → {v : V // v ∈ R} → G)
    (u : I → Edge Γ → G) (μ : I → ℂ) {n : ℕ}
    (e : Boundary (Γ := Γ) R ≃ Fin (n + 1))
    (hrelative : ∀ i f, FreeGroup.lift
        (regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o (u i))
        (regularRegionCycleWord (Finset.univ \ R) T (p f)) =
      regularCombinedBoundaryTransport R (kR i)
          (regularRegionTreeGauge (Finset.univ \ R) T hT htree o (u i)).1 (u i) 1 f *
        (regularCombinedBoundaryTransport R (kR i)
          (regularRegionTreeGauge (Finset.univ \ R) T hT htree o (u i)).1 (u i) 1 (e.symm 0))⁻¹)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) (Finset.univ \ R) T o)
    (θ : Boundary (Γ := Γ) R → G) :
    let A := fun j => c.1 (regionBoundaryEdgeComplEquiv (G := Γ) R (e.symm j))
    let B := fun j => θ (e.symm j)
    (∑ i, μ i * regularControlledComplementMatrix R T hT htree o v w p (kR i) (u i)
        ((regularRegionCoordinatesEquiv (Finset.univ \ R) T hT htree o).symm c) θ) =
      Matrix.omegaVec (Fintype.card (Fin n → G))
        (Fintype.equivFin (Fin n → G) (regularBoundaryRelativeEquiv n A).2,
          Fintype.equivFin (Fin n → G) (regularBoundaryRelativeEquiv n B).2) *
        ∑ i, μ i * ((Real.sqrt (Fintype.card (Fin n → G) : ℝ) : ℂ) *
          (Fintype.card G : ℂ)⁻¹ ^ (Finset.univ \ R).card *
          (let m := regularCombinedBoundaryTransport R (kR i)
            (regularRegionTreeGauge (Finset.univ \ R) T hT htree o (u i)).1 (u i) 1 (e.symm 0)
           let x := A 0 * (B 0)⁻¹ * m⁻¹
           if c.2.2.2 = (fun f => x *
             regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o (u i) f * x⁻¹)
             then 1 else 0)) := by
  classical
  simp_rw [regularControlledComplementMatrix_factorization R T hT htree o v w p
    _ _ e (hrelative _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Contract the two actual canonical region matrices after the complementary
physical control. The inverse region boundary transport only reindexes the
shared bond sum. Source: SCP10, lines 1935–1990. -/
noncomputable def regularControlledProjectorCutMatrix
    (kR : {v : V // v ∈ R} → G) (u : Edge Γ → G) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R)
      (RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R)) ℂ :=
  fun α β => ∑ θ : Boundary (Γ := Γ) R → G,
    regularProjectorTwistedRegionMatrix R u α ((regularRegionBoundaryTransport R kR u).symm θ) *
      regularControlledComplementMatrix R T hT htree o v w p kR u β θ

/-- The transported contraction is the original canonical region product with
only the complementary physical basis changed. In particular the shared
boundary transport is a reindexing, rather than an assumed tensor factorization.
Source: SCP10, lines 1935–1990. -/
theorem regularControlledProjectorCutMatrix_eq_native_contraction
    (kR : {v : V // v ∈ R} → G) (u : Edge Γ → G)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (β : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R)) :
    regularControlledProjectorCutMatrix R T hT htree o v w p kR u α β =
      ∑ θ : Boundary (Γ := Γ) R → G, regularProjectorTwistedRegionMatrix R u α θ *
        (regularComplementWalkControlMatrix (G := G) R T hT htree o v w p *
          regularProjectorTwistedRegionMatrix (Finset.univ \ R) u) β
            (fun f => θ ((regionBoundaryEdgeComplEquiv (G := Γ) R).symm f)) := by
  classical
  let f : (Boundary (Γ := Γ) R → G) → ℂ := fun θ =>
    regularProjectorTwistedRegionMatrix R u α θ *
      (regularComplementWalkControlMatrix (G := G) R T hT htree o v w p *
        regularProjectorTwistedRegionMatrix (Finset.univ \ R) u) β
          (fun f => θ ((regionBoundaryEdgeComplEquiv (G := Γ) R).symm f))
  change (∑ θ, f ((regularRegionBoundaryTransport R kR u).symm θ)) = ∑ θ, f θ
  exact (regularRegionBoundaryTransport R kR u).symm.sum_comp f

/-- The fully contracted actual canonical cut has a common relative-boundary
Kronecker delta; all remaining sector dependence is a conjugacy-orbit sum of the
complementary cycle residuals. No individual-sector Gram formula is assumed.
Source: SCP10, lines 1935–1990 and 2043–2072. -/
theorem regularControlledProjectorCutMatrix_coordinates
    (TR : SimpleGraph {v : V // v ∈ R}) [DecidableRel TR.Adj]
    (hTR : TR ≤ Γ.induce (R : Set V)) (htreeR : TR.IsTree) (oR : {v : V // v ∈ R})
    (u : Edge Γ → G) {n : ℕ} (e : Boundary (Γ := Γ) R ≃ Fin (n + 1))
    (hflat : ∀ f, regularRegionTreeCycleResidual R TR hTR htreeR oR u f = 1)
    (hrelative : ∀ f, FreeGroup.lift
        (regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o u)
        (regularRegionCycleWord (Finset.univ \ R) T (p f)) =
      regularCombinedBoundaryTransport R (regularRegionTreeGauge R TR hTR htreeR oR u).1
          (regularRegionTreeGauge (Finset.univ \ R) T hT htree o u).1 u 1 f *
        (regularCombinedBoundaryTransport R (regularRegionTreeGauge R TR hTR htreeR oR u).1
          (regularRegionTreeGauge (Finset.univ \ R) T hT htree o u).1 u 1 (e.symm 0))⁻¹)
    (cR : RegularRegionCoordinates (Γ := Γ) (G := G) R TR oR)
    (cS : RegularRegionCoordinates (Γ := Γ) (G := G) (Finset.univ \ R) T o) :
    let A := fun i => cR.1 (e.symm i)
    let B := fun i => cS.1 (regionBoundaryEdgeComplEquiv (G := Γ) R (e.symm i))
    regularControlledProjectorCutMatrix R T hT htree o v w p
        (regularRegionTreeGauge R TR hTR htreeR oR u).1 u
        ((regularRegionCoordinatesEquiv R TR hTR htreeR oR).symm cR)
        ((regularRegionCoordinatesEquiv (Finset.univ \ R) T hT htree o).symm cS) =
      ((Fintype.card G : ℂ)⁻¹ ^ R.card *
        (Fintype.card G : ℂ)⁻¹ ^ (Finset.univ \ R).card) *
      (if (regularBoundaryRelativeEquiv n A).2 =
        (regularBoundaryRelativeEquiv n B).2 then (1 : ℂ) else 0) *
      (if cR.2.2.2 = 1 then 1 else 0) *
      ∑ x : G, if cS.2.2.2 = (fun f => x *
        regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o u f * x⁻¹)
        then 1 else 0 := by
  classical
  let kR := (regularRegionTreeGauge R TR hTR htreeR oR u).1
  let kS := (regularRegionTreeGauge (Finset.univ \ R) T hT htree o u).1
  let E := regionBoundaryEdgeComplEquiv (G := Γ) R
  let m := regularCombinedBoundaryTransport R kR kS u 1 (e.symm 0)
  have hregion (θ : Boundary (Γ := Γ) R → G) :
      regularProjectorTwistedRegionMatrix R u
        ((regularRegionCoordinatesEquiv R TR hTR htreeR oR).symm cR)
          ((regularRegionBoundaryTransport R kR u).symm θ) =
        (Fintype.card G : ℂ)⁻¹ ^ R.card *
          ∑ t : G, if cR.1 = t • θ ∧ cR.2.2.2 = 1 then (1 : ℂ) else 0 := by
    rw [regularProjectorTwistedRegionMatrix_coordinates]
    simp only [kR, Equiv.apply_symm_apply]
    simp_rw [hflat, mul_one, mul_inv_cancel]
    rfl
  have hcomplement (θ : Boundary (Γ := Γ) R → G) :
      regularControlledComplementMatrix R T hT htree o v w p kR u
        ((regularRegionCoordinatesEquiv (Finset.univ \ R) T hT htree o).symm cS) θ =
        (Fintype.card G : ℂ)⁻¹ ^ (Finset.univ \ R).card *
          ∑ x : G, if cS.1 = (fun f => x * m * θ (E.symm f)) ∧
            cS.2.2.2 = (fun f => x *
              regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o u f * x⁻¹)
            then (1 : ℂ) else 0 := by
    exact regularCycleControlledBoundaryMatrix_mul_coordinates_of_combined_relative_walk_words
      R kR T hT htree o v w p u (e.symm 0) hrelative cS θ
  change (∑ θ : Boundary (Γ := Γ) R → G,
    regularProjectorTwistedRegionMatrix R u
      ((regularRegionCoordinatesEquiv R TR hTR htreeR oR).symm cR)
        ((regularRegionBoundaryTransport R kR u).symm θ) *
    regularControlledComplementMatrix R T hT htree o v w p kR u
      ((regularRegionCoordinatesEquiv (Finset.univ \ R) T hT htree o).symm cS) θ) = _
  simp_rw [hregion, hcomplement]
  by_cases hz : cR.2.2.2 = 1
  · simp only [hz, and_true, ↓reduceIte, mul_one]
    change (∑ θ : Boundary (Γ := Γ) R → G,
      ((Fintype.card G : ℂ)⁻¹ ^ R.card *
        ∑ t : G, if cR.1 = t • θ then (1 : ℂ) else 0) *
      ((Fintype.card G : ℂ)⁻¹ ^ (Finset.univ \ R).card *
        ∑ x : G, if cS.1 = (fun f => x * m * θ (E.symm f)) ∧
          cS.2.2.2 = (fun f => x *
            regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o u f * x⁻¹)
          then (1 : ℂ) else 0)) = _
    simp_rw [mul_mul_mul_comm ((Fintype.card G : ℂ)⁻¹ ^ R.card) _
      ((Fintype.card G : ℂ)⁻¹ ^ (Finset.univ \ R).card)]
    rw [← Finset.mul_sum]
    simp only [mul_assoc]
    apply congrArg ((Fintype.card G : ℂ)⁻¹ ^ R.card * ·)
    apply congrArg ((Fintype.card G : ℂ)⁻¹ ^ (Finset.univ \ R).card * ·)
    let F := e.arrowCongr (Equiv.refl G)
    rw [← F.symm.sum_comp]
    have hR (θ : Fin (n + 1) → G) (t : G) :
        cR.1 = t • F.symm θ ↔ (fun i => cR.1 (e.symm i)) = t • θ := by
      simpa only [F, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.symm_symm,
        Equiv.refl_symm, Equiv.coe_refl, Function.comp_def,
        Pi.smul_def, Pi.smul_apply, smul_eq_mul, id_eq, e.apply_symm_apply] using
        (e.symm.surjective.right_cancellable (g₁ := cR.1) (g₂ := t • F.symm θ)).symm
    have hS (θ : Fin (n + 1) → G) (x : G) :
        cS.1 = (fun f => x * (m * F.symm θ (E.symm f))) ↔
          (fun i => cS.1 (E (e.symm i))) = (x * m) • θ := by
      simpa only [F, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.symm_symm,
        Equiv.refl_symm, Equiv.coe_refl, Function.comp_def,
        Pi.smul_def, Pi.smul_apply, smul_eq_mul, id_eq, Equiv.trans_apply,
        e.apply_symm_apply, E.symm_apply_apply, mul_assoc] using
        ((e.symm.trans E).surjective.right_cancellable (g₁ := cS.1)
          (g₂ := fun f => x * m * F.symm θ (E.symm f))).symm
    simp_rw [hR, hS]
    simpa only [mul_assoc] using sum_boundary_pair_cycle n
      (fun i => cR.1 (e.symm i)) (fun i => cS.1 (E (e.symm i))) m
      cS.2.2.2 (regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o u)
  · simp only [hz, and_false, ↓reduceIte, Finset.sum_const_zero, zero_mul, mul_zero]

/-- The fixed region ancillary vector consists of a uniform reference boundary
label and uniform internal/rooted labels, with every region cycle equal to the
identity. Source: SCP10, regular blocking, lines 1840–1920 and 2043–2072. -/
noncomputable def regularReferenceRegionAncilla
    (TR : SimpleGraph {v : V // v ∈ R}) [DecidableRel TR.Adj] (oR : {v : V // v ∈ R}) :
    (G × ({f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} → G) × RootedGroupLabels (G := G) oR ×
      ({f : {f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} //
        ¬ TR.Adj ⟨f.1.1.1, f.2.1⟩ ⟨f.1.1.2, f.2.2⟩} → G)) → ℂ :=
  fun c => if c.2.2.2 = 1 then
    (Real.sqrt (Fintype.card (G ×
      (({f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} → G) ×
        RootedGroupLabels (G := G) oR)) : ℝ) : ℂ)⁻¹ else 0

/-- The fixed reference-region ancillary vector has norm one.
Source: SCP10, the normalized regular ancillary factors, lines 1840–1920. -/
theorem regularReferenceRegionAncilla_dotProduct
    (TR : SimpleGraph {v : V // v ∈ R}) [DecidableRel TR.Adj] (oR : {v : V // v ∈ R}) :
    (∑ b : G, ∑ a, ∑ r, ∑ z,
      star (regularReferenceRegionAncilla (Γ := Γ) (G := G) R TR oR (b, a, r, z)) *
        regularReferenceRegionAncilla (Γ := Γ) R TR oR (b, a, r, z)) = 1 := by
  classical
  let A := {f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} → G
  let Q := RootedGroupLabels (G := G) oR
  let : Nonempty Q := ⟨⟨1, rfl⟩⟩
  let N := Fintype.card (G × (A × Q))
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr Fintype.card_pos
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : star ((Real.sqrt (N : ℝ) : ℂ)⁻¹) *
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
    simpa only [star_inv₀, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_natCast]
      using Complex.ofReal_sqrt_inv_mul_self (N : ℝ) hNr.le
  have hp (b a r z) :
      star (regularReferenceRegionAncilla (Γ := Γ) (G := G) R TR oR (b, a, r, z)) *
        regularReferenceRegionAncilla (Γ := Γ) R TR oR (b, a, r, z) =
      (N : ℂ)⁻¹ * (if z = 1 then (1 : ℂ) else 0) := by
    by_cases hz : z = 1
    · simpa only [regularReferenceRegionAncilla, hz, ↓reduceIte, mul_one] using hs
    · simp only [regularReferenceRegionAncilla, hz, ↓reduceIte, star_zero, mul_zero]
  simp_rw [hp]
  simp only [← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN : (N : ℂ) = (Fintype.card G : ℂ) * (Fintype.card A : ℂ) *
      (Fintype.card Q : ℂ) := by simp [N, Fintype.card_prod, mul_assoc]
  change (Fintype.card Q : ℂ) * ((Fintype.card A : ℂ) *
    ((Fintype.card G : ℂ) * (N : ℂ)⁻¹)) = 1
  calc
    _ = ((Fintype.card G : ℂ) * (Fintype.card A : ℂ) *
      (Fintype.card Q : ℂ)) * (N : ℂ)⁻¹ := by ring
    _ = 1 := by rw [← hN, mul_inv_cancel₀ hNc]

/-- The same normalized maximally entangled factor and the same normalized region
ancillary vector separate from an arbitrary coherent sum of the actual controlled
canonical cut matrices. All sector dependence remains in the complementary cycle
orbit coefficient. Source: SCP10, lines 1935–1990 and 2043–2072. -/
theorem regularControlledProjectorCutMatrix_sum_factorization
    (TR : SimpleGraph {v : V // v ∈ R}) [DecidableRel TR.Adj]
    (hTR : TR ≤ Γ.induce (R : Set V)) (htreeR : TR.IsTree) (oR : {v : V // v ∈ R})
    {I : Type*} [Fintype I] (u : I → Edge Γ → G) (μ : I → ℂ) {n : ℕ}
    (e : Boundary (Γ := Γ) R ≃ Fin (n + 1))
    (hflat : ∀ i f, regularRegionTreeCycleResidual R TR hTR htreeR oR (u i) f = 1)
    (hrelative : ∀ i f, FreeGroup.lift
        (regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o (u i))
        (regularRegionCycleWord (Finset.univ \ R) T (p f)) =
      regularCombinedBoundaryTransport R (regularRegionTreeGauge R TR hTR htreeR oR (u i)).1
          (regularRegionTreeGauge (Finset.univ \ R) T hT htree o (u i)).1 (u i) 1 f *
        (regularCombinedBoundaryTransport R (regularRegionTreeGauge R TR hTR htreeR oR (u i)).1
          (regularRegionTreeGauge (Finset.univ \ R) T hT htree o (u i)).1 (u i) 1 (e.symm 0))⁻¹)
    (cR : RegularRegionCoordinates (Γ := Γ) (G := G) R TR oR)
    (cS : RegularRegionCoordinates (Γ := Γ) (G := G) (Finset.univ \ R) T o) :
    let A := fun j => cR.1 (e.symm j)
    let B := fun j => cS.1 (regionBoundaryEdgeComplEquiv (G := Γ) R (e.symm j))
    (∑ i, μ i * regularControlledProjectorCutMatrix R T hT htree o v w p
      (regularRegionTreeGauge R TR hTR htreeR oR (u i)).1 (u i)
      ((regularRegionCoordinatesEquiv R TR hTR htreeR oR).symm cR)
      ((regularRegionCoordinatesEquiv (Finset.univ \ R) T hT htree o).symm cS)) =
      Matrix.omegaVec (Fintype.card (Fin n → G))
        (Fintype.equivFin (Fin n → G) (regularBoundaryRelativeEquiv n A).2,
          Fintype.equivFin (Fin n → G) (regularBoundaryRelativeEquiv n B).2) *
      regularReferenceRegionAncilla (Γ := Γ) (G := G) R TR oR (A 0, cR.2) *
      ((Real.sqrt (Fintype.card (Fin n → G) : ℝ) : ℂ) *
        (Real.sqrt (Fintype.card (G ×
          (({f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} → G) ×
            RootedGroupLabels (G := G) oR)) : ℝ) : ℂ) *
        ((Fintype.card G : ℂ)⁻¹ ^ R.card *
          (Fintype.card G : ℂ)⁻¹ ^ (Finset.univ \ R).card) *
        ∑ i, μ i * ∑ x : G, if cS.2.2.2 = (fun f => x *
          regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o (u i) f * x⁻¹)
          then 1 else 0) := by
  classical
  let Q := RootedGroupLabels (G := G) oR
  let : Nonempty Q := ⟨⟨1, rfl⟩⟩
  have hL : (Real.sqrt (Fintype.card (Fin n → G) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)).ne'
  have hF : (Real.sqrt (Fintype.card (G ×
      (({f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} → G) × Q)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)).ne'
  dsimp only [Q] at hF
  simp_rw [regularControlledProjectorCutMatrix_coordinates R T hT htree o v w p
    TR hTR htreeR oR _ e (hflat _) (hrelative _)]
  rw [Matrix.omegaVec_apply]
  by_cases hr : (regularBoundaryRelativeEquiv n (fun j => cR.1 (e.symm j))).2 =
      (regularBoundaryRelativeEquiv n
        (fun j => cS.1 (regionBoundaryEdgeComplEquiv (G := Γ) R (e.symm j)))).2
  · by_cases hz : cR.2.2.2 = 1
    · simp only [hr, hz, ↓reduceIte, mul_one, regularReferenceRegionAncilla, one_div]
      rw [show (∑ i, μ i *
        (((Fintype.card G : ℂ)⁻¹ ^ R.card *
          (Fintype.card G : ℂ)⁻¹ ^ (Finset.univ \ R).card) *
          ∑ x : G, if cS.2.2.2 = (fun f => x *
            regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o (u i) f * x⁻¹)
            then (1 : ℂ) else 0)) =
        ((Fintype.card G : ℂ)⁻¹ ^ R.card *
          (Fintype.card G : ℂ)⁻¹ ^ (Finset.univ \ R).card) *
          ∑ i, μ i * ∑ x : G, if cS.2.2.2 = (fun f => x *
            regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o (u i) f * x⁻¹)
            then (1 : ℂ) else 0 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring]
      field_simp [hL, hF]
    · simp only [hz, ↓reduceIte, mul_zero, zero_mul, Finset.sum_const_zero,
        regularReferenceRegionAncilla]
  · simp only [(Fintype.equivFin (Fin n → G)).injective.eq_iff, hr, ↓reduceIte,
      zero_mul, mul_zero, Finset.sum_const_zero]

end TNLean.PEPS
