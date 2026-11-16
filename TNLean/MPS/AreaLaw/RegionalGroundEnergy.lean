/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.HardTruncationResidual
import TNLean.MPS.AreaLaw.AKLV.Truncation
import QICLean.Analysis.GroundEnergyBounds
import QICLean.Analysis.LowEnergyPerturbation
import QICLean.Analysis.ProjectedPositiveEnergy
import QICLean.Analysis.ViableProjectionNonzero

/-!
# Regional excitation energy on the full original ground space

For an interval of a nearest-neighbour chain, the regional Hamiltonian,
centered at its actual minimum, has energy at most two on every unit
vector of the full original ground space. Only the two crossing bonds
contribute to this budget. Its norm is bounded by the chain length.
Projection into a candidate with loss at most `1 / (100 * (L + 1))`
keeps the regional energy below three and supplies a nonzero candidate
vector with this Rayleigh bound.

This is an auxiliary for ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1631–1632, and the energy-estimation argument in the proof of
`t:alg1`, lines 1805–1806. No gap or simple-ground-space assumption is used.
-/

open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- The actual regional minimum gives a positive regional excitation
operator whose energy on the original full ground space is at most two.
Its norm is at most the chain length. A sufficiently close candidate
contains a nonzero vector with regional excitation energy at most three,
and the same bound holds on the entire projected ground space.
All regional and ground-space data
are constructed from the original bonds. Auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631–1632. -/
theorem exists_regional_ground_energy_bound {L q l r : ℕ}
    (hq : 0 < q) (hlr : l ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let _ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let H := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)
    let A := aklvRegionalHamiltonians l r h 1
    ∃ (e : ℝ) (x : (Fin L → Fin q) → ℂ),
      star x ⬝ᵥ x = 1 ∧ A *ᵥ x = (e : ℂ) • x ∧
      let C := A - (e : ℂ) • 1
      C.PosSemidef ∧ ‖C‖ ≤ (L : ℝ) ∧
        (∀ g ∈ G, (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) C g) g).re ≤
          2 * ‖g‖ ^ 2) ∧
        ∀ (δ : ℝ) (U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))),
          0 ≤ δ → δ ≤ 1 / (100 * ((L : ℝ) + 1)) → Submodule.IsCloseTo δ U G →
          (∀ v ∈ G.map U.starProjection.toLinearMap,
            (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) C v) v).re ≤
              3 * ‖v‖ ^ 2) ∧
          ∃ v ∈ U, v ≠ 0 ∧
            (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) C v) v).re ≤
              3 * ‖v‖ ^ 2 := by
  intro config H hH G A
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨e, x, z, E, hx, hxe, he, he0, hz, hHz, hE, hE0, hE2, _htruncation⟩ :=
    ALVV.exists_single_region_hard_truncation_residuals hq hlr hrL h hs h0 h1
  clear _htruncation
  refine ⟨e 1, x, hx, hxe 1, ?_⟩
  intro C
  have hC : C.PosSemidef := he 1
  let I := Finset.univ.filter (fun i : Fin (L - 1) ↦ l ≤ i.val ∧ i.val + 1 < r)
  have hAeq : A = ∑ i ∈ I, h i := rfl
  have hcard : I.card ≤ L := by
    calc
      I.card ≤ Fintype.card (Fin (L - 1)) := Finset.card_le_univ I
      _ = L - 1 := Fintype.card_fin _
      _ ≤ L := Nat.sub_le _ _
  have hcapA : A ≤ (L : ℝ) • 1 := by
    calc
      A = ∑ i ∈ I, h i := hAeq
      _ ≤ (I.card : ℝ) • 1 :=
        (sum_posSemidef_and_le_card_of_positive_unit_terms I h
          (fun i _ ↦ h0 i) (fun i _ ↦ h1 i)).2
      _ ≤ (L : ℝ) • 1 := smul_le_smul_of_nonneg_right (by exact_mod_cast hcard) zero_le_one
  have hcapC : C ≤ (L : ℝ) • 1 := by
    refine (sub_le_self A ?_).trans hcapA
    rw [Complex.coe_smul]
    exact smul_nonneg (he0 1) zero_le_one
  have hnorm : ‖C‖ ≤ (L : ℝ) :=
    (CStarAlgebra.norm_le_iff_le_algebraMap C (by positivity) hC.nonneg).mpr
      (by simpa only [Algebra.algebraMap_eq_smul_one] using hcapC)
  let S := ∑ j, e j
  have hmin : minEigenvalue hH = E + S :=
    hH.minEigenvalue_eq_add_of_centered_ground S E z hz hHz hE
  let Y := ∑ i ∈ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ)), h i
  have hrest : ((aklvRegionalHamiltonians l r h 0 - (e 0 : ℂ) • 1) +
      (aklvRegionalHamiltonians l r h 2 - (e 2 : ℂ) • 1) + Y).PosSemidef :=
    ((he 0).add (he 2)).add (posSemidef_sum _ (fun i _ ↦ (h0 i).posSemidef))
  have hsplit : H - (S : ℂ) • 1 - C =
      (aklvRegionalHamiltonians l r h 0 - (e 0 : ℂ) • 1) +
        (aklvRegionalHamiltonians l r h 2 - (e 2 : ℂ) • 1) + Y := by
    dsimp only [H, S, C, A, Y]
    rw [sum_three_regions_add_crossings hlr h]
    simp only [Fin.sum_univ_three, Complex.ofReal_add, add_smul]
    abel
  have hpos : (H - (S : ℂ) • 1 - C).PosSemidef := by rw [hsplit]; exact hrest
  have hbase : ∀ g ∈ G,
      (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) C g) g).re ≤
        2 * ‖g‖ ^ 2 := by
    intro g hg
    have hraw := Submodule.re_inner_apply_le_of_mem_spectralSpanLE
      hH.eigenvectorBasis hH.eigenvalues
      (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H).toLinearMap
      (fun j ↦ hH.toEuclideanCLM_eigenvectorBasis j) (minEigenvalue hH) hg
    have hquadratic := hpos.isPositive_toEuclideanCLM.re_inner_nonneg_left g
    simp only [map_sub, map_smul, map_one, _root_.sub_apply,
      _root_.smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, RCLike.re_to_complex, Complex.conj_ofReal,
      Complex.re_ofReal_mul] at hquadratic
    have hself : (inner ℂ g g).re = ‖g‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) g
    rw [hself] at hquadratic
    have hrawLeft : (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H g) g).re ≤
        minEigenvalue hH * ‖g‖ ^ 2 := by
      calc
        _ = (inner ℂ g (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H g)).re :=
          inner_re_symm (𝕜 := ℂ) _ _
        _ ≤ _ := hraw
    rw [hmin] at hrawLeft
    nlinarith only [hquadratic, hrawLeft, mul_le_mul_of_nonneg_right hE2 (sq_nonneg ‖g‖)]
  refine ⟨hC, hnorm, hbase, ?_⟩
  intro δ U hδ0 hsmall hclose
  have hfinal : ∀ v ∈ G.map U.starProjection.toLinearMap,
      (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) C v) v).re ≤
        3 * ‖v‖ ^ 2 :=
    hclose.map_starProjection_energy_le_three hδ0
      (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) C) hC.isPositive_toEuclideanCLM
      hbase hnorm hsmall
  refine ⟨hfinal, ?_⟩
  have hδ1 : δ < 1 :=
    (Real.projected_positive_energy_le_three (by positivity : (0 : ℝ) ≤ L) hδ0 hsmall).1
  obtain ⟨g0, hg0, hg0norm⟩ : ∃ g0 ∈ G, ‖g0‖ = 1 := by
    obtain ⟨j, hj⟩ := minEigenvalue_achieved hH
    exact ⟨hH.eigenvectorBasis j, Submodule.subset_span ⟨j, hj.le, rfl⟩,
      hH.eigenvectorBasis.norm_eq_one j⟩
  have hvnz : U.starProjection g0 ≠ 0 :=
    hclose.starProjection_ne_zero hδ1 hg0 (norm_ne_zero_iff.mp (hg0norm.trans_ne one_ne_zero))
  exact ⟨U.starProjection g0, U.starProjection_apply_mem g0, hvnz,
    hfinal _ (Submodule.mem_map_of_mem hg0)⟩

end TNLean.MPS.AreaLaw
