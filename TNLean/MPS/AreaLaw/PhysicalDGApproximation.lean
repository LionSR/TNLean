/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGViability
import TNLean.MPS.AreaLaw.IndependentPhysicalDGViability
import TNLean.MPS.AreaLaw.SharpApproximationParameters
import QICLean.Analysis.ViableSubspaceSchmidtRank

/-!
# Normalized approximations from the full physical ground space

A fixed viable subspace is enlarged using the independently chosen
truncation and polynomial scales. The approximating vectors are normalized
in the original Hilbert space, and their Schmidt ranks have the full original
ground-space dimension as a linear factor. This supports the fixed-cut
conclusion of ALVV, arXiv:1602.08828v2, Theorem 4.9, source lines 1048–1085.

**Local fix (parameter choice):** The printed prescription is replaced by
independent scales as documented in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Scope restriction (gap dependence):** The bound uses `min gamma 1`.
Comparison with the printed quantitative dependence is established for
`0 < gamma ≤ 1`; the larger-gap comparison remains as recorded in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.

The distinct spectral values express Assumption (DG) of the source,
lines 275–279, which requires a second smallest eigenvalue.
-/

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- Every original unit ground vector has a normalized approximation at an
actual interval cut. The integer rank budget retains a single factor equal
to the full ground-space dimension. Both universal constants precede the
Hamiltonian, interval and error. Supporting ALVV, arXiv:1602.08828v2,
Theorem 4.9, fixed-cut conclusion, source lines 1048–1085. -/
theorem exists_physical_dg_normalized_approximation_of_independent_scales :
    ∃ A C : ℝ, 1 ≤ A ∧ 21 ≤ C ∧
      ∀ (L q p r : ℕ), p ≤ r → r ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let g := min gamma 1
      let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D0 : ℕ := (q * ell ^ 2) ^ (22 * ell)
      let cA : ℝ := 6 + 2 * Real.log (A + 1)
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      2 ≤ D0 ∧
      Real.log (D0 : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let a := 16 + Real.log (1 / g) + Real.log (1 / delta)
      ∃ ell1 : ℕ, 1 ≤ ell1 ∧
      (ell1 : ℝ) ≤ 8 / (4 * g / 5) +
        (7 * C) ^ (1 / 4 : ℝ) * (1 / (4 * g / 5)) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) ∧
      let D1 : ℕ := (q * ell1 ^ 2) ^ (22 * ell1)
      let e := Tm.trans (Submodule.euclideanTensorEquiv (J → Fin q) (↥(Jᶜ) → Fin q)).symm
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G → ‖ψ‖ = 1 →
      ∃ φ : EuclideanSpace ℂ (Fin L → Fin q), ‖φ‖ = 1 ∧
        1 - delta ≤ ‖⟪φ, ψ⟫_ℂ‖ ∧
        Matrix.schmidtRank (WithLp.ofLp (e φ)) ≤ Module.finrank ℂ G * D0 ^ 24 * D1 ^ 2 := by
  classical
  obtain ⟨A, hA, _hA21, hphysical⟩ := exists_accuracy_physical_interval_family_and_bootstrap
  obtain ⟨C, hC, hscalar⟩ := Real.exists_sharp_approximation_scalar_parameters
  refine ⟨A, C, hA, hC, ?_⟩
  intro L q p r hpr hrL h hs h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G g u ell D0 cA J beta tau U Phi Tm
  let EM := EuclideanSpace ℂ (J → Fin q)
  let EE := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)
  obtain ⟨hD0, hlogD0, W0, hWdim, hW0, _hcoarse⟩ :=
    hphysical L q p r hpr hrL h hs h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hgapg : ∀ x ∈ spectrum ℝ H, x = mu ∨ mu + g ≤ x := by
    intro x hx
    rcases hgap x hx with heq | hge
    · exact Or.inl heq
    · have hgg : g ≤ gamma := min_le_left gamma 1
      exact Or.inr (by linarith only [hgg, hge])
  have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
  refine ⟨hD0, hlogD0, ?_⟩
  intro delta hdelta hdelta1 a
  let t := C * a
  obtain ⟨ell1, hell1, hbound, ht, htail, hfilter⟩ := hscalar g delta hg hg1 hdelta hdelta1
  refine ⟨ell1, hell1, hbound, ?_⟩
  intro D1 e ψ hψG hψ
  have hD02 : 2 ≤ D0 := hD0
  have hD0pos : 0 < D0 := Nat.lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hD02
  have hbasepos : 0 < Module.finrank ℂ G * D0 ^ 24 :=
    Nat.mul_pos (Nat.lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hrG) (pow_pos hD0pos 24)
  by_cases hshort : r - p ≤ 4 * ell1
  · have hJ : J.card ≤ 4 * ell1 := (card_interval_le (L := L) p r).trans hshort
    have hell2 : 1 ≤ ell1 ^ 2 :=
      hell1.trans (Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) ell1)
    have hbase : q ≤ q * ell1 ^ 2 := by
      simpa only [mul_one] using Nat.mul_le_mul_left q hell2
    have hcount : Fintype.card (J → Fin q) ≤ D1 ^ 2 := by
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
      calc
        q ^ J.card ≤ q ^ (4 * ell1) := Nat.pow_le_pow_right (by omega) hJ
        _ ≤ (q * ell1 ^ 2) ^ (4 * ell1) := Nat.pow_le_pow_left hbase _
        _ ≤ (q * ell1 ^ 2) ^ ((22 * ell1) * 2) :=
          Nat.pow_le_pow_right ((by omega : 0 < q).trans_le hbase) (by omega)
        _ = D1 ^ 2 := pow_mul _ _ _
    have hbaseone : 1 ≤ Module.finrank ℂ G * D0 ^ 24 := Nat.succ_le_iff.mpr hbasepos
    have hbudget : D1 ^ 2 ≤ Module.finrank ℂ G * D0 ^ 24 * D1 ^ 2 := by
      simpa only [one_mul] using (Nat.mul_le_mul_right (D1 ^ 2) hbaseone)
    refine ⟨ψ, hψ, ?_, (Matrix.schmidtRank_le_left _).trans (hcount.trans hbudget)⟩
    have hinner : ‖⟪ψ, ψ⟫_ℂ‖ = 1 := by norm_num [inner_self_eq_norm_sq_to_K, hψ]
    rw [hinner]
    linarith only [hdelta]
  · obtain ⟨T, Fops, hTG, hGT, _hdim, himprove⟩ :=
      exists_independent_long_middle_actual_dg_family q q ell1 t g delta (delta / 8)
        hq le_rfl hell1 ht hg hg1 hdelta hdelta1 htail hfilter
        L p r hpr hrL (Nat.lt_of_not_ge hshort) h hs h0 h1 mu hmu hgapg
    have hGTmap := (Submodule.isCloseTo_map_iff Tm).mpr hGT
    have hTGmap := (Submodule.isCloseTo_map_iff Tm).mpr hTG
    have hstart : Submodule.IsViable (F := EE) 0.04 W0
        (T.map Tm.toLinearEquiv.toLinearMap) :=
      (Submodule.IsCloseTo.trans hW0 hGTmap (by norm_num)).of_le (by linarith only [hdelta1])
    obtain ⟨hdimension, hraw⟩ := himprove W0 0.04 hstart (by norm_num)
    let V : Submodule ℂ EM := ⨆ j : Fin (D1 ^ 2), W0.map (Fops j).toLinearMap
    have herr : (delta / 8) / (1 - (0.04 : ℝ)) ^ 2 ≤ delta / 5 := by
      norm_num
      linarith only [hdelta]
    have hsmall : Submodule.IsViable (F := EE) (delta / 5) V
        (T.map Tm.toLinearEquiv.toLinearMap) := Submodule.IsCloseTo.of_le hraw herr
    have hV : Submodule.IsViable (F := EE) (delta / 2) V
        (G.map Tm.toLinearEquiv.toLinearMap) :=
      (Submodule.IsCloseTo.trans hsmall hTGmap (by positivity)).of_le (by linarith)
    have hcomp : e.trans (Submodule.euclideanTensorEquiv (J → Fin q) (↥(Jᶜ) → Fin q)) =
        Tm := by
      ext x
      simp only [e, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
    have hV' : Submodule.IsViable (F := EE) (delta / 2) V
        (G.map (e.trans (Submodule.euclideanTensorEquiv
          (J → Fin q) (↥(Jᶜ) → Fin q))).toLinearEquiv.toLinearMap) := by
      rw [hcomp]
      exact hV
    obtain ⟨φ, hφ, _hφV, hoverlap, hrank⟩ :=
      hV'.exists_unit_schmidtRank_le_of_equiv e (by linarith only [hdelta1]) hψG hψ
    refine ⟨φ, hφ, ?_, hrank.trans ?_⟩
    · nlinarith [norm_nonneg ⟪φ, ψ⟫_ℂ]
    · calc
        Module.finrank ℂ V ≤ D1 ^ 2 * Module.finrank ℂ W0 := hdimension
        _ ≤ D1 ^ 2 * (Module.finrank ℂ G * D0 ^ 24) :=
          Nat.mul_le_mul_left _ hWdim.le
        _ = Module.finrank ℂ G * D0 ^ 24 * D1 ^ 2 := Nat.mul_comm _ _

end TNLean.MPS.AreaLaw
