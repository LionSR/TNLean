/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.LowEnergy.ChebyshevViability
import QICLean.Spectral.LowEnergy.Coordinates
import QICLean.Probability.Sampling.ViableSubspaceBootstrap
import QICLean.Analysis.Subspace.ViableSubspaceCoordinates
import QICLean.Analysis.Subspace.ViableSubspace
import TNLean.MPS.AreaLaw.ActualClippedPolynomialFamily
import QICLean.ManyBody.Sites.Lattice.Chain
import TNLean.MPS.AreaLaw.FiveRegionTruncationResidual
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import TNLean.MPS.AreaLaw.PolynomialFilterParameters
import TNLean.MPS.AreaLaw.ShortRegionViableFamily
import TNLean.MPS.AreaLaw.PhysicalDGLongMiddleFamily

/-!
# A common viable-space enlargement for a gapped chain

For an actual nearest-neighbour Hamiltonian, a universal scalar choice gives a fixed operator
family on any prescribed interval. The target is mutually close to the full original ground
space, and the family improves every viable subspace with error below one. Long intervals use
a clipped spectral cluster; short intervals use configuration matrix units.

These results support ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, and Theorem `t:ais`, lines 1010–1024.
-/

open ManyBody (card_interval_le interval)

section

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- A fixed family on any prescribed middle interval improves viability
for a subspace mutually close to the full original ground space. The scalar
constant is chosen before every chain, Hamiltonian, gap and interval.
A ground spectral value and any strictly higher spectral value are supplied by ALVV,
arXiv:1602.08828v2, Assumption (DG), lines 273–280; the conclusion is the
operator-family assertion of Theorem `t:ais`, lines 1010–1024, with an
explicit logarithmic bound. The gap is normalized internally by its minimum
with one. No upper bound on the original gap, on-site dimension condition,
trace core, canonical spectral basis or boundary margin is assumed.

**Local fix (ground-space cutoff and viability boundary):** The original
comparison space is the full ground space, following the proof of `t:ais`,
line 1020. Its statement at line 1012 prints an extra ground-energy shift.
The improvement formula is used for viability error below one. Both readings
are documented in the companion note
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf.
This assertion concerns existence and the viability estimate; the efficient
MPO construction is a separate result of the source. -/
theorem exists_physical_dg_viable_family :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (L q p r : ℕ), p ≤ r → r ≤ L →
      ∀ (Φ : ManyBody.BondInteraction L q)
        (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let g := min gamma 1
      let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (q * ell ^ 2) ^ (22 * ell)
      let cA : ℝ := 6 + 2 * Real.log (A + 1)
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ ({v // v ∉ J} → Fin q)
      Real.log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 ∧
      ∃ (W : Fin (D ^ 2) → EM →L[ℂ] EM)
        (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ),
        Submodule.IsCloseTo (1 / 200 : ℝ) T G ∧
        Submodule.IsCloseTo (1 / 200 : ℝ) G T ∧
        0 < Delta ∧ (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
        ∀ (S : Submodule ℂ EM) (delta : ℝ),
          Submodule.IsViable (F := EE) delta S
            (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
              (EM ⊗[ℂ] EE))) → delta < 1 →
          Submodule.IsViable (F := EE) (Delta / (1 - delta) ^ (2 : ℕ))
            (⨆ j, S.map (W j : EM →ₗ[ℂ] EM))
            (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
              (EM ⊗[ℂ] EE))) := by
  classical
  obtain ⟨A, hA, hA21, hall⟩ := exists_long_middle_actual_dg_family
  refine ⟨A, hA, hA21, ?_⟩
  intro L q p r hpr hrL Φ h0 h1 mu nu gamma hgamma H hH
    hmu hnu hmunu hgap G g u ell D cA J beta tau U Phi Tm EM EE
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hggamma : g ≤ gamma := min_le_left gamma 1
  have hgapg : ∀ z ∈ spectrum ℝ H, z = mu ∨ mu + g ≤ z := by
    intro z hz
    rcases hgap z hz with hzmu | hzlower
    · exact Or.inl hzmu
    · exact Or.inr (by linarith only [hggamma, hzlower])
  obtain ⟨hell, _hD, hlogD, hlong⟩ := hall q g hq hg hg1
  refine ⟨hlogD, ?_⟩
  by_cases hshort : r - p ≤ 4 * ell
  · have hJ : J.card ≤ 4 * ell :=
      (card_interval_le (L := L) p r).trans hshort
    obtain ⟨W, Delta, hDelta, hbudget, himprove⟩ :=
      exists_short_actual_region_improving_family (F := EE) L q ell J hq
        (Nat.le_trans (by decide : 1 ≤ 21) hell) hJ
    have hGG : Submodule.IsCloseTo (1 / 200 : ℝ) G G :=
      Submodule.isCloseTo_of_le (by norm_num) le_rfl
    refine ⟨W, G, Delta, hGG, hGG, hDelta, hbudget, ?_⟩
    intro S delta hS hdelta
    exact himprove (G.map (Tm.toLinearEquiv :
      EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ] (EM ⊗[ℂ] EE))) S delta hS hdelta
  · obtain ⟨T, Delta, W, hTG, hGT, hDelta, hbudget, himprove⟩ :=
      hlong L p r hpr hrL (Nat.lt_of_not_ge hshort) Φ h0 h1 mu hmu hgapg
    refine ⟨W, T, Delta, hTG, hGT, hDelta, hbudget, ?_⟩
    intro S delta hS hdelta
    exact (himprove S delta hS hdelta).2
end TNLean.MPS.AreaLaw
end

section

section

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- A gapped nearest-neighbour chain has a small viable subspace on every
interval, with the full ground-space dimension as a linear factor. The
improving family and sampling threshold are derived internally. This is
the interval form used at line 1080 in the area-law argument of ALVV,
arXiv:1602.08828v2, supporting Proposition `prop:albootstrap-dg`, lines 1062–1075.

**Scope restriction (contiguous regions):** The physical bootstrap statements
in this module concern intervals. The printed proposition permits arbitrary
subsets, whereas its proof invokes the contiguous-block family.
Disconnected regions do not satisfy the asserted uniform dimension bound,
as a product of adjacent Bell pairs shows. The interval statement suffices
for the area-law theorem. The scope and numerical corrections belong to
https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf.
This theorem is not the unrestricted-subset proposition. -/
theorem exists_physical_interval_viable_subspace :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (L q p r : ℕ), p ≤ r → r ≤ L →
      ∀ (Φ : ManyBody.BondInteraction L q)
        (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let g := min gamma 1
      let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (q * ell ^ 2) ^ (22 * ell)
      let cA : ℝ := 6 + 2 * Real.log (A + 1)
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ ({v // v ∉ J} → Fin q)
      Real.log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 ∧
      ∃ W : Submodule ℂ EM,
        Module.finrank ℂ W < Module.finrank ℂ G * D ^ 24 ∧
        Submodule.IsViable (F := EE) 0.015 W
          (G.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
            (EM ⊗[ℂ] EE))) := by
  classical
  obtain ⟨A, hA, hA21, hfamily⟩ := exists_physical_dg_viable_family
  refine ⟨A, hA, hA21, ?_⟩
  intro L q p r hpr hrL Φ h0 h1 mu nu gamma hgamma H hH
    hmu hnu hmunu hgap G g u ell D cA J beta tau U Phi Tm EM EE
  obtain ⟨hlogD, Fops, T, Delta, hTG, hGT, _hDelta0, hbudget, himprove⟩ :=
    hfamily L q p r hpr hrL Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine ⟨hlogD, ?_⟩
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2) hq)
  have hu1 : 1 ≤ u := by
    have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
    have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
    dsimp only [u]
    linarith only [hlogq, hlogg]
  have hApos : 0 < A := by linarith only [hA]
  have hupos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hellpos : 0 < ell := Nat.ceil_pos.mpr (by positivity)
  have hell1 : 1 ≤ ell := hellpos
  have hbase : 2 ≤ q * ell ^ 2 := by
    calc
      2 ≤ q := hq
      _ = q * 1 := (mul_one q).symm
      _ ≤ q * ell ^ 2 := Nat.mul_le_mul_left q (Left.one_le_pow_of_le hell1 2)
  have hD : 2 ≤ D := hbase.trans
    (le_self_pow (Nat.le_trans (by decide : 1 ≤ 2) hbase)
      (Nat.mul_ne_zero (by decide : (22 : ℕ) ≠ 0) hellpos.ne'))
  have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
  have hdimT : Module.finrank ℂ T = Module.finrank ℂ G :=
    Nat.le_antisymm (hGT.finrank_le (by norm_num)) (hTG.finrank_le (by norm_num))
  have hdimMap : Module.finrank ℂ
      (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
        (EM ⊗[ℂ] EE))) = Module.finrank ℂ G :=
    (LinearEquiv.finrank_map_eq Tm.toLinearEquiv T).trans hdimT
  have hrMap : 1 ≤ Module.finrank ℂ
      (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
        (EM ⊗[ℂ] EE))) := by
    rw [hdimMap]
    exact hrG
  have hGTmap : Submodule.IsCloseTo 0.005
      (G.map Tm.toLinearEquiv.toLinearMap) (T.map Tm.toLinearEquiv.toLinearMap) := by
    rw [show (0.005 : ℝ) = 1 / 200 by norm_num]
    exact (Submodule.isCloseTo_map_iff Tm).mpr hGT
  have hTGmap : Submodule.IsCloseTo 0.005
      (T.map Tm.toLinearEquiv.toLinearMap) (G.map Tm.toLinearEquiv.toLinearMap) := by
    rw [show (0.005 : ℝ) = 1 / 200 by norm_num]
    exact (Submodule.isCloseTo_map_iff Tm).mpr hTG
  have hbudget' : (D : ℝ) ^ 12 * Delta ≤ 0.00001 := by
    simpa only [show (0.00001 : ℝ) = 1 / 100000 by norm_num] using hbudget
  obtain ⟨W, hWdim, hWviable⟩ :=
    Submodule.exists_isViable_finrank_lt_rank_mul_pow hGTmap hTGmap Fops
      (fun delta hdelta S hS ↦ himprove S delta hS hdelta) hD hbudget' hrMap
  refine ⟨W, ?_, hWviable⟩
  simpa only [hdimMap] using hWdim
end TNLean.MPS.AreaLaw
end
end

section

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- One universal choice of scale gives viable families of every numerical
accuracy on every actual interval of a gapped nearest-neighbour chain. The
integer `m` is at least the physical on-site dimension and controls only the
count and error bounds; configurations and the tensor identification remain
those of the original chain. The full ground space is used. Supporting the
accuracy refinement in ALVV, arXiv:1602.08828v2, `thm:al-dg`, lines 1048–1099,
through `t:ais`, lines 1010–1024. No tail or regional spectral estimate is an
input, and no efficient construction is asserted. -/
private theorem exists_accuracy_physical_dg_viable_family :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (L q m p r : ℕ), q ≤ m → p ≤ r → r ≤ L →
      ∀ (Φ : ManyBody.BondInteraction L q)
        (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let g := min gamma 1
      let u : ℝ := 1 + Real.log (m : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (m * ell ^ 2) ^ (22 * ell)
      let cA : ℝ := 6 + 2 * Real.log (A + 1)
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ ({v // v ∉ J} → Fin q)
      21 ≤ ell ∧ m ≤ D ∧ 2 ≤ D ∧
      Real.log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 ∧
      ∃ (W : Fin (D ^ 2) → EM →L[ℂ] EM)
        (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ),
        Submodule.IsCloseTo (1 / (200 * (m : ℝ)) : ℝ) T G ∧
        Submodule.IsCloseTo (1 / (200 * (m : ℝ)) : ℝ) G T ∧
        Module.finrank ℂ T = Module.finrank ℂ G ∧
        0 < Delta ∧ (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
        ∀ (S : Submodule ℂ EM) (delta : ℝ),
          Submodule.IsViable (F := EE) delta S
            (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
              (EM ⊗[ℂ] EE))) → delta < 1 →
          Submodule.IsViable (F := EE) (Delta / (1 - delta) ^ (2 : ℕ))
            (⨆ j, S.map (W j : EM →ₗ[ℂ] EM))
            (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
              (EM ⊗[ℂ] EE))) := by
  classical
  obtain ⟨A, hA, hA21, hall⟩ := exists_accuracy_long_middle_actual_dg_family
  refine ⟨A, hA, hA21, ?_⟩
  intro L q m p r hqm hpr hrL Φ h0 h1 mu nu gamma hgamma H hH
    hmu hnu hmunu hgap G g u ell D cA J beta tau U Phi Tm EM EE
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hggamma : g ≤ gamma := min_le_left gamma 1
  have hgapg : ∀ z ∈ spectrum ℝ H, z = mu ∨ mu + g ≤ z := by
    intro z hz
    rcases hgap z hz with hzmu | hzlower
    · exact Or.inl hzmu
    · exact Or.inr (by linarith only [hggamma, hzlower])
  obtain ⟨hell, hmD, hD, hlogD, hlong⟩ := hall m q g hq hqm hg hg1
  refine ⟨hell, hmD, hD, hlogD, ?_⟩
  by_cases hshort : r - p ≤ 4 * ell
  · have hJ : J.card ≤ 4 * ell :=
      (card_interval_le (L := L) p r).trans hshort
    obtain ⟨W, Delta, hDelta, hbudget, himprove⟩ :=
      exists_short_actual_region_improving_family_of_count_base (F := EE)
        L q m ell J hq hqm (Nat.le_trans (by decide : 1 ≤ 21) hell) hJ
    have hGG : Submodule.IsCloseTo (1 / (200 * (m : ℝ)) : ℝ) G G :=
      Submodule.isCloseTo_of_le (by positivity) le_rfl
    refine ⟨W, G, Delta, hGG, hGG, rfl, hDelta, hbudget, ?_⟩
    intro S delta hS hdelta
    exact himprove (G.map (Tm.toLinearEquiv :
      EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ] (EM ⊗[ℂ] EE))) S delta hS hdelta
  · obtain ⟨T, Delta, W, hTG, hGT, hdim, hDelta, hbudget, himprove⟩ :=
      hlong L p r hpr hrL (Nat.lt_of_not_ge hshort) Φ h0 h1 mu hmu hgapg
    refine ⟨W, T, Delta, hTG, hGT, hdim, hDelta, hbudget, ?_⟩
    intro S delta hS hdelta
    exact (himprove S delta hS hdelta).2
end TNLean.MPS.AreaLaw
end

section

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- The accuracy-dependent physical families and a bootstrap subspace share
one universal scale. The bootstrap family is obtained by setting the numerical
count base equal to the original on-site dimension, before choosing the
families at other accuracies. Consequently its dimension is bounded using
that same scale, rather than an independently chosen constant. Supporting
ALVV, arXiv:1602.08828v2, `prop:albootstrap-dg`, lines 1062–1075, and the
entropy argument of `thm:al-dg`, lines 1080–1099. All tensor coordinates are
those of the actual interval. -/
theorem exists_accuracy_physical_interval_family_and_bootstrap :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (L q p r : ℕ), p ≤ r → r ≤ L →
      ∀ (Φ : ManyBody.BondInteraction L q)
        (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let g := min gamma 1
      let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (q * ell ^ 2) ^ (22 * ell)
      let cA : ℝ := 6 + 2 * Real.log (A + 1)
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ ({v // v ∉ J} → Fin q)
      2 ≤ D ∧
      Real.log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 ∧
      ∃ W0 : Submodule ℂ EM,
        Module.finrank ℂ W0 < Module.finrank ℂ G * D ^ 24 ∧
        Submodule.IsViable (F := EE) 0.015 W0
          (G.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
            (EM ⊗[ℂ] EE))) ∧
        ∀ (m : ℕ), q ≤ m →
          let um : ℝ := 1 + Real.log (m : ℝ) + Real.log (1 / g)
          let ellm : ℕ := ⌈A * um ^ 2 / g⌉₊
          let Dm : ℕ := (m * ellm ^ 2) ^ (22 * ellm)
          21 ≤ ellm ∧ m ≤ Dm ∧ 2 ≤ Dm ∧
          Real.log (Dm : ℝ) ≤ 22 * (A + 1) * cA / g * um ^ 3 ∧
          ∃ (W : Fin (Dm ^ 2) → EM →L[ℂ] EM)
            (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ),
            Submodule.IsCloseTo (1 / (200 * (m : ℝ)) : ℝ) T G ∧
            Submodule.IsCloseTo (1 / (200 * (m : ℝ)) : ℝ) G T ∧
            Module.finrank ℂ T = Module.finrank ℂ G ∧
            0 < Delta ∧ (Dm : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
            ∀ (S : Submodule ℂ EM) (delta : ℝ),
              Submodule.IsViable (F := EE) delta S
                (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
                  (EM ⊗[ℂ] EE))) → delta < 1 →
              Submodule.IsViable (F := EE) (Delta / (1 - delta) ^ (2 : ℕ))
                (⨆ j, S.map (W j : EM →ₗ[ℂ] EM))
                (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
                  (EM ⊗[ℂ] EE))) := by
  classical
  obtain ⟨A, hA, hA21, hfamily⟩ := exists_accuracy_physical_dg_viable_family
  refine ⟨A, hA, hA21, ?_⟩
  intro L q p r hpr hrL Φ h0 h1 mu nu gamma hgamma H hH
    hmu hnu hmunu hgap G g u ell D cA J beta tau U Phi Tm EM EE
  obtain ⟨_hell, _hqD, hD, hlogD, Fops, T, Delta, hTG, hGT,
    hdimT, _hDelta0, hbudget, himprove⟩ :=
    hfamily L q q p r le_rfl hpr hrL Φ h0 h1 mu nu gamma
      hgamma hmu hnu hmunu hgap
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have herror : (1 / (200 * (q : ℝ)) : ℝ) ≤ 1 / 200 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith only [hqR]
  have hGTsmall : Submodule.IsCloseTo (1 / 200 : ℝ) G T := hGT.of_le herror
  have hTGsmall : Submodule.IsCloseTo (1 / 200 : ℝ) T G := hTG.of_le herror
  have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
  have hdimMap : Module.finrank ℂ
      (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
        (EM ⊗[ℂ] EE))) = Module.finrank ℂ G :=
    (LinearEquiv.finrank_map_eq Tm.toLinearEquiv T).trans hdimT
  have hrMap : 1 ≤ Module.finrank ℂ
      (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
        (EM ⊗[ℂ] EE))) := by
    rw [hdimMap]
    exact hrG
  have hGTmap : Submodule.IsCloseTo 0.005
      (G.map Tm.toLinearEquiv.toLinearMap) (T.map Tm.toLinearEquiv.toLinearMap) := by
    rw [show (0.005 : ℝ) = 1 / 200 by norm_num]
    exact (Submodule.isCloseTo_map_iff Tm).mpr hGTsmall
  have hTGmap : Submodule.IsCloseTo 0.005
      (T.map Tm.toLinearEquiv.toLinearMap) (G.map Tm.toLinearEquiv.toLinearMap) := by
    rw [show (0.005 : ℝ) = 1 / 200 by norm_num]
    exact (Submodule.isCloseTo_map_iff Tm).mpr hTGsmall
  have hbudget' : (D : ℝ) ^ 12 * Delta ≤ 0.00001 := by
    simpa only [show (0.00001 : ℝ) = 1 / 100000 by norm_num] using hbudget
  obtain ⟨W0, hWdim, hWviable⟩ :=
    Submodule.exists_isViable_finrank_lt_rank_mul_pow hGTmap hTGmap Fops
      (fun delta hdelta S hS ↦ himprove S delta hS hdelta) hD hbudget' hrMap
  refine ⟨hD, hlogD, W0, ?_, hWviable, ?_⟩
  · simpa only [hdimMap] using hWdim
  · intro m hqm um ellm Dm
    exact hfamily L q m p r hqm hpr hrL Φ h0 h1 mu nu gamma
      hgamma hmu hnu hmunu hgap
end TNLean.MPS.AreaLaw
end
