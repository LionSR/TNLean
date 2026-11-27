/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.SharpApproximationParameters
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.PhysicalDGViability
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.IndependentPhysicalDGPower
import QICLean.Channel.Schmidt.ViableSubspaceSchmidtRank
import TNLean.MPS.Tensor.OpenMPS.NormalizedSequentialApproximation
import QICLean.Analysis.Real.LogRankRounding
import QICLean.ManyBody.Entropy.ViableSubspaceEntropy
import QICLean.Channel.Schmidt.MaximalOverlap

/-!
# The explicit sharp logarithmic-rank estimate

The physical normalized approximation retains one logarithm of the full
ground-space dimension. Its remaining rank cost has inverse-gap cubic local
logarithms and a quarter-power gap, three-quarter-power accuracy term, with
an explicit logarithmic correction. This supports the fixed-cut conclusion
of ALVV, arXiv:1602.08828v2, Theorem 4.9, source lines 1048–1085.

**Local fix (parameter choice):** Independent scales replace the printed
nonuniform prescription; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Scope restriction (gap dependence):** The bound uses `min gamma 1`.
For `0 < gamma ≤ 1` this is the printed quantitative dependence; for larger
gaps it costs the factor `max gamma 1 ≤ 1 + log r / log q` in the exponent,
as proved in `TNLean.MPS.AreaLaw.ALVV.LargeGapComparison` and recorded in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.

The distinct spectral values express Assumption (DG) of the source,
lines 275–279, which requires a second smallest eigenvalue.

It also contains the following results.

* `TNLean.MPS.AreaLaw.exists_physical_dg_normalized_approximation_of_independent_scales`: normalized
  approximations from the full physical ground space.
* `TNLean.MPS.AreaLaw.exists_physical_dg_normalized_isOpenMPS_approximation`: one physical matrix
  product approximant at all cuts.
-/

section PhysicalDGApproximation

/-!
## Normalized approximations from the full physical ground space

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

open ManyBody (card_interval_le interval)

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
      let D0 : ℕ := (q * ell ^ 2) ^ (22 * ell)
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
      2 ≤ D0 ∧
      Real.log (D0 : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let a := 16 + Real.log (1 / g) + Real.log (1 / delta)
      ∃ ell1 : ℕ, 1 ≤ ell1 ∧
      (ell1 : ℝ) ≤ 8 / (4 * g / 5) +
        (7 * C) ^ (1 / 4 : ℝ) * (1 / (4 * g / 5)) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) ∧
      let D1 : ℕ := (q * ell1 ^ 2) ^ (22 * ell1)
      let e := Tm.trans
        (Submodule.euclideanTensorEquiv (J → Fin q) ({v // v ∉ J} → Fin q)).symm
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G → ‖ψ‖ = 1 →
      ∃ φ : EuclideanSpace ℂ (Fin L → Fin q), ‖φ‖ = 1 ∧
        1 - delta ≤ ‖⟪φ, ψ⟫_ℂ‖ ∧
        Matrix.schmidtRank (WithLp.ofLp (e φ)) ≤ Module.finrank ℂ G * D0 ^ 24 * D1 ^ 2 := by
  classical
  obtain ⟨A, hA, _hA21, hphysical⟩ := exists_accuracy_physical_interval_family_and_bootstrap
  obtain ⟨C, hC, hscalar⟩ := Real.exists_sharp_approximation_scalar_parameters
  refine ⟨A, C, hA, hC, ?_⟩
  intro L q p r hpr hrL Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G g u ell D0 cA J beta tau U Phi Tm
  let EM := EuclideanSpace ℂ (J → Fin q)
  let EE := EuclideanSpace ℂ ({v // v ∉ J} → Fin q)
  obtain ⟨hD0, hlogD0, W0, hWdim, hW0, _hcoarse⟩ :=
    hphysical L q p r hpr hrL Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
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
        L p r hpr hrL (Nat.lt_of_not_ge hshort) Φ h0 h1 mu hmu hgapg
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
    have hcomp : e.trans (Submodule.euclideanTensorEquiv (J → Fin q) ({v // v ∉ J} → Fin q)) =
        Tm := by
      ext x
      simp only [e, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
    have hV' : Submodule.IsViable (F := EE) (delta / 2) V
        (G.map (e.trans (Submodule.euclideanTensorEquiv
          (J → Fin q) ({v // v ∉ J} → Fin q))).toLinearEquiv.toLinearMap) := by
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

end PhysicalDGApproximation

section PhysicalDGSharpApproximation

open ManyBody (interval)

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- A normalized approximation to every original unit ground vector satisfies
the explicit logarithmic Schmidt-rank estimate at each actual interval cut.
No rank, overlap or approximation premise is supplied. The universal constant
precedes the chain, Hamiltonian, gap, interval, accuracy and ground vector.
Supporting ALVV, arXiv:1602.08828v2, Theorem 4.9, fixed-cut conclusion,
source lines 1048–1085. -/
theorem exists_physical_dg_interval_normalized_approximation :
    ∃ K : ℝ, 0 < K ∧
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
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      let e := Tm.trans (Submodule.euclideanTensorEquiv (J → Fin q) ({v // v ∉ J} → Fin q)).symm
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let a := 16 + Real.log (1 / g) + Real.log (1 / delta)
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G → ‖ψ‖ = 1 →
      ∃ φ : EuclideanSpace ℂ (Fin L → Fin q), ‖φ‖ = 1 ∧
        1 - delta ≤ ‖⟪φ, ψ⟫_ℂ‖ ∧
        Real.log (Matrix.schmidtRank (WithLp.ofLp (e φ)) : ℝ) ≤
          Real.log (Module.finrank ℂ G : ℝ) +
          K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
            (1 + Real.log a) := by
  classical
  obtain ⟨A, C, hA, hC, hraw⟩ :=
    exists_physical_dg_normalized_approximation_of_independent_scales
  let cA : ℝ := 6 + 2 * Real.log (A + 1)
  let K0 : ℝ := 22 * (A + 1) * cA
  let b : ℝ := (7 * C) ^ (1 / 4 : ℝ) * (5 / 4 : ℝ) ^ (1 / 4 : ℝ)
  have hlogA : 0 ≤ Real.log (A + 1) := Real.log_nonneg (by linarith only [hA])
  have hK0 : 0 ≤ K0 := by dsimp only [K0, cA]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hlogb : 0 ≤ Real.log (11 + b) := Real.log_nonneg (by linarith only [hb])
  let K := 24 * K0 + 88 * (1 + Real.log (11 + b)) * (11 + b)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro L q p r hpr hrL Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G g u J beta tau U Phi Tm e
  let ell0 : ℕ := ⌈A * u ^ 2 / g⌉₊
  let D0 : ℕ := (q * ell0 ^ 2) ^ (22 * ell0)
  obtain ⟨hD0, hlogD0, happrox⟩ :=
    hraw L q p r hpr hrL Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  have hD02 : 2 ≤ D0 := hD0
  have hbootstrap : Real.log (D0 : ℝ) ≤ K0 / g * u ^ 3 := hlogD0
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
  intro delta hdelta hdelta1 a ψ hψG hψ
  obtain ⟨ell1, hell1, hwindow, hvectors⟩ := happrox delta hdelta hdelta1
  let D1 : ℕ := (q * ell1 ^ 2) ^ (22 * ell1)
  obtain ⟨φ, hφ, hoverlap, hrank⟩ := hvectors ψ hψG hψ
  have hfrac : 1 / (4 * g / 5) = (5 / 4 : ℝ) * (1 / g) := by field_simp
  have hten : 8 / (4 * g / 5) = 10 / g := by
    field_simp
    norm_num
  have hwindow' : (ell1 : ℝ) ≤
      10 / g + b * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) := by
    rw [hten, hfrac, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5 / 4)
      (by positivity : (0 : ℝ) ≤ 1 / g)] at hwindow
    simpa only [b, mul_assoc] using hwindow
  have ha : 1 ≤ a := by
    have hlogg := Real.log_nonneg ((one_le_div hg).2 hg1)
    have hlogdelta := Real.log_nonneg ((one_le_div hdelta).2 hdelta1)
    dsimp only [a]
    linarith only [hlogg, hlogdelta]
  have hbudget : Real.log ((Module.finrank ℂ G * D0 ^ 24 * D1 ^ 2 : ℕ) : ℝ) ≤
      Real.log (Module.finrank ℂ G : ℝ) +
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log a) :=
    Real.sharp_approximation_log_rank_budget (Module.finrank ℂ G) D0 q ell1 g a K0 b
      hrG (by omega) (by omega) hell1 hg hg1 ha hK0 hb hwindow' hbootstrap
  refine ⟨φ, hφ, hoverlap, ?_⟩
  by_cases hzero : Matrix.schmidtRank (WithLp.ofLp (e φ)) = 0
  · rw [hzero, Nat.cast_zero, Real.log_zero]
    exact (Real.log_natCast_nonneg (Module.finrank ℂ G * D0 ^ 24 * D1 ^ 2)).trans hbudget
  · have hpos : (0 : ℝ) < (Matrix.schmidtRank (WithLp.ofLp (e φ)) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    exact (Real.log_le_log hpos (by exact_mod_cast hrank)).trans hbudget

end TNLean.MPS.AreaLaw

end PhysicalDGSharpApproximation

section PhysicalDGGlobalApproximation

/-!
## One physical matrix product approximant at all cuts

Fixed-cut normalized approximants control the discarded spectral mass of the
original marginals. The output vector is the single sequential truncation
onto their leading eigenspaces, followed by normalization. This supports the
global matrix product state conclusion of ALVV, arXiv:1602.08828v2,
Theorem 4.9, source lines 1080–1086.

**Local fix (parameter choice):** The independent scales are documented in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Scope restriction (gap dependence):** The bound uses `min gamma 1`.
For `0 < gamma ≤ 1` this is the printed quantitative dependence; for larger
gaps it costs the factor `max gamma 1 ≤ 1 + log r / log q` in the exponent,
as proved in `TNLean.MPS.AreaLaw.ALVV.LargeGapComparison` and recorded in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.

The distinct spectral values express Assumption (DG) of the source,
lines 275–279, which requires a second smallest eigenvalue.
-/

open ManyBody (interval)

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- Every original ground vector has one normalized open-boundary matrix
product approximant with simultaneous bond control at all cuts. The factor
beyond the ground-space dimension is chosen before the vector. The proof
constructs one sequential projection product and then normalizes it.
Supporting ALVV, arXiv:1602.08828v2, Theorem 4.9, global conclusion,
source lines 1080–1086. -/
theorem exists_physical_dg_normalized_isOpenMPS_approximation :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q : ℕ),
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
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let b := 16 + Real.log (1 / g) + Real.log (16 * ((L : ℝ) + 1) / delta)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G → ‖ψ‖ = 1 →
      ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
        IsOpenMPS L q (Module.finrank ℂ G * B) (fun x ↦ Φ x) ∧
        1 - delta ≤ ‖⟪Φ, ψ⟫_ℂ‖ ∧ ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
  classical
  obtain ⟨K, hK, hfixed⟩ := exists_physical_dg_interval_normalized_approximation
  refine ⟨K + 1, by linarith only [hK], ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap G g u
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogq, hlogg]
  intro delta hdelta hdelta1 b
  let deltaCut := delta / (16 * ((L : ℝ) + 1))
  have hden : 0 < 16 * ((L : ℝ) + 1) := by positivity
  have hcut : 0 < deltaCut := div_pos hdelta hden
  have hcut1 : deltaCut ≤ 1 := by
    apply (div_le_iff₀ hden).2
    have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
    linarith only [hdelta1, hL]
  have hrecip : 1 / deltaCut = 16 * ((L : ℝ) + 1) / delta := by
    dsimp only [deltaCut]
    field_simp
  have hb : 16 ≤ b := by
    have hlogcut := Real.log_nonneg ((one_le_div hcut).2 hcut1)
    rw [hrecip] at hlogcut
    dsimp only [b]
    linarith only [hlogg, hlogcut]
  let F := u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u
  have hbase : 1 ≤ u ^ 3 / g := (le_div_iff₀ hg).2 (by
    have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu
    linarith only [hu3, hg1])
  have hroot : 0 ≤ (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u := by positivity
  have hsum : 1 ≤ u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u := by
    linarith only [hbase, hroot]
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg (by linarith only [hb])
  have hF : 1 ≤ F := hsum
  have hPone : 1 ≤ 1 + Real.log b := by linarith only [hlogb]
  have hFP : 1 ≤ F * (1 + Real.log b) := by
    simpa only [one_mul] using
      (mul_le_mul hF hPone (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans hF))
  let E := K * F * (1 + Real.log b)
  have hE : 0 ≤ E := mul_nonneg (mul_nonneg hK.le (zero_le_one.trans hF))
    (zero_le_one.trans hPone)
  let B : ℕ := ⌈Real.exp E⌉₊
  obtain ⟨hB, hlogB⟩ := Real.log_ceil_exp_le_add_one E hE
  refine ⟨B, hB, ?_, ?_⟩
  · change Real.log (B : ℝ) ≤ (K + 1) * F * (1 + Real.log b)
    change Real.log (B : ℝ) ≤ E + 1 at hlogB
    dsimp only [E] at hlogB
    nlinarith only [hlogB, hFP]
  · intro ψ hψG hψ
    have htail : ∀ k ∈ Finset.Ico 1 L,
        1 - (ManyBody.regionState_isHermitian (X := fun _ ↦ Fin q)
          (interval L 0 k) ψ).kyFanNorm (Module.finrank ℂ G * B) ≤
            delta / (8 * ((L : ℝ) + 1)) := by
      intro k hk
      have hkL : k ≤ L := (Finset.mem_Ico.mp hk).2.le
      obtain ⟨φ, hφ, hoverlap, hlogrank⟩ :=
        hfixed L q 0 k (Nat.zero_le k) hkL Φ h0 h1 mu nu gamma hgamma
          hmu hnu hmunu hgap deltaCut hcut hcut1 ψ hψG hψ
      rw [hrecip] at hlogrank
      have hregional := one_sub_regional_kyFanNorm_le_twice_error
        (interval L 0 k) ψ φ hφ deltaCut hcut1 (Module.finrank ℂ G * B)
        (Nat.le_mul_ceil_exp_of_log_le hrG E hlogrank) hoverlap
      convert hregional using 1
      dsimp only [deltaCut]
      field_simp; ring
    exact exists_unit_mps_of_uniform_prefix_mass ψ hψ (Module.finrank ℂ G * B)
      delta hdelta hdelta1 htail

end TNLean.MPS.AreaLaw

end PhysicalDGGlobalApproximation
