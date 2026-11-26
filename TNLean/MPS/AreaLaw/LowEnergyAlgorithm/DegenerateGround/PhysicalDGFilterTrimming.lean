/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Hamiltonian.Models
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.FullIntervalFilterTrimming
import QICLean.Spectral.Filter.GroundSpaceAffineFilter
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.FullIntervalFilterIteration
import QICLean.Analysis.Parameter.QuantitativeFilterIteration
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.FullIntervalViability
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.PhysicalGroundReference
import QICLean.Analysis.Parameter.ViableRefinementParameters
import QICLean.Spectral.LowEnergy.RitzGroundSpaceCloseness
import QICLean.Analysis.Parameter.RefinementOutputPolynomialBound
import TNLean.MPS.Tensor.OpenMPS.OpenMPSCutRank
import QICLean.Spectral.Eigenvalue.RitzCompression
import QICLean.Analysis.Subspace.ViableSubspace

/-!
# The physical full-ground filter at the same root

The filter is constructed from the actual positive chain Hamiltonian, its
original ground energy and its operator norm. The two actual distinct
spectral values and the original global gap determine its positive
normalization and complementary contraction. The complete ground space
is retained, with no uniqueness assumption or gap cap.

This supports ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1620–1643,
and the final refinement in `t:alg1`, lines 1809–1817. The reference and
trimming threshold remain explicit in the one-step auxiliary; their automatic
choice and the repeated iteration are separate.

**Local fix (normalized gain):** The normalized error estimate replaces
the printed raw multiplicative overlap gain. The actual image and trim
spaces equal those obtained from the printed unnormalized filter; see
`docs/paper-gaps/alvv16_final_filter_gain.tex`.

## Finite refinement of the same physical root

One fixed reference and threshold control every actual raw-filter-and-trim
iterate. The target is the full original ground space throughout. The
stable scalar recurrence reaches every positive requested error, while
the literal spaces retain the original dimension budget and their actual
trimmed spanning vectors.

This supports ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1634–1640,
and its final refinement argument, lines 1809–1817. Physical reference
selection and Ritz extraction are separate applications. No printed
iteration count or algorithmic running time is asserted here.

**Local fix (normalized gain):** The raw operation is compared with its
nonzero normalized multiple as in `docs/paper-gaps/alvv16_final_filter_gain.tex`.
The proof uses the corrected error recurrence.

## Automatic common-reference refinement of the same candidate

The physical reference and positive threshold are chosen before every
initial candidate. They fit both the original tree threshold and the
strict source threshold inequality. The terminal space is a literal
raw-filter-and-trim iterate of the given candidate, and its actual
compressed Ritz space approximates the original full ground space.
Its MPS bound follows from the recorded terminal trimming vectors,
including the additional spanning-family factor.

This is a parameter-selection and refinement auxiliary for ALVV,
arXiv:1602.08828v2, `eq:algo-xi-dg`, lines 1800–1805, and final refinement,
lines 1809–1817. The initial-candidate hypothesis is discharged by the
actual common-radius tree in the subsequent composition.

**Scope restriction (reference gap dependence):** The reference estimate
uses `min gamma 1`; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.
No adaptive sampling probability or running time is asserted.

**Local fix (normalized gain):** The literal raw-filter iterates use the
corrected recurrence recorded in `docs/paper-gaps/alvv16_final_filter_gain.tex`.
The printed iteration count is not identified with this accuracy choice.

## Polynomial refinement of any actual viable root

One positive refinement radius and number of literal rounds precede every
initial candidate. The resulting Ritz space is extracted from that same
candidate's actual filter-and-trim iterate. The coefficient of the squared
candidate count has a polynomial bound fixed before length, multiplicity
and accuracy. No initial matrix product representation is assumed.

This is a conditional final-refinement auxiliary for ALVV,
arXiv:1602.08828v2, lines 1801–1817. It does not construct an initial tree
or identify its trimming radius with the final refinement radius.

**Scope restriction (reference gap dependence):** The reference estimate
uses the capped gap; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.
**Local fix (normalized gain):** The iterate is the corrected literal raw
filter from `docs/paper-gaps/alvv16_final_filter_gain.tex`. In the flat
spectral branch zero rounds retain the given root exactly.

It also contains the following results.

* `TNLean.MPS.AreaLaw.flat_ground_same_root_ritz_exact`: exact Ritz extraction from the same root in
  the flat case.
-/

section PhysicalFlatGroundRitz

/-!
## Exact Ritz extraction from the same root in the flat case

Under a spectral gap implication, absence of an excited spectral value makes
all eigenvalues equal to the ground energy. The original ground space is the
whole space. A candidate approximating it with error below one is therefore
that same whole space, not an independently chosen approximation.

Zero rounds of the literal filter-and-trim operation retain the given root.
Its actual full-rank Ritz space is exact, and every vector has MPS bond at
most the ground multiplicity, hence at most the supplied dimension bound.
The raw filter is not applied; it may vanish for a scalar Hamiltonian.

This is the flat-case auxiliary for a gap-implication-only formulation of
ALVV, arXiv:1602.08828v2, final extraction in Figure `fig:algo1`, lines
1641–1643 and 1814–1817. The source's nonflat `(DG)` assumption is not
replaced by an extra excited-value hypothesis in such a formulation.
-/

open ManyBody (interval)
open ManyBody (cutMatrix)

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A given root close to the full ground space is retained exactly when
there is no excited spectral value. Zero literal refinement rounds and the
actual same-root Ritz extraction give zero error and bond at most the ground
multiplicity or the supplied count. Auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1641–1643 and 1814–1817. -/
theorem flat_ground_same_root_ritz_exact {L q count : ℕ}
    {H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hH : H.IsHermitian)
    (mu gamma delta : ℝ) (hgamma : 0 < gamma) (hmu : mu ∈ spectrum ℝ H)
    (hgap : ∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z)
    (hflat : ¬ ∃ nu ∈ spectrum ℝ H, mu < nu)
    (S0 : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)))
    (hcount : Module.finrank ℂ S0 ≤ count) :
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let r := Module.finrank ℂ G
    let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (1 - ‖H‖⁻¹ • H)
    Submodule.IsCloseTo delta (nativeFullIntervalSpace L q S0) G → delta < 1 →
    ∀ xi : ℝ,
    let S := fullIntervalFilterTrimIterate L q Kraw xi S0 0
    let W := nativeFullIntervalSpace L q S
    let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) r
    G = ⊤ ∧ S0 = ⊤ ∧ S = S0 ∧ W = G ∧ R = W ∧
      Module.finrank ℂ R = r ∧
      Submodule.IsCloseTo 0 G R ∧ Submodule.IsCloseTo 0 R G ∧ r ≤ count ∧
      ∀ v ∈ R, IsOpenMPS L q r (fun x ↦ v x) ∧
        IsOpenMPS L q count (fun x ↦ v x) := by
  classical
  intro G r Kraw hclose hdelta xi S W R
  have heig (i) : hH.eigenvalues i = mu := by
    rcases hgap _ (hH.eigenvalues_mem_spectrum_real i) with hi | hi
    · exact hi
    · exact False.elim (hflat ⟨_, hH.eigenvalues_mem_spectrum_real i,
        by linarith only [hi, hgamma]⟩)
  have hGtop : G = ⊤ := by
    apply top_unique
    intro v _
    apply (Submodule.mem_spectralSpanLE_iff _ _ _ _).mpr
    intro i hi
    simp only [heig i, lt_self_iff_false] at hi
  have hWtop : W = ⊤ := by
    apply Submodule.eq_of_le_of_finrank_le le_top
    have hdim := hclose.finrank_le hdelta
    change Module.finrank ℂ G ≤ Module.finrank ℂ W at hdim
    rw [hGtop] at hdim
    exact hdim
  have hWG : W = G := hWtop.trans hGtop.symm
  have hS0top : S0 = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    calc
      Module.finrank ℂ S0 = Module.finrank ℂ W :=
        ((fullIntervalEquiv L q).toLinearEquiv.finrank_map_eq S0).symm
      _ = Module.finrank ℂ (EuclideanSpace ℂ (Fin L → Fin q)) := by rw [hWtop]; simp
      _ = Module.finrank ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)) :=
        (fullIntervalEquiv L q).toLinearEquiv.finrank_eq.symm
  have hdimW : Module.finrank ℂ W = r := by rw [hWG]
  have hRle : R ≤ W := W.ritzSubspace_le
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) r
  have hdimR : Module.finrank ℂ R = r := W.finrank_ritzSubspace
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) r hdimW.ge
  have hRW : R = W := Submodule.eq_of_le_of_finrank_eq hRle (hdimR.trans hdimW.symm)
  have hGR : Submodule.IsCloseTo 0 G R := by
    rw [hRW, hWG]
    exact Submodule.isCloseTo_of_le (by norm_num) le_rfl
  have hRG : Submodule.IsCloseTo 0 R G := by
    rw [hRW, hWG]
    exact Submodule.isCloseTo_of_le (by norm_num) le_rfl
  have hrCount : r ≤ count := by
    calc
      r = Module.finrank ℂ W := hdimW.symm
      _ = Module.finrank ℂ S0 := (fullIntervalEquiv L q).toLinearEquiv.finrank_map_eq S0
      _ ≤ count := hcount
  refine ⟨hGtop, hS0top, rfl, hWG, hRW, hdimR, hGR, hRG, hrCount, ?_⟩
  have hconfig : Nonempty (Fin L → Fin q) := by
    by_contra hempty
    have : IsEmpty (Fin L → Fin q) := not_nonempty_iff.mp hempty
    simp only [spectrum.of_subsingleton, Set.mem_empty_iff_false] at hmu
  let config : Fin L → Fin q := Classical.choice hconfig
  intro v _
  have hv : IsOpenMPS L q r (fun x ↦ v x) := by
    apply (isOpenMPS_iff_internal_cutMatrix_rank_le v).mpr
    intro k hk0 hkL
    have hq : 1 ≤ q := by
      have hvalue := (config ⟨0, by omega⟩).isLt
      omega
    calc
      (cutMatrix (leftBlock L k) v).rank ≤
          Fintype.card ((w : {w : Fin L // w ∈ leftBlock L k}) → Fin q) :=
        Matrix.rank_le_card_height _
      _ = q ^ Fintype.card {w : Fin L // w ∈ leftBlock L k} := by simp
      _ ≤ q ^ L := Nat.pow_le_pow_right hq (by
        simpa using Fintype.card_subtype_le (fun w : Fin L ↦ w ∈ leftBlock L k))
      _ = r := by
        change q ^ L = Module.finrank ℂ G
        rw [hGtop]
        simp
  exact ⟨hv, hv.mono hrCount⟩

end TNLean.MPS.AreaLaw

end PhysicalFlatGroundRitz

section PhysicalDGFilterTrimming

section

open ManyBody (interval)

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

private theorem fullIntervalFilterTrimStep_smul {L q : ℕ} {a : ℂ} (ha : a ≠ 0)
    (K : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q))
    (xi : ℝ) (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) :
    fullIntervalFilterTrimStep L q (a • K) xi S = fullIntervalFilterTrimStep L q K xi S := by
  have hfilter : fullIntervalFilter L q (a • K) = a • fullIntervalFilter L q K := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [fullIntervalFilter_apply, smul_apply, map_smul]
  have himage : S.map (fullIntervalFilter L q (a • K)).toLinearMap =
      S.map (fullIntervalFilter L q K).toLinearMap := by
    rw [hfilter]
    exact Submodule.map_smul (fullIntervalFilter L q K).toLinearMap S a ha
  exact congrArg (fun V : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)) ↦
    intervalTrimSubspace L q 0 L xi (fun i ↦ ((stdOrthonormalBasis ℂ V) i : _))) himage

/-- Multiplying the actual affine filter by its nonzero ground-energy
normalization leaves every full-interval filter-and-trim space unchanged.
The standard basis and trim are those of the same image subspace.
Supporting ALVV, arXiv:1602.08828v2, final filter, lines 1620–1643. -/
theorem fullIntervalFilterTrimStep_normalized_affine_eq_raw
    {L q : ℕ} (H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (mu M : ℝ) (hM : M ≠ 0) (hden : M - mu ≠ 0)
    (xi : ℝ) (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) :
    fullIntervalFilterTrimStep L q
      (Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        ((M - mu)⁻¹ • (M • 1 - H))) xi S =
      fullIntervalFilterTrimStep L q
        (Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - M⁻¹ • H)) xi S := by
  have hnormal : 1 - mu / M ≠ 0 := by
    rw [← div_self hM, ← sub_div]
    exact div_ne_zero hden hM
  rw [← Matrix.normalized_affine_filter_eq_smul_raw H mu M hM,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [map_smul]
  exact fullIntervalFilterTrimStep_smul (Complex.ofReal_ne_zero.mpr (inv_ne_zero hnormal)) _ xi S

/-- The actual positive chain supplies a normalized filter for its original
full degenerate ground space: the chain case of
`Matrix.PosSemidef.normalized_affine_ground_filter_spec_of_norm`. Supporting ALVV,
arXiv:1602.08828v2, hypothesis (DG), lines 275–279, and final filter, lines 1620–1643. -/
theorem physical_dg_normalized_ground_filter_spec
    {L q : ℕ} (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (mu nu gamma : ℝ) (hgamma : 0 < gamma) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let M := ‖H‖
    let K := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      ((M - mu)⁻¹ • (M • 1 - H))
    let c := gamma / (M - mu)
    0 < M ∧ 0 < M - mu ∧ 0 < c ∧ c ≤ 1 ∧
      (∀ x ∈ G, K x = x) ∧
      (∀ x ∈ Gᗮ, K x ∈ Gᗮ) ∧
      ∀ x ∈ Gᗮ, ‖K x‖ ^ 2 ≤ (1 - c) * ‖x‖ ^ 2 := by
  intro H hH hmu hnu hmunu hgap
  exact Matrix.PosSemidef.normalized_affine_ground_filter_spec_of_norm
    (Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ ↦ h0 i)) hgamma hmu hnu hmunu hgap

/-- One actual physical filter and collective trim of the given root
obeys the stable recurrence for the original full ground space. The
printed raw filter produces exactly the same image and trimmed spaces as
its nonzero ground-normalized multiple. The filter and its contraction
are derived from the actual Hamiltonian;
the common reference and numerical trimming budgets are explicit inputs.
Supporting ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1809–1817. -/
theorem isCloseTo_nativeFullIntervalSpace_filterTrimStep_of_physical_dg
    {L q : ℕ} (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (mu nu gamma : ℝ) (hgamma : 0 < gamma) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let M := ‖H‖
    let K := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - M⁻¹ • H)
    let c := gamma / (M - mu)
    ∀ (D : ℕ), 1 ≤ D →
    ∀ (U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (epsilon eta xi delta : ℝ),
    0 ≤ epsilon → 0 < xi → 0 ≤ delta → delta ≤ 1 / 2 →
    Submodule.IsCloseTo epsilon G U → Submodule.IsCloseTo epsilon U G →
    (∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x)) →
    epsilon ≤ c ^ 2 * eta / 1024 →
    xi * Real.sqrt (((L - 1 : ℕ) : ℝ) * (D ^ 2 : ℕ)) ≤ c * eta / 48 →
    ∀ (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))),
    Submodule.IsCloseTo delta (nativeFullIntervalSpace L q S) G →
    Submodule.IsCloseTo ((1 - c / 4) * delta + c * eta / 8)
      (nativeFullIntervalSpace L q (fullIntervalFilterTrimStep L q K xi S)) G := by
  intro H hH hmu hnu hmunu hgap G M K c D hD U epsilon eta xi delta
    hepsilon hxi hdelta0 hdelta hGU hUG hU hepsilonBudget hxiBudget S hS
  let Kn := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    ((M - mu)⁻¹ • (M • 1 - H))
  obtain ⟨hM, hden, hc, hc1, hfix, hKGo, hhigh⟩ :=
    physical_dg_normalized_ground_filter_spec Φ h0 mu nu gamma hgamma
      hmu hnu hmunu hgap
  have hnext := isCloseTo_nativeFullIntervalSpace_filterTrimStep hD hxi hc hc1
    hdelta0 hdelta hepsilon Kn (fun x hx ↦ by rw [hfix x hx]; exact hx) hKGo
    (fun x hx ↦ by rw [hfix x hx]) hhigh hGU hUG hU hepsilonBudget hxiBudget S hS
  dsimp only [Kn] at hnext
  rw [fullIntervalFilterTrimStep_normalized_affine_eq_raw H mu M hM.ne' hden.ne' xi S] at hnext
  exact hnext

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- An explicit logarithmic number of actual raw-filter-and-trim steps reaches
the requested projection error. The common reference and threshold precede
the initial candidate. The iteration count is expressed in terms of that
projection error, not the final Ritz energy tolerance. Auxiliary to ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1809–1817. -/
theorem physical_dg_filterTrimIterate_ceil_log_isCloseTo
    {L q : ℕ} (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (mu nu gamma : ℝ) (hgamma : 0 < gamma) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let M := ‖H‖
    let K := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - M⁻¹ • H)
    let c := gamma / (M - mu)
    ∀ (D : ℕ), 1 ≤ D →
    ∀ (U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (epsilon rho xi delta0 : ℝ),
    0 ≤ epsilon → 0 < rho → rho ≤ 1 → 0 < xi → 0 ≤ delta0 → delta0 ≤ 1 / 2 →
    Submodule.IsCloseTo epsilon G U → Submodule.IsCloseTo epsilon U G →
    (∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x)) →
    epsilon ≤ c ^ 2 * rho / 1024 →
    xi * Real.sqrt (((L - 1 : ℕ) : ℝ) * (D ^ 2 : ℕ)) ≤ c * rho / 48 →
    ∀ (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))),
    Submodule.IsCloseTo delta0 (nativeFullIntervalSpace L q S) G →
    let n := ⌈4 / c * Real.log (1 / rho)⌉₊ + 1
    0 < n ∧
      Submodule.IsCloseTo rho
        (nativeFullIntervalSpace L q (fullIntervalFilterTrimIterate L q K xi S n)) G ∧
      Module.finrank ℂ (fullIntervalFilterTrimIterate L q K xi S n) ≤ Module.finrank ℂ S ∧
      IsIntervalSpanWithRankBound L q 0 L (Module.finrank ℂ S) xi
        (fullIntervalFilterTrimIterate L q K xi S n) := by
  intro H hH hmu hnu hmunu hgap G M K c D hD U epsilon rho xi delta0
    hepsilon hrho hrho1 hxi hdelta0 hdelta0half hGU hUG hU hepsilonBudget hxiBudget S hS n
  obtain ⟨_hM, _hden, hc, hc1, _hfix, _hKGo, _hhigh⟩ :=
    physical_dg_normalized_ground_filter_spec Φ h0 mu nu gamma hgamma hmu hnu hmunu hgap
  change 0 < c at hc
  change c ≤ 1 at hc1
  let u : ℕ → ℝ := Nat.rec delta0 (fun _ d ↦ (1 - c / 4) * d + c * rho / 8)
  have hstep : ∀ n, u n ≤ 1 / 2 → u (n + 1) ≤ (1 - c / 4) * u n + c * rho / 8 :=
    fun _ _ ↦ le_rfl
  have hstable := Real.filter_trim_iterate_le hc hc1 hrho.le hrho1 u hdelta0half hstep
  have hu0 : ∀ n, 0 ≤ u n := by
    intro n
    induction n with
    | zero => exact hdelta0
    | succ n ih =>
      exact add_nonneg (mul_nonneg (by linarith) ih) (by positivity)
  have hall : ∀ n, Submodule.IsCloseTo (u n)
      (nativeFullIntervalSpace L q (fullIntervalFilterTrimIterate L q K xi S n)) G := by
    intro n
    induction n with
    | zero => exact hS
    | succ n ih =>
      exact isCloseTo_nativeFullIntervalSpace_filterTrimStep_of_physical_dg
        Φ h0 mu nu gamma hgamma hmu hnu hmunu hgap D hD U epsilon rho xi (u n)
        hepsilon hxi (hu0 n) (hstable.1 n) hGU hUG hU hepsilonBudget hxiBudget _ ih
  have hterminal : u n ≤ rho :=
    Real.filter_trim_iterate_ceil_log_le hc hc1 hrho hrho1 u hdelta0half hstep
  exact ⟨Nat.succ_pos _, (hall n).of_le hterminal,
    finrank_fullIntervalFilterTrimIterate_le K xi S _,
    isIntervalSpanWithRankBound_fullIntervalFilterTrimIterate_succ hxi K S le_rfl _⟩

/-- A positive finite number of actual raw-filter-and-trim steps reaches
the requested error for the original full ground space. The one common
reference and threshold precede the initial candidate. The terminal space
is a literal iterate of that candidate, with unchanged dimension budget.
Supporting ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1809–1817. -/
theorem exists_physical_dg_filterTrimIterate_isCloseTo
    {L q : ℕ} (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (mu nu gamma : ℝ) (hgamma : 0 < gamma) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let M := ‖H‖
    let K := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - M⁻¹ • H)
    let c := gamma / (M - mu)
    ∀ (D : ℕ), 1 ≤ D →
    ∀ (U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (epsilon rho xi delta0 : ℝ),
    0 ≤ epsilon → 0 < rho → rho ≤ 1 → 0 < xi → 0 ≤ delta0 → delta0 ≤ 1 / 2 →
    Submodule.IsCloseTo epsilon G U → Submodule.IsCloseTo epsilon U G →
    (∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x)) →
    epsilon ≤ c ^ 2 * rho / 1024 →
    xi * Real.sqrt (((L - 1 : ℕ) : ℝ) * (D ^ 2 : ℕ)) ≤ c * rho / 48 →
    ∀ (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))),
    Submodule.IsCloseTo delta0 (nativeFullIntervalSpace L q S) G →
    ∃ n : ℕ, 0 < n ∧
      Submodule.IsCloseTo rho
        (nativeFullIntervalSpace L q (fullIntervalFilterTrimIterate L q K xi S n)) G ∧
      Module.finrank ℂ (fullIntervalFilterTrimIterate L q K xi S n) ≤ Module.finrank ℂ S ∧
      IsIntervalSpanWithRankBound L q 0 L (Module.finrank ℂ S) xi
        (fullIntervalFilterTrimIterate L q K xi S n) := by
  intro H hH hmu hnu hmunu hgap G M K c D hD U epsilon rho xi delta0
    hepsilon hrho hrho1 hxi hdelta0 hdelta0half hGU hUG hU hepsilonBudget hxiBudget S hS
  refine ⟨⌈4 / c * Real.log (1 / rho)⌉₊ + 1, ?_⟩
  exact physical_dg_filterTrimIterate_ceil_log_isCloseTo Φ h0 mu nu gamma hgamma
    hmu hnu hmunu hgap D hD U epsilon rho xi delta0 hepsilon hrho hrho1 hxi
    hdelta0 hdelta0half hGU hUG hU hepsilonBudget hxiBudget S hS

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The actual physical reference and threshold can be chosen before any
initial candidate. A candidate already close to the original full ground
space is refined by literal raw-filter-and-trim iterates, and the actual
Ritz extraction from that same terminal space has the prescribed accuracy.
The initial-candidate premise belongs to this auxiliary, not to the final
physical tree construction. Supporting ALVV, arXiv:1602.08828v2,
`eq:algo-xi-dg`, lines 1800–1805, and `t:alg1`, lines 1809–1817. -/
theorem exists_physical_dg_automatic_same_candidate_refinement :
    ∃ Kref : ℝ, 0 < Kref ∧ ∀ (L q : ℕ),
    ∀ (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ),
    0 < gamma →
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let rG := Module.finrank ℂ G
    let g := min gamma 1
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let A := ‖H‖ - mu
    let c := gamma / A
    let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
    ∀ (Dtree Dfilter : ℕ), 1 ≤ Dtree → 1 ≤ Dfilter →
    ∀ eta : ℝ, 0 < eta →
    let rho := eta * gamma / (2 * A + eta * gamma)
    let n := Nat.ceil (4 / c * Real.log (1 / rho)) + 1
    let epsilonRef := c ^ 2 * rho / 32768
    let bref := 16 + Real.log (1 / g) +
      Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonRef)
    ∃ B : ℕ, 1 ≤ B ∧
    Real.log (B : ℝ) ≤
      Kref * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
        (1 + Real.log bref) ∧
    let b := rG ^ 2 * B
    let Dcommon := max Dtree b
    let N := Nat.ceil (100 * (Dfilter : ℝ) ^ 12 / (c * rho))
    let xi := 1 / (1000 * ((Dcommon * N : ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))
    ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
      Module.finrank ℂ U = rG ∧
      Submodule.IsCloseTo epsilonRef U G ∧ Submodule.IsCloseTo epsilonRef G U ∧
      (∀ v ∈ U, IsOpenMPS L q b (fun x ↦ v x)) ∧
      0 < xi ∧
      xi ≤ 1 / (1000 * (Dtree : ℝ) * Real.sqrt ((L : ℝ) + 1)) ∧
      Real.sqrt ((L : ℝ) * (rG : ℝ) * (b : ℝ)) * xi <
        eta / (10000 * (Dfilter : ℝ) ^ 12) ∧
      ∀ (count : ℕ) (S0 : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))),
      Module.finrank ℂ S0 ≤ count →
      Submodule.IsCloseTo (3 / 200 : ℝ) (nativeFullIntervalSpace L q S0) G →
      let S := fullIntervalFilterTrimIterate L q Kraw xi S0 n
      let W := nativeFullIntervalSpace L q S
      let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) rG
      0 < n ∧ Submodule.IsCloseTo rho W G ∧ Module.finrank ℂ S ≤ count ∧
        R ≤ W ∧ Module.finrank ℂ R = rG ∧
        Submodule.IsCloseTo (eta / 2) G R ∧ Submodule.IsCloseTo (eta / 2) R G ∧
        ∀ v ∈ R, IsOpenMPS L q
          (1000000 * (Dcommon * N) ^ 2 * (L + 1) * count ^ 2) (fun x ↦ v x) := by
  classical
  obtain ⟨Kref, hKref, hreference⟩ := exists_physical_dg_isOpenMPS_reference_subspace
  refine ⟨Kref, hKref, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u A c Kraw Dtree Dfilter hDtree hDfilter eta heta rho n epsilonRef bref
  have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  obtain ⟨_hM, hA, _hc, hc1, _hfix, _hKGo, _hhigh⟩ :=
    physical_dg_normalized_ground_filter_spec Φ h0 mu nu gamma hgamma hmu hnu hmunu hgap
  change 0 < A at hA
  change gamma / A ≤ 1 at hc1
  have hgammaA : gamma ≤ A := (div_le_one hA).mp hc1
  obtain ⟨hc, _hc1', hrho, hrho1, _hrhoEta, hpEta, hepsilon, hepsilonSmall,
    hepsilonBudget, henergy⟩ := Real.viable_refinement_error_parameters hgamma hgammaA heta
  have hepsilon1 : epsilonRef ≤ 1 := hepsilonSmall.trans (by norm_num)
  obtain ⟨B, hB, hlogB, U, hdimU, hUG, hGU, hUMPS⟩ :=
    hreference L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      epsilonRef hepsilon hepsilon1
  refine ⟨B, hB, hlogB, ?_⟩
  intro b Dcommon N xi
  have hrb : rG ≤ b := by
    have hsquare : rG ≤ rG ^ 2 := by
      simpa only [mul_one, pow_two] using Nat.mul_le_mul_left rG hrG
    exact hsquare.trans (by simpa only [mul_one] using Nat.mul_le_mul_left (rG ^ 2) hB)
  have hb : 1 ≤ b := hrG.trans hrb
  obtain ⟨hN, hDN, hxi, hxiTree, hxiBudget, hxiSource⟩ :=
    Real.viable_refinement_radius_parameters (L := L) hrG hrb hDtree hDfilter
      (mul_pos hc hrho) hpEta
  refine ⟨U, hdimU, hUG, hGU, hUMPS, hxi, hxiTree, hxiSource, ?_⟩
  intro count S0 hdimS0 hcloseS0
  have hxiBudget' : xi * Real.sqrt (((L - 1 : ℕ) : ℝ) * (b ^ 2 : ℕ)) ≤ c * rho / 48 := by
    simpa only [Nat.cast_pow] using hxiBudget
  obtain ⟨hn, hcloseW, hdimS, _hrecorded⟩ :=
    physical_dg_filterTrimIterate_ceil_log_isCloseTo Φ h0 mu nu gamma hgamma
      hmu hnu hmunu hgap b hb U epsilonRef rho xi (3 / 200)
      hepsilon.le hrho hrho1.le hxi (by norm_num) (by norm_num)
      hGU hUG hUMPS hepsilonBudget hxiBudget' S0 hcloseS0
  let S := fullIntervalFilterTrimIterate L q Kraw xi S0 n
  let W := nativeFullIntervalSpace L q S
  let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) rG
  have hspan := isIntervalSpanWithRankBound_fullIntervalFilterTrimIterate_succ
    hxi Kraw S0 hdimS0 (Nat.ceil (4 / c * Real.log (1 / rho)))
  have hWmps : ∀ v ∈ W, IsOpenMPS L q
      (1000000 * (Dcommon * N) ^ 2 * (L + 1) * count ^ 2) (fun x ↦ v x) := by
    intro v hv
    exact isOpenMPS_of_mem_nativeFullIntervalSpace_of_trimming_rank_bound hDN hspan hv
  obtain ⟨hRle, hdimR, hGR, hRG⟩ :=
    hH.ritzSubspace_isCloseTo_ground_of_isCloseTo W hgamma hmu hgap hrho.le hrho1 hcloseW
  have herror : (‖H‖ - mu) * rho / (1 - rho) / gamma = eta / 2 := by
    rw [henergy]
    field_simp
  rw [herror] at hGR hRG
  exact ⟨hn, hcloseW, hdimS.trans hdimS0, hRle, hdimR, hGR, hRG,
    fun v hv ↦ hWmps v (hRle hv)⟩

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Any actual original-ground viable root has a polynomial-size literal
refinement and actual Ritz extraction. All refinement choices precede the
count and candidate; the gap implication includes flat spectra. Auxiliary
to ALVV, arXiv:1602.08828v2, final refinement, lines 1809–1817. -/
theorem exists_physical_same_root_polynomial_refinement
    (q Dfilter : ℕ) (hq : 1 ≤ q) (hDfilter : 1 ≤ Dfilter)
    (gamma : ℝ) (hgamma : 0 < gamma) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ (L : ℕ)
      (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu : ℝ),
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let r := Module.finrank ℂ G
    let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
    ∀ eta : ℝ, 0 < eta →
    let Z := ((L : ℝ) + 1) * ((r : ℝ) + 1) * (1 + 1 / eta)
    ∃ (rounds : ℕ) (xi : ℝ) (Bscale : ℕ), 0 < xi ∧ (Bscale : ℝ) ≤ C * Z ^ k ∧
      ∀ (count : ℕ) (S0 : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))),
      Module.finrank ℂ S0 ≤ count →
      Submodule.IsCloseTo (3 / 200) (nativeFullIntervalSpace L q S0) G →
      let S := fullIntervalFilterTrimIterate L q Kraw xi S0 rounds
      let W := nativeFullIntervalSpace L q S
      let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) r
      Module.finrank ℂ S ≤ count ∧ R ≤ W ∧ Module.finrank ℂ R = r ∧
        Submodule.IsCloseTo (eta / 2) G R ∧ Submodule.IsCloseTo (eta / 2) R G ∧
        ∀ v ∈ R, IsOpenMPS L q (Bscale * count ^ 2) (fun x ↦ v x) := by
  classical
  obtain ⟨Kref, hKref, hautomatic⟩ :=
    exists_physical_dg_automatic_same_candidate_refinement
  let g := min gamma 1
  let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right _ _
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hu : 0 ≤ u := by
    dsimp only [u]
    have hginv : 1 ≤ 1 / g := (le_div_iff₀ hg).mpr (by simpa using hg1)
    linarith [Real.log_nonneg hq1, Real.log_nonneg hginv]
  obtain ⟨C0, hC0, k, hpoly⟩ := Real.exists_refinement_output_polynomial_bound
    gamma g u 0 Kref Dfilter hgamma hg hg1 hu (by norm_num) hKref.le hDfilter
  refine ⟨max C0 1, lt_max_of_lt_left hC0, k, ?_⟩
  intro L Φ h0 h1 mu H hH hmu hgap G r Kraw eta heta Z
  have hr : 1 ≤ r := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  by_cases hexcited : ∃ nu ∈ spectrum ℝ H, mu < nu
  · obtain ⟨nu, hnu, hmunu⟩ := hexcited
    let A := ‖H‖ - mu
    let c := gamma / A
    let rho := eta * gamma / (2 * A + eta * gamma)
    let rounds := Nat.ceil (4 / c * Real.log (1 / rho)) + 1
    obtain ⟨_hM, hA, _hc, hc1, _hfix, _hKGo, _hhigh⟩ :=
      physical_dg_normalized_ground_filter_spec Φ h0 mu nu gamma hgamma hmu hnu hmunu hgap
    have hgammaA : gamma ≤ A := (div_le_one hA).mp hc1
    have hmu0 : 0 ≤ mu := spectrum_nonneg_of_nonneg
      (show 0 ≤ H from Finset.sum_nonneg fun i _ ↦ h0 i) hmu
    have hnorm : ‖H‖ ≤ ((L - 1 : ℕ) : ℝ) := by
      simpa [H, ManyBody.Interaction.hamiltonian] using
        norm_sum_le_of_le (Finset.univ : Finset (Fin (L - 1)))
          (fun i _ ↦ (CStarAlgebra.norm_le_one_iff_of_nonneg (Φ.term i) (h0 i)).mpr (h1 i))
    have hAL : A ≤ (L : ℝ) + 1 := by
      have hlen : ((L - 1 : ℕ) : ℝ) ≤ (L : ℝ) + 1 := by
        exact_mod_cast (show L - 1 ≤ L + 1 by omega)
      dsimp only [A]
      linarith only [hnorm, hmu0, hlen]
    obtain ⟨B, hB, hlogB, hprecision⟩ :=
      hautomatic L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
        1 Dfilter (by norm_num) hDfilter eta heta
    let b := r ^ 2 * B
    let common := max 1 b
    let N := Nat.ceil (100 * (Dfilter : ℝ) ^ 12 / (c * rho))
    let xi := 1 / (1000 * ((common * N : ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))
    obtain ⟨_U, _hdimU, _hUG, _hGU, _hUMPS, hxi, _hxiTree, _hxiSource, hterminal⟩ := hprecision
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hDreal : (1 : ℝ) ≤ Dfilter := by exact_mod_cast hDfilter
    have hlogs : 1 ≤ 1 + Real.log (r : ℝ) + Real.log (Dfilter : ℝ) + Real.log 2 := by
      linarith only [Real.log_nonneg hrR, Real.log_nonneg hDreal,
        Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    have hsampleOne : (1 : ℝ) ≤
        4097 * (r : ℝ) * (1 + Real.log (r : ℝ) + Real.log (Dfilter : ℝ) + Real.log 2) :=
      (by linarith only [hrR] : (1 : ℝ) ≤ 4097 * (r : ℝ)).trans
        (le_mul_of_one_le_right (by positivity) hlogs)
    have hbudget := hpoly L r A eta hr hgammaA hAL heta
      1 B (by norm_num) hB (by norm_num) hlogB 1
        (by simpa only [Nat.cast_one] using hsampleOne)
    have hb1 : 1 ≤ b :=
      one_le_mul_of_one_le_of_one_le (Nat.one_le_pow 2 r hr) hB
    have hcommon : common = r ^ 2 * B := max_eq_right hb1
    have htreeCommon : max (r ^ 2 * 1) (r ^ 2 * B) = common := by
      rw [hcommon, Nat.mul_one,
        max_eq_right (le_mul_of_one_le_right (Nat.zero_le (r ^ 2)) hB)]
    change ((1000000 * (max (r ^ 2 * 1) (r ^ 2 * B) * N) ^ 2 * (L + 1) *
      (Dfilter ^ 6 * 1 ^ 3) ^ 2 : ℕ) : ℝ) ≤ C0 * Z ^ k at hbudget
    rw [htreeCommon] at hbudget
    simp only [one_pow, mul_one] at hbudget
    let Bscale := 1000000 * (common * N) ^ 2 * (L + 1)
    have hscale : (Bscale : ℝ) ≤ C0 * Z ^ k := by
      have hDcount : 1 ≤ (Dfilter ^ 6) ^ 2 :=
        Nat.one_le_pow 2 _ (Nat.one_le_pow 6 Dfilter hDfilter)
      have hcost : Bscale ≤ Bscale * (Dfilter ^ 6) ^ 2 :=
        le_mul_of_one_le_right (Nat.zero_le Bscale) hDcount
      exact (show (Bscale : ℝ) ≤ ((Bscale * (Dfilter ^ 6) ^ 2 : ℕ) : ℝ) by
        exact_mod_cast hcost).trans hbudget
    refine ⟨rounds, xi, Bscale, hxi,
      hscale.trans (mul_le_mul_of_nonneg_right (le_max_left C0 1) (by positivity)), ?_⟩
    intro count S0 hcount hclose S W R
    obtain ⟨_hn, _hcloseW, hdimS, hRW, hdimR, hGR, hRG, hMPS⟩ :=
      hterminal count S0 hcount hclose
    exact ⟨hdimS, hRW, hdimR, hGR, hRG, hMPS⟩
  · have hL1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by
      linarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
    have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by
      linarith only [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    have heta1 : (1 : ℝ) ≤ 1 + 1 / eta := le_add_of_nonneg_right (by positivity)
    have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hL1 hr1) heta1
    refine ⟨0, 1, 1, by norm_num, ?_, ?_⟩
    · simpa only [Nat.cast_one] using
        (one_le_mul_of_one_le_of_one_le (le_max_right C0 1)
          (one_le_pow₀ hZ : (1 : ℝ) ≤ Z ^ k))
    · intro count S0 hcount hclose S W R
      obtain ⟨_hGtop, _hS0top, _hSsame, _hWG, hRW, hdimR, hGR, hRG, _hrcount, hMPS⟩ :=
        flat_ground_same_root_ritz_exact hH mu gamma (3 / 200) hgamma hmu hgap
          hexcited S0 hcount hclose (by norm_num) 1
      have hdimS : Module.finrank ℂ S ≤ count := by
        change Module.finrank ℂ S0 ≤ count
        exact hcount
      refine ⟨hdimS, hRW.le, hdimR,
        hGR.of_le (by positivity), hRG.of_le (by positivity), ?_⟩
      intro v hv
      simpa only [one_mul] using (hMPS v hv).2.mono
        (by simpa only [pow_two] using Nat.le_mul_self count)

end TNLean.MPS.AreaLaw

end

end PhysicalDGFilterTrimming
