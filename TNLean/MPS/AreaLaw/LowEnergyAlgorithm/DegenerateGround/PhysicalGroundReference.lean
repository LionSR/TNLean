/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Subspace.ViableSubspace
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.PhysicalDGSharpApproximation
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.MPSReferenceSpace
import TNLean.MPS.AreaLaw.ViableSet.CollectiveTrimming
import QICLean.Analysis.Parameter.RefinementOutputPolynomialBound
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.IntervalCollectiveTrimming
import QICLean.Analysis.Parameter.ViableRefinementParameters

/-!
# An original-ground reference, including flat spectra

The reference used for ALVV collective trimming is constructed from the original
physical ground space. A distinct excited energy is needed only to invoke the
existing area-law approximation. If the Hamiltonian has flat spectrum, its ground
space is the whole space and is its own exact reference.

This is an auxiliary to ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1805.
No reference is taken from a sampled tree or its output.

**Scope restriction (gap dependence):** The quantitative profile uses the clipped
gap `min gamma 1`; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.

It also contains the following results.

* `TNLean.MPS.AreaLaw.exists_physical_dg_common_reference_for_clipped_targets`: one physical
  reference for all nearby clipped targets.
* `TNLean.MPS.AreaLaw.exists_physical_dg_isOpenMPS_reference_subspace`: a physical ground-space
  reference for collective trimming.
* `TNLean.MPS.AreaLaw.isCloseTo_leftSupportSubmodule_chainTrimSubspace_of_reference`,
  `TNLean.MPS.AreaLaw.exists_physical_dg_collective_trimming_bound`: collective trimming through a
  common reference space.
* `TNLean.MPS.AreaLaw.exists_physical_ground_reference_polynomial`: a polynomial reference profile
  for the original ground space.
* `TNLean.MPS.AreaLaw.exists_physical_ground_reference_trimming_profile`: a common original-ground
  reference and trimming radius.
-/

open ManyBody (interval)

section PhysicalDGReferenceSpace

/-!
## A physical ground-space reference for collective trimming

Apply the global matrix product approximation to a genuine orthonormal
basis of the full ground space, at accuracy `epsilon / (2*r)`.
Their fixed span has dimension `r`, is mutually `epsilon`-close to the
original ground space, and every vector in the span has an exact bond
bound `r^2*B`. This supplies the reference-space step in ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1805.
The viable-space merge construction is a separate result. The sharp
coefficient-one entropy theorem concerns the original ground space.

**Scope restriction (gap dependence):** The quantitative bound uses
`min gamma 1`; comparison with the printed inverse-gap rate is established
for `0 < gamma ≤ 1`. See
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- A fixed nearby reference subspace for the full physical ground space has
one exact matrix product bond bound for every vector. The original ground
basis and its approximants are constructed internally. The per-basis global
accuracy is `epsilon/(2*r)`, giving a total squared error at most `epsilon/4`.
This supports the use of the area law in collective trimming in ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1805; no merge-tree
construction or entropy bound for the whole reference space is asserted. -/
theorem exists_physical_dg_isOpenMPS_reference_subspace :
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
      let r := Module.finrank ℂ G
      let g := min gamma 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
      let b := 16 + Real.log (1 / g) +
        Real.log (32 * (r : ℝ) * ((L : ℝ) + 1) / epsilon)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ U = r ∧
        Submodule.IsCloseTo epsilon U G ∧ Submodule.IsCloseTo epsilon G U ∧
        ∀ v ∈ U, IsOpenMPS L q (r ^ 2 * B) (fun x ↦ v x) := by
  classical
  obtain ⟨K, hK, hglobal⟩ := exists_physical_dg_normalized_isOpenMPS_approximation
  refine ⟨K, hK, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap G r g u
    epsilon hepsilon hepsilon1 b
  have hG : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hr : 1 ≤ r := Submodule.one_le_finrank_iff.mpr hG
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith only [hrR]
  let deltaBasis := epsilon / (2 * (r : ℝ))
  have hdelta : 0 < deltaBasis := by dsimp only [deltaBasis]; positivity
  have hdelta1 : deltaBasis ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (r : ℝ))).2
    linarith only [hepsilon1, hrR]
  obtain ⟨B, hB, hlogB, hvectors⟩ :=
    hglobal L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      deltaBasis hdelta hdelta1
  have hratio : 16 * ((L : ℝ) + 1) / deltaBasis =
      32 * (r : ℝ) * ((L : ℝ) + 1) / epsilon := by
    dsimp only [deltaBasis]
    field_simp [ne_of_gt hepsilon, ne_of_gt hr0]; ring
  rw [hratio] at hlogB
  let basis : OrthonormalBasis (Fin r) ℂ G := stdOrthonormalBasis ℂ G
  have hunit (i : Fin r) : ‖(basis i : EuclideanSpace ℂ (Fin L → Fin q))‖ = 1 := by
    rw [Submodule.norm_coe]
    exact basis.norm_eq_one i
  choose phi _hphiUnit hphiMPS _hphiOverlap hphiError using
    fun i : Fin r ↦ hvectors (basis i) (basis i).property (hunit i)
  have hsum : ∑ i : Fin r,
      ‖phi i - (basis i : EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2 ≤ epsilon / 4 := by
    calc
      _ ≤ ∑ _i : Fin r, deltaBasis / 2 := Finset.sum_le_sum fun i _ ↦ hphiError i
      _ = (r : ℝ) * (deltaBasis / 2) := by simp only [Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = epsilon / 4 := by
        dsimp only [deltaBasis]
        field_simp [ne_of_gt hr0]; ring
  obtain ⟨U, hdim, hUG, hGU, hUMPS⟩ :=
    exists_reference_subspace_of_isOpenMPS_basis_approximations G basis phi epsilon
      hepsilon.le hepsilon1 hsum hphiMPS
  refine ⟨B, hB, hlogB, U, hdim, hUG, hGU, ?_⟩
  intro v hv
  simpa only [r, pow_two, mul_assoc] using hUMPS v hv

end TNLean.MPS.AreaLaw

end PhysicalDGReferenceSpace

section PhysicalGroundReference

open ManyBody (cutMatrix)

open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- A reference for the original full ground space with the usual logarithmic
matrix product bond bound. The flat-spectrum case is included, without requiring
an excited energy as an additional hypothesis. Supporting ALVV,
arXiv:1602.08828v2, `t:alg1`, lines 1801–1805. -/
theorem exists_physical_ground_isOpenMPS_reference_subspace :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q : ℕ), 1 ≤ q →
      ∀ (Φ : ManyBody.BondInteraction L q)
        (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let r := Module.finrank ℂ G
      let g := min gamma 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
      let b := 16 + Real.log (1 / g) +
        Real.log (32 * (r : ℝ) * ((L : ℝ) + 1) / epsilon)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ U = r ∧
        Submodule.IsCloseTo epsilon U G ∧ Submodule.IsCloseTo epsilon G U ∧
        ∀ v ∈ U, IsOpenMPS L q (r ^ 2 * B) (fun x ↦ v x) := by
  classical
  obtain ⟨K, hK, href⟩ := exists_physical_dg_isOpenMPS_reference_subspace
  refine ⟨K, hK, ?_⟩
  intro L q hq Φ h0 h1 mu gamma hgamma H hH hmu hgap G r g u
    epsilon hepsilon hepsilon1 b
  by_cases hnonflat : ∃ nu ∈ spectrum ℝ H, mu < nu
  · obtain ⟨nu, hnu, hmunu⟩ := hnonflat
    exact href L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      epsilon hepsilon hepsilon1
  · have heig (i) : hH.eigenvalues i = mu := by
      rcases hgap _ (hH.eigenvalues_mem_spectrum_real i) with hi | hi
      · exact hi
      · exact False.elim (hnonflat ⟨_, hH.eigenvalues_mem_spectrum_real i,
          by linarith only [hi, hgamma]⟩)
    have hGtop : G = ⊤ := by
      apply top_unique
      intro v _
      apply (Submodule.mem_spectralSpanLE_iff _ _ _ _).mpr
      intro i hi
      simp only [heig i, lt_self_iff_false] at hi
    have hr : 1 ≤ r := Submodule.one_le_finrank_iff.mpr
      (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hg : 0 < g := lt_min hgamma (by norm_num)
    have hlogg : 0 ≤ Real.log (1 / g) :=
      Real.log_nonneg ((one_le_div hg).2 (min_le_right gamma 1))
    have hu : 0 ≤ u := by
      have hlogq := Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq)
      dsimp only [u]
      linarith only [hlogq, hlogg]
    have hb : 1 ≤ b := by
      have hratio : 1 ≤ 32 * (r : ℝ) * ((L : ℝ) + 1) / epsilon := by
        apply (one_le_div hepsilon).2
        nlinarith only [hrR, (Nat.cast_nonneg L : (0 : ℝ) ≤ L), hepsilon1]
      have hlog := Real.log_nonneg hratio
      dsimp only [b]
      linarith only [hlogg, hlog]
    have hcost : 0 ≤ K *
        (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) := by
      have hlogb := Real.log_nonneg hb
      positivity
    refine ⟨1, le_rfl, ?_, G, rfl,
      Submodule.isCloseTo_of_le hepsilon.le le_rfl,
      Submodule.isCloseTo_of_le hepsilon.le le_rfl, ?_⟩
    · simpa only [Nat.cast_one, Real.log_one] using hcost
    · intro v _
      apply (isOpenMPS_iff_internal_cutMatrix_rank_le v).mpr
      intro k _ _
      calc
        (cutMatrix (interval L 0 k) v).rank ≤
            Fintype.card ((w : {w : Fin L // w ∈ interval L 0 k}) → Fin q) :=
          Matrix.rank_le_card_height _
        _ = q ^ Fintype.card {w : Fin L // w ∈ interval L 0 k} := by simp
        _ ≤ q ^ L := Nat.pow_le_pow_right hq (by
          simpa using Fintype.card_subtype_le (fun w : Fin L ↦ w ∈ interval L 0 k))
        _ = r := by
          change q ^ L = Module.finrank ℂ G
          rw [hGtop]
          simp
        _ ≤ r ^ 2 * 1 := by nlinarith only [hr]

end TNLean.MPS.AreaLaw

end PhysicalGroundReference

section PhysicalDGClippedReference

/-!
## One physical reference for all nearby clipped targets

An original-ground-space reference is chosen at the same small accuracy
as the original-to-clipped comparison. It then controls every nearby
clipped target, in both directions, before the interval is chosen. The
clipping error and reference error are separate inputs to the triangle
estimate; neither is replaced by a fixed constant.

This supports ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`,
lines 1668–1670, and the reference argument, lines 1801–1805.
The actual clipped targets must still be constructed with the stated
accuracy by the physical truncation estimate.

**Scope restriction (reference gap dependence):** The reference rank bound
uses `min gamma 1`; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.
No physical cutoff calibration or adaptive probability is asserted here.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- One actual physical MPS reference controls every target mutually close
to the original full ground space at the prescribed small accuracy. It is
chosen before all such targets and retains one all-span MPS bound. The
original-to-clipped accuracy must be separately derived in the physical
application. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:merge-prime`, lines 1668–1670, and lines 1801–1805. -/
theorem exists_physical_dg_common_reference_for_clipped_targets :
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
      let r := Module.finrank ℂ G
      let g := min gamma 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ a : ℝ, 0 < a → a ≤ 1 →
      let tau := a ^ 2 / 1048576
      let b := 16 + Real.log (1 / g) +
        Real.log (32 * (r : ℝ) * ((L : ℝ) + 1) / tau)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ U = r ∧
        Submodule.IsCloseTo tau U G ∧ Submodule.IsCloseTo tau G U ∧
        (∀ v ∈ U, IsOpenMPS L q (r ^ 2 * B) (fun x ↦ v x)) ∧
        4 * tau ≤ a ^ 2 / 16384 ∧
        ∀ T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
          Submodule.IsCloseTo tau G T → Submodule.IsCloseTo tau T G →
          Submodule.IsCloseTo (4 * tau) T U ∧ Submodule.IsCloseTo (4 * tau) U T := by
  classical
  obtain ⟨K, hK, hreference⟩ := exists_physical_dg_isOpenMPS_reference_subspace
  refine ⟨K, hK, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G r g u a ha ha1 tau b
  have htau : 0 < tau := by dsimp only [tau]; positivity
  have htau1 : tau ≤ 1 := by
    have haSq : a ^ 2 ≤ 1 := by nlinarith
    dsimp only [tau]
    linarith
  obtain ⟨B, hB, hlogB, U, hdimU, hUG, hGU, hUMPS⟩ :=
    hreference L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap tau htau htau1
  refine ⟨B, hB, hlogB, U, hdimU, hUG, hGU, hUMPS, ?_, ?_⟩
  · dsimp only [tau]
    nlinarith [sq_nonneg a]
  · intro T hGT hTG
    constructor
    · exact (hTG.trans hGU htau.le).of_le (by linarith)
    · exact (hUG.trans hGT htau.le).of_le (by linarith)

end TNLean.MPS.AreaLaw

end PhysicalDGClippedReference

section PhysicalDGReferenceTrimming

/-!
## Collective trimming through a common reference space

A viable block space is transferred to a nearby reference space, trimmed
collectively by the actual spectral projections, and transferred back to
the original target. This makes the use of the area law in ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1805, explicit.
The reference space is constructed from the physical Hamiltonian before
the block and viable space are chosen. No sampled merge-tree induction
is asserted.

**Local fix (trimming constant):** The bound uses the proved collective
trimming loss `2*xi*sqrt(m*b)` rather than the printed constant in
Lemma `lem:trimming`. See the companion paper-gap note
<https://sirui-lu.com/QICLean/paper-gaps/alvv16_trimming_constant.pdf>.

**Scope restriction (gap dependence):** The physical reference bound uses
`min gamma 1`; comparison with the printed inverse-gap rate is established
for `0 < gamma ≤ 1`. See
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- Transfer a viable space to one nearby matrix product reference, apply
collective trimming to its actual orthonormal basis, and transfer back.
The resulting loss is `4*delta + 6*epsilon + 4*xi*sqrt((i-1)*D)`.
This is the reference-space use of collective trimming in ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1805, with the corrected
constant of Lemma `lem:trimming`, lines 660–697. -/
theorem isCloseTo_leftSupportSubmodule_chainTrimSubspace_of_reference
    {L q i s D : ℕ} (hi : i ≤ L)
    {G U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))}
    {epsilon delta xi : ℝ} (hepsilon : 0 ≤ epsilon) (hdelta : 0 ≤ delta) (hxi : 0 < xi)
    (hGU : Submodule.IsCloseTo epsilon G U)
    (hUG : Submodule.IsCloseTo epsilon U G)
    (hU : ∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x))
    {S : Submodule ℂ (LeftBlockVector L q i)} (u : OrthonormalBasis (Fin s) ℂ S)
    (hS : Submodule.IsCloseTo delta
      (leftSupportSubmodule (S : Set (LeftBlockVector L q i))) G) :
    Submodule.IsCloseTo
      (4 * delta + 6 * epsilon + 4 * xi * Real.sqrt (((i - 1 : ℕ) : ℝ) * D))
      (leftSupportSubmodule
        (chainTrimSubspace xi (fun k ↦ (u k : LeftBlockVector L q i)) :
          Set (LeftBlockVector L q i))) G := by
  have hSU := hS.trans hGU hdelta
  have htrim := isCloseTo_leftSupportSubmodule_chainTrimSubspace hxi u hSU
    (fun v hv j hj0 hji ↦ (hU v hv).rank_cutMatrix_le hj0 (lt_of_lt_of_le hji hi))
  convert htrim.trans hUG (by positivity) using 1
  ring

/-- Actual collective trimming of any viable block space preserves viability
for the original physical ground space, with the explicit loss obtained
by transfer through one common matrix product reference. The integer bound
is chosen before the block and viable space. The chosen orthonormal
basis and all trimming projections are constructed internally.
This establishes the reference-space trimming step of ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1805; it does not
construct the sampled viable spaces of the merge tree. -/
theorem exists_physical_dg_collective_trimming_bound :
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
      let r := Module.finrank ℂ G
      let g := min gamma 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
      let b := 16 + Real.log (1 / g) +
        Real.log (32 * (r : ℝ) * ((L : ℝ) + 1) / epsilon)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∀ (i : ℕ), i ≤ L → ∀ (S : Submodule ℂ (LeftBlockVector L q i)),
      ∀ delta : ℝ, 0 ≤ delta → ∀ xi : ℝ, 0 < xi →
      Submodule.IsCloseTo delta
        (leftSupportSubmodule (S : Set (LeftBlockVector L q i))) G →
      let basis := stdOrthonormalBasis ℂ S
      Submodule.IsCloseTo
        (4 * delta + 6 * epsilon +
          4 * xi * Real.sqrt (((i - 1 : ℕ) : ℝ) * (r ^ 2 * B)))
        (leftSupportSubmodule
          (chainTrimSubspace xi (fun k ↦ (basis k : LeftBlockVector L q i)) :
            Set (LeftBlockVector L q i))) G := by
  obtain ⟨K, hK, hreference⟩ := exists_physical_dg_isOpenMPS_reference_subspace
  refine ⟨K, hK, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap G r g u
    epsilon hepsilon hepsilon1 b
  obtain ⟨B, hB, hlogB, U, _hdim, hUG, hGU, hU⟩ :=
    hreference L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      epsilon hepsilon hepsilon1
  refine ⟨B, hB, hlogB, fun i hi S delta hdelta xi hxi hS ↦ ?_⟩
  simpa only [Nat.cast_mul, Nat.cast_pow] using
    isCloseTo_leftSupportSubmodule_chainTrimSubspace_of_reference hi hepsilon.le hdelta hxi
      hGU hUG hU (stdOrthonormalBasis ℂ S) hS

end TNLean.MPS.AreaLaw

end PhysicalDGReferenceTrimming

section PhysicalGroundReferencePolynomial

/-!
## A polynomial reference profile for the original ground space

For fixed local dimension and positive gap, the whole-exterior reference rank is
polynomial in chain length and ground multiplicity. All coefficients and exponents
are chosen before the Hamiltonian. The reference comes from the original area-law
approximation, including the exact flat-spectrum case, not from a sampled output.

This is an auxiliary to ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1801–1805.
The exponent is not asserted to have the source's sharp inverse-gap dependence.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- At fixed local dimension and gap, the squared whole-chain reference bond has
one polynomial bound in length and ground multiplicity. The reference has error
`1/100000` in both directions. Supporting ALVV, arXiv:1602.08828v2,
`t:alg1`, lines 1801–1805; this is an existence bound, not a running-time claim. -/
theorem exists_physical_ground_reference_polynomial
    (q : ℕ) (hq : 1 ≤ q) (gamma : ℝ) (hgamma : 0 < gamma) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ,
      ∀ (L : ℕ)
      (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let r := Module.finrank ℂ G
      ∃ B : ℕ, 1 ≤ B ∧
        (((r ^ 2 * B) ^ 2 : ℕ) : ℝ) ≤
          C * (((L : ℝ) + 1) * ((r : ℝ) + 1)) ^ P ∧
      ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ U = r ∧
        Submodule.IsCloseTo (1 / 100000) U G ∧
        Submodule.IsCloseTo (1 / 100000) G U ∧
        ∀ v ∈ U, IsOpenMPS L q (r ^ 2 * B) (fun x ↦ v x) := by
  classical
  obtain ⟨K, hK, href⟩ := exists_physical_ground_isOpenMPS_reference_subspace
  let g := min gamma 1
  let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
  let a0 := u ^ 3 / g
  let a1 := (1 / g) ^ (1 / 4 : ℝ) * u
  let b0 := 16 + Real.log (1 / g) + Real.log (3200000 : ℝ)
  let C0 := Real.exp (K * (a0 + 5 * a1) * b0)
  let p0 := Nat.ceil (K * (a0 + 5 * a1))
  refine ⟨1 + C0 ^ 2, by positivity, 4 + 2 * p0, ?_⟩
  intro L Φ h0 h1 mu H hH hmu hgap G r
  obtain ⟨B, hB, hlogB, U, hdim, hUG, hGU, hUMPS⟩ :=
    href L q hq Φ h0 h1 mu gamma hgamma hmu hgap
      (1 / 100000) (by norm_num) (by norm_num)
  have hr : 1 ≤ r := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  let Z := ((L : ℝ) + 1) * ((r : ℝ) + 1)
  let b := 16 + Real.log (1 / g) +
    Real.log (32 * (r : ℝ) * ((L : ℝ) + 1) / (1 / 100000))
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hlogg : 0 ≤ Real.log (1 / g) :=
    Real.log_nonneg ((one_le_div hg).2 (min_le_right gamma 1))
  have hu : 0 ≤ u := by
    have hlogq := Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq)
    dsimp only [u]
    linarith only [hlogq, hlogg]
  have ha0 : 0 ≤ a0 := by dsimp only [a0]; positivity
  have ha1 : 0 ≤ a1 := by dsimp only [a1]; positivity
  have hb0 : 1 ≤ b0 := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 3200000 by norm_num)
    dsimp only [b0]
    linarith only [hlogg, hlog]
  have hZ : 1 ≤ Z := by
    dsimp only [Z]
    nlinarith only [hrR, (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hb : 1 ≤ b := by
    have hlog := Real.log_nonneg (show
        1 ≤ 32 * (r : ℝ) * ((L : ℝ) + 1) / (1 / 100000) by
      nlinarith only [hrR, (Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
    dsimp only [b]
    linarith only [hlogg, hlog]
  have hratio : 32 * (r : ℝ) * ((L : ℝ) + 1) / (1 / 100000) ≤
      3200000 * Z := by
    dsimp only [Z]
    nlinarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hbx : b ≤ b0 + Real.log Z := by
    have hlog := Real.log_le_log (by positivity :
      0 < 32 * (r : ℝ) * ((L : ℝ) + 1) / (1 / 100000)) hratio
    rw [Real.log_mul (by norm_num : (3200000 : ℝ) ≠ 0)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hZ))] at hlog
    dsimp only [b, b0]
    linarith only [hlog]
  have hBP : (B : ℝ) ≤ C0 * Z ^ p0 := by
    apply Real.reference_profile_polynomial_bound hK.le le_rfl ha0 ha1 hb hb0
      (by exact_mod_cast (by omega : 0 < B)) hZ hbx
    dsimp only [a0, a1]
    convert hlogB using 1
    ring
  refine ⟨B, hB, ?_, U, hdim, hUG, hGU, hUMPS⟩
  have hrZ : (r : ℝ) ≤ Z := by
    dsimp only [Z]
    nlinarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ L),
      (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  calc
    (((r ^ 2 * B) ^ 2 : ℕ) : ℝ) ≤ (Z ^ 2 * (C0 * Z ^ p0)) ^ 2 := by
      push_cast
      gcongr
    _ = C0 ^ 2 * Z ^ (4 + 2 * p0) := by
      simp only [pow_add, pow_mul, mul_pow]
      ring
    _ ≤ (1 + C0 ^ 2) * Z ^ (4 + 2 * p0) := by
      gcongr
      linarith only [sq_nonneg C0]

end TNLean.MPS.AreaLaw

end PhysicalGroundReferencePolynomial

section PhysicalGroundReferenceTrimming

/-!
## A common original-ground reference and trimming radius

One reference space, constructed from the original ground space, controls every
interval with its full exterior. Its squared whole-chain bond is the reference
rank. A single positive radius is fixed before all intervals, candidates, and
samples. The exact weighted loss has no candidate-dimension factor. The latter
appears separately in the coarse polynomial ceiling for the output bond.

This supports ALVV, arXiv:1602.08828v2, collective trimming, lines 660–697,
and `t:alg1`, lines 1801–1813. No sampled output is used to construct the reference.
The asserted polynomial dependence is at fixed local dimension and gap; no
running-time or sharp inverse-gap estimate is asserted. The trimming loss is the
corrected weighted reference loss, recorded in
https://sirui-lu.com/QICLean/paper-gaps/alvv16_trimming_constant.pdf.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- The original ground space supplies one fixed reference and one positive
trimming radius for every interval. The two-boundary reference rank, exact
weighted loss, inverse-square profile, and separate candidate-count cost are
retained. Supporting ALVV, arXiv:1602.08828v2, lines 660–697 and 1801–1813. -/
theorem exists_physical_ground_reference_trimming_profile
    (q : ℕ) (hq : 1 ≤ q) (gamma : ℝ) (hgamma : 0 < gamma) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ,
      ∀ (L : ℕ)
      (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let r := Module.finrank ℂ G
      let Z := ((L : ℝ) + 1) * ((r : ℝ) + 1)
      ∃ B : ℕ, 1 ≤ B ∧
      let d := r ^ 2 * B
      let bRef := d ^ 2
      let xi := 1 / (1000 * (d : ℝ) * Real.sqrt ((L : ℝ) + 1))
      ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ U = r ∧
        Submodule.IsCloseTo (1 / 100000) U G ∧
        Submodule.IsCloseTo (1 / 100000) G U ∧
        (∀ v ∈ U, IsOpenMPS L q d (fun x ↦ v x)) ∧
        (bRef : ℝ) ≤ C * Z ^ P ∧
        0 < xi ∧
        (∀ kCuts : ℕ, kCuts ≤ L →
          xi * Real.sqrt ((kCuts : ℝ) * (bRef : ℝ)) ≤ 1 / 1000) ∧
        (xi⁻¹) ^ 2 ≤ 1000000 * C * Z ^ (P + 1) ∧
        (∀ count : ℕ,
          ((1000000 * bRef * (L + 1) * count ^ 2 : ℕ) : ℝ) ≤
            1000000 * C * Z ^ (P + 1) * (count : ℝ) ^ 2) ∧
        ∀ p s : ℕ,
          let F := Entropy.regionConfigurationSplit q (interval L p s)
          Submodule.IsCloseTo (1 / 100000)
            (U.map F.toLinearEquiv.toLinearMap) (G.map F.toLinearEquiv.toLinearMap) ∧
          Submodule.IsCloseTo (1 / 100000)
            (G.map F.toLinearEquiv.toLinearMap) (U.map F.toLinearEquiv.toLinearMap) ∧
          ∀ t ∈ U.map F.toLinearEquiv.toLinearMap, ∀ j < s - p - 1,
            Matrix.schmidtRank (WithLp.ofLp
              (Entropy.cutEnvVector (n := fun _ : interval L p s ↦ q)
                (intervalTrimCut L p s j) t)) ≤ bRef := by
  classical
  obtain ⟨C, hC, P, href⟩ :=
    exists_physical_ground_reference_polynomial q hq gamma hgamma
  refine ⟨C, hC, P, ?_⟩
  intro L Φ h0 h1 mu H hH hmu hgap G r Z
  obtain ⟨B, hB, hbound, U, hdim, hUG, hGU, hUMPS⟩ :=
    href L Φ h0 h1 mu hmu hgap
  let d := r ^ 2 * B
  let bRef := d ^ 2
  let xi := 1 / (1000 * (d : ℝ) * Real.sqrt ((L : ℝ) + 1))
  have hr : 1 ≤ r := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  have hd : 1 ≤ d := by
    change 0 < d
    dsimp only [d]
    positivity
  have hxi : 0 < xi := (Real.viable_node_trimming_radius_budget
    (L := L) (cuts := 0) (Nat.zero_le L) hd).1
  have hbudget (kCuts : ℕ) (hk : kCuts ≤ L) :
      xi * Real.sqrt ((kCuts : ℝ) * (bRef : ℝ)) ≤ 1 / 1000 := by
    have h := (Real.viable_node_trimming_radius_budget hk hd).2
    change 4 * xi * Real.sqrt ((kCuts : ℝ) * (d : ℝ) ^ 2) ≤ 1 / 250 at h
    dsimp only [bRef]
    push_cast
    linarith only [h]
  have hinv : (xi⁻¹) ^ 2 = 1000000 * (bRef : ℝ) * ((L : ℝ) + 1) := by
    dsimp only [xi, bRef]
    rw [one_div, inv_inv, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    push_cast
    norm_num
  have hLZ : (L : ℝ) + 1 ≤ Z := by
    dsimp only [Z]
    nlinarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ L),
      (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hcost : 1000000 * (bRef : ℝ) * ((L : ℝ) + 1) ≤
      1000000 * C * Z ^ (P + 1) := by
    calc
      _ ≤ 1000000 * (C * Z ^ P) * Z := by gcongr
      _ = _ := by rw [pow_succ]; ring
  refine ⟨B, hB, U, hdim, hUG, hGU, hUMPS, hbound, hxi, hbudget, ?_, ?_, ?_⟩
  · exact hinv.le.trans hcost
  · intro count
    push_cast
    simpa only [bRef, d, Nat.cast_pow, Nat.cast_mul] using
      mul_le_mul_of_nonneg_right hcost (sq_nonneg (count : ℝ))
  · intro p s F
    refine ⟨(Submodule.isCloseTo_map_iff F).mpr hUG,
      (Submodule.isCloseTo_map_iff F).mpr hGU, ?_⟩
    intro t ht j hj
    exact schmidtRank_cutEnvVector_interval_reference_le hd hUMPS p s ht j hj

end TNLean.MPS.AreaLaw

end PhysicalGroundReferenceTrimming
