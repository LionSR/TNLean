/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGReferenceSpace
import TNLean.MPS.AreaLaw.ViableSet.CollectiveTrimming

/-!
# Collective trimming through a common reference space

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
  intro L q h hs h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap G r g u
    epsilon hepsilon hepsilon1 b
  obtain ⟨B, hB, hlogB, U, _hdim, hUG, hGU, hU⟩ :=
    hreference L q h hs h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      epsilon hepsilon hepsilon1
  refine ⟨B, hB, hlogB, fun i hi S delta hdelta xi hxi hS ↦ ?_⟩
  simpa only [Nat.cast_mul, Nat.cast_pow] using
    isCloseTo_leftSupportSubmodule_chainTrimSubspace_of_reference hi hepsilon.le hdelta hxi
      hGU hUG hU (stdOrthonormalBasis ℂ S) hS

end TNLean.MPS.AreaLaw
