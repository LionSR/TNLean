/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.FullIntervalMPS
import QICLean.ManyBody.Entropy.Cut.RegionalViability
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.IntervalGenerators
import QICLean.Analysis.Parameter.ViableRefinementParameters

/-!
# Viability on the whole chain

Reading coefficients on the full interval is a linear isometry onto the
native chain Hilbert space. Since the full interval has empty exterior,
viability of an interval subspace is exactly closeness of its native image
to the original target. The target remains the full global subspace.
These are the whole-region coordinates of ALVV, arXiv:1602.08828v2,
Definition `d:vs`, lines 433–440, and `t:alg1`, lines 1777–1817.

## Native matrix product vectors from weighted trimming bounds

The weighted rank bound of each actual recorded vector is converted at the
chosen common threshold. The existing finite-span result supplies the
additional generator-count factor for every vector in the same native space.

This supports ALVV, arXiv:1602.08828v2, collective trimming, lines 660–697,
and final refinement, lines 1809–1817. The finite-span argument is LVV,
arXiv:1307.5143v1, Claim `c:2`, lines 520–527.
-/

section

open ManyBody (interval mem_interval)

namespace TNLean.MPS.AreaLaw

private def fullIntervalConfigurationEquiv (L q : ℕ) :
    (interval L 0 L → Fin q) ≃ (Fin L → Fin q) where
  toFun a v := a ⟨v, mem_interval.mpr ⟨Nat.zero_le _, v.isLt⟩⟩
  invFun a v := a v.val
  left_inv a := by
    funext v
    apply congrArg a
    exact Subtype.ext rfl
  right_inv _ := rfl

/-- Reading the full interval in native chain coordinates preserves its
Hilbert-space norm. Supporting ALVV, arXiv:1602.08828v2, the full-chain
root of `t:alg1`, lines 1777–1817. -/
noncomputable def fullIntervalEquiv (L q : ℕ) :
    EuclideanSpace ℂ (interval L 0 L → Fin q) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin L → Fin q) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (fullIntervalConfigurationEquiv L q)

/-- The isometry reads exactly the coefficients of the full-interval
vector. Supporting ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817. -/
@[simp]
theorem fullIntervalEquiv_apply (L q : ℕ)
    (u : EuclideanSpace ℂ (interval L 0 L → Fin q)) :
    WithLp.ofLp (fullIntervalEquiv L q u) = fullIntervalRead L q u := rfl

/-- The native chain subspace obtained from a subspace on the full interval.
Supporting ALVV, arXiv:1602.08828v2, the full-chain root of `t:alg1`,
lines 1777–1817. -/
noncomputable def nativeFullIntervalSpace (L q : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) :
    Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)) :=
  S.map (fullIntervalEquiv L q).toLinearEquiv.toLinearMap

private theorem fullInterval_slice_regionConfigurationSplit {L q : ℕ}
    (ψ : EuclideanSpace ℂ (Fin L → Fin q))
    (b : {v // v ∉ interval L 0 L} → Fin q) :
    (WithLp.toLp 2 fun a ↦
      Entropy.regionConfigurationSplit q (interval L 0 L) ψ (a, b)) =
      (fullIntervalEquiv L q).symm ψ := by
  ext a
  change ψ ((ManyBody.cutEquiv (fun _ : Fin L ↦ Fin q)
      (interval L 0 L)).symm (a, b)) =
    ψ (fullIntervalConfigurationEquiv L q a)
  apply congrArg ψ
  funext v
  rw [ManyBody.cutEquiv_symm_apply_mem _ _
    (mem_interval.mpr ⟨Nat.zero_le _, v.isLt⟩)]
  rfl

/-- The full-interval coefficient isometry identifies the actual native
subspace with its interval/exterior extension in the original configuration
coordinates. The full interval has empty exterior. Supporting ALVV,
arXiv:1602.08828v2,
Definition `d:vs`, lines 433–440, and the final step of Figure `fig:algo1`,
lines 1634–1643. -/
theorem map_nativeFullIntervalSpace_regionConfigurationSplit {L q : ℕ}
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) :
    (nativeFullIntervalSpace L q S).map
      (Entropy.regionConfigurationSplit q (interval L 0 L)).toLinearEquiv.toLinearMap =
      Submodule.prodExt S ({v // v ∉ interval L 0 L} → Fin q) := by
  classical
  ext w
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    apply Submodule.mem_prodExt.mpr
    intro b
    change (WithLp.toLp 2 fun a ↦
      Entropy.regionConfigurationSplit q (interval L 0 L)
        (fullIntervalEquiv L q u) (a, b)) ∈ S
    rw [fullInterval_slice_regionConfigurationSplit,
      LinearIsometryEquiv.symm_apply_apply]
    exact hu
  · intro hw
    let b : {v // v ∉ interval L 0 L} → Fin q := fun v ↦
      False.elim (v.property (mem_interval.mpr ⟨Nat.zero_le _, v.val.isLt⟩))
    let ψ := (Entropy.regionConfigurationSplit q (interval L 0 L)).symm w
    have hlocal : (fullIntervalEquiv L q).symm ψ ∈ S := by
      have hs := Submodule.mem_prodExt.mp hw b
      have hslice := fullInterval_slice_regionConfigurationSplit ψ b
      rw [LinearIsometryEquiv.apply_symm_apply] at hslice
      rwa [← hslice]
    refine ⟨ψ, ?_, LinearIsometryEquiv.apply_symm_apply _ _⟩
    exact ⟨(fullIntervalEquiv L q).symm ψ, hlocal,
      LinearIsometryEquiv.apply_symm_apply _ _⟩

/-- Viability on the whole interval is closeness of the same subspace in
native chain coordinates to the original global target. There is no
exterior factor left to trace out. This is the full-region case of ALVV,
arXiv:1602.08828v2, Definitions `d:vs` and `d:close`, lines 433–474. -/
theorem isViable_fullInterval_iff_isCloseTo {L q : ℕ} {δ : ℝ}
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)))
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) :
    Submodule.IsViable δ S
      (G.map (Entropy.regionTensorCoordinates q
        (interval L 0 L)).toLinearEquiv.toLinearMap) ↔
      Submodule.IsCloseTo δ (nativeFullIntervalSpace L q S) G := by
  rw [← Entropy.isCloseTo_prodExt_region_iff_isViable,
    ← map_nativeFullIntervalSpace_regionConfigurationSplit]
  exact Submodule.isCloseTo_map_iff
    (Entropy.regionConfigurationSplit q (interval L 0 L))

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

namespace TNLean.MPS.AreaLaw

/-- The actual full-interval space with recorded weighted trimming bounds
has one native MPS bond bound for its entire span. The extra count factor
is retained. Supporting ALVV, arXiv:1602.08828v2, collective trimming,
lines 660–697, and LVV, arXiv:1307.5143v1, Claim `c:2`, lines 520–527. -/
theorem isOpenMPS_of_mem_nativeFullIntervalSpace_of_trimming_rank_bound
    {L q D count : ℕ} (hD : 1 ≤ D)
    {S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))}
    (hS : IsIntervalSpanWithRankBound L q 0 L count
      (1 / (1000 * (D : ℝ) * Real.sqrt ((L : ℝ) + 1))) S)
    {v : EuclideanSpace ℂ (Fin L → Fin q)} (hv : v ∈ nativeFullIntervalSpace L q S) :
    IsOpenMPS L q (1000000 * D ^ 2 * (L + 1) * count ^ 2) (fun x ↦ v x) := by
  obtain ⟨n, hn, generators, hspan, hranks⟩ := hS
  obtain ⟨x, hx, rfl⟩ := hv
  have hgenerators : ∀ (i : Fin n) (j : ℕ), j < L - 1 →
      Matrix.schmidtRank (WithLp.ofLp
        (ManyBody.cutVector (intervalTrimCut L 0 L j) (generators i))) ≤
          1000000 * D ^ 2 * (L + 1) * count := by
    intro i j hj
    exact Real.viable_node_trimming_rank_bound hD (hranks j (by simpa using hj) i)
  rw [hspan] at hx
  have hmps := isOpenMPS_fullIntervalRead_of_mem_span generators hgenerators hx
  change IsOpenMPS L q (1000000 * D ^ 2 * (L + 1) * count ^ 2)
    (WithLp.ofLp (fullIntervalEquiv L q x))
  rw [fullIntervalEquiv_apply]
  apply hmps.mono
  calc
    _ ≤ count * (1000000 * D ^ 2 * (L + 1) * count) :=
      Nat.mul_le_mul_right _ hn
    _ = _ := by ring

end TNLean.MPS.AreaLaw

end
