/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FullIntervalMPS
import QICLean.Entropy.RegionalViability

/-!
# Viability on the whole chain

Reading coefficients on the full interval is a linear isometry onto the
native chain Hilbert space. Since the full interval has empty exterior,
viability of an interval subspace is exactly closeness of its native image
to the original target. The target remains the full global subspace.
These are the whole-region coordinates of ALVV, arXiv:1602.08828v2,
Definition `d:vs`, lines 433–440, and `t:alg1`, lines 1777–1817.
-/

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
    (b : ↥((interval L 0 L)ᶜ) → Fin q) :
    (WithLp.toLp 2 fun a ↦
      Entropy.regionConfigurationSplit q (interval L 0 L) ψ (a, b)) =
      (fullIntervalEquiv L q).symm ψ := by
  ext a
  change ψ ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q)
      (interval L 0 L)).symm (a, b)) =
    ψ (fullIntervalConfigurationEquiv L q a)
  apply congrArg ψ
  funext v
  rw [FiniteProduct.splitEquiv_symm_apply_of_mem _ _ _ _ _
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
      Submodule.prodExt S (↥((interval L 0 L)ᶜ) → Fin q) := by
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
    have hempty : (interval L 0 L)ᶜ = ∅ := by
      rw [interval_zero_eq_univ (L := L) le_rfl, Finset.compl_univ]
    let b : ↥((interval L 0 L)ᶜ) → Fin q := fun v ↦
      False.elim (by simpa only [hempty, Finset.notMem_empty] using v.property)
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
