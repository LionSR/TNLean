/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointRightOpenGap
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointPeriodicStateContinuity

/-!
# A uniform periodic gap along the closed mixed interpolation

The actual extended mixed Hamiltonian has a positive norm gap uniform over
the closed parameter interval and every periodic length at least two.
Only positivity of the two endpoint bond dimensions and one-site
injectivity of the two given endpoint tensors are required.

The endpoint open-gap estimates and the injective interior supply strict
finite windows. A smaller strict window bound persists near each parameter.
Knabe's estimate applies to the canonical parent strictly inside the
interval; the independent actual endpoint periodic estimates cover its
ends. Compactness makes the resulting large-volume bound uniform, and
continuity of the actual periodic kernel handles the finitely many shorter
rings. The conclusion concerns the gap of this concrete interpolation.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563, Section 5,
lines 1687–1692; the compact finite-window argument is arXiv:1010.3732,
Appendix A, lines 2575–2578.
-/

open scoped InnerProductSpace Topology

namespace MPSTensor
namespace MPOSymmetry

variable {D₀ D₁ : ℕ}

/-- Every parameter of the closed mixed path admits a strict finite open
window for its actual extended interaction. At an endpoint this is derived
from its eventual open gap; in the interior it follows from injectivity
and the exact canonical open kernel. Source: arXiv:2203.12563, Section 5,
lines 1690–1692. -/
private theorem exists_strict_mixedEndpoint_open_window [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (γ : unitInterval) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ η : ℝ, 1 < (m : ℝ) * η ∧
      ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap (m + 1)))ᗮ,
        η * ‖v‖ ≤ ‖openInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap (m + 1) v‖ := by
  by_cases hend : (γ : ℝ) = 0 ∨ (γ : ℝ) = 1
  · obtain ⟨W, hW, η, hη, hgap⟩ :=
      exists_uniform_mixedEndpoint_open_endpoints_gap A₀ A₁ h₀ h₁
    obtain ⟨n, hn⟩ := exists_lt_nsmul hη (1 : ℝ)
    let m := n + W
    have hm : 2 ≤ m := by dsimp only [m]; omega
    have hnum : 1 < (m : ℝ) * η := by
      have hnm : (n : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast (by dsimp only [m]; omega : n ≤ m)
      calc
        (1 : ℝ) < n • η := hn
        _ = (n : ℝ) * η := by simp only [nsmul_eq_mul]
        _ ≤ (m : ℝ) * η := mul_le_mul_of_nonneg_right hnm hη.le
    exact ⟨m, hm, η, hnum, hgap γ hend (m + 1) (by dsimp only [m]; omega)⟩
  have hzero : (γ : ℝ) ≠ 0 := fun h => hend (Or.inl h)
  have hone : (γ : ℝ) ≠ 1 := fun h => hend (Or.inr h)
  have hγ : (γ : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne γ.property.1 (Ne.symm hzero),
      lt_of_le_of_ne γ.property.2 hone⟩
  let : NeZero (D₀ + D₁) := ⟨by have := NeZero.ne D₀; omega⟩
  have hInj := isInjective_mixedEndpointInterpolation A₀ A₁ h₀ h₁ hγ
  obtain ⟨m, hm, η, hnum, hgap⟩ :=
    exists_strict_openParentHamiltonianES_two_window_of_isInjective _ hInj
  refine ⟨m, hm, η, hnum, ?_⟩
  intro v hv
  rw [mixedEndpoint_openInteractionHamiltonianES_eq_of_mem_Ioo A₀ A₁ hγ] at hv ⊢
  rw [ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
    (Kraus.isNBlkInjective_one_of_isInjective hInj) (by norm_num) (by omega)] at hv
  exact hgap v hv

/-- Near every parameter of the closed path, one positive gap and one
length threshold work for the actual periodic Hamiltonians. The canonical
Knabe estimate is used only in the interior; the independently derived
endpoint periodic gaps cover the endpoints. Source: arXiv:2203.12563,
Section 5, lines 1690–1692; arXiv:1010.3732, Appendix A. -/
private theorem eventually_mixedEndpoint_periodic_long_gap [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (γ₀ : unitInterval) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ᶠ γ : unitInterval in 𝓝 γ₀,
      ∀ N : ℕ, N₀ ≤ N →
        ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N))ᗮ,
          δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
            (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N v‖ := by
  obtain ⟨m, hm, η, hnum, hgap⟩ :=
    exists_strict_mixedEndpoint_open_window A₀ A₁ h₀ h₁ γ₀
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hthreshold : 1 / (m : ℝ) < η :=
    (div_lt_iff₀ hmpos).2 (by simpa only [mul_comm] using hnum)
  obtain ⟨η', hη'lower, hη'upper⟩ := exists_between hthreshold
  have hηpos : 0 < η := (div_pos zero_lt_one hmpos).trans hthreshold
  have hnearReal := eventually_mixedEndpoint_open_gap A₀ A₁ h₀ h₁
    (NeZero.pos D₀) (NeZero.pos D₁) (by omega : 2 ≤ m + 1) hηpos hη'upper hgap
  have hnear := (show ContinuousAt (fun γ : unitInterval => (γ : ℝ)) γ₀
    from continuous_subtype_val.continuousAt).eventually hnearReal
  have hnum' : 1 < (m : ℝ) * η' := by
    simpa only [mul_comm] using (div_lt_iff₀ hmpos).1 hη'lower
  let δK : ℝ := ((m : ℝ) * η' - 1) / ((m : ℝ) - 1)
  have hδK : 0 < δK := by
    apply div_pos (sub_pos.mpr hnum')
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨δE, hδE, hEndpoint⟩ :=
    exists_uniform_mixedEndpoint_periodic_endpoints_gap A₀ A₁ h₀ h₁
  refine ⟨min δK δE, lt_min hδK hδE, 2 * m, ?_⟩
  filter_upwards [hnear] with γ hOpen
  intro N hN v hv
  by_cases hend : (γ : ℝ) = 0 ∨ (γ : ℝ) = 1
  · exact (mul_le_mul_of_nonneg_right (min_le_right δK δE) (norm_nonneg v)).trans
      (hEndpoint γ hend N (by omega) v hv)
  have hzero : (γ : ℝ) ≠ 0 := fun h => hend (Or.inl h)
  have hone : (γ : ℝ) ≠ 1 := fun h => hend (Or.inr h)
  have hγ : (γ : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne γ.property.1 (Ne.symm hzero),
      lt_of_le_of_ne γ.property.2 hone⟩
  have hOpenCanonical :
      ∀ u ∈ (LinearMap.ker (openParentHamiltonianES
        (mixedEndpointInterpolation A₀ A₁ γ) 2 (m + 2 - 1)))ᗮ,
        η' * ‖u‖ ≤ ‖openParentHamiltonianES
          (mixedEndpointInterpolation A₀ A₁ γ) 2 (m + 2 - 1) u‖ := by
    rw [show m + 2 - 1 = m + 1 by omega,
      ← mixedEndpoint_openInteractionHamiltonianES_eq_of_mem_Ioo A₀ A₁ hγ]
    exact hOpen
  have hvCanonical : v ∈ (LinearMap.ker (parentHamiltonianES
      (mixedEndpointInterpolation A₀ A₁ γ) 2 N))ᗮ := by
    rw [← mixedEndpoint_periodicInteractionHamiltonianES_eq_of_mem_Ioo A₀ A₁ hγ]
    exact hv
  have hKnabe := (parentHamiltonianES_gap_of_openParentHamiltonianES_gap
    (mixedEndpointInterpolation A₀ A₁ γ) (R := 2) (m := m) (by norm_num) hm
    (by simpa only [show ((2 : ℝ) - 1) ^ 2 = 1 by norm_num] using hnum')
    hOpenCanonical).2 N hN v hvCanonical
  have hactual : δK * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N v‖ := by
    rw [mixedEndpoint_periodicInteractionHamiltonianES_eq_of_mem_Ioo A₀ A₁ hγ]
    simpa only [δK, Nat.cast_ofNat, show ((2 : ℝ) - 1) ^ 2 = 1 by norm_num,
      show (m : ℝ) - 2 + 1 = (m : ℝ) - 1 by ring] using hKnabe
  exact (mul_le_mul_of_nonneg_right (min_le_left δK δE) (norm_nonneg v)).trans hactual

/-- Compactness gives one gap bound for the actual mixed periodic path at
all sufficiently large lengths, allowing the strict open-window length to
vary with the parameter. Source: arXiv:2203.12563, Section 5,
lines 1690–1692; arXiv:1010.3732, Appendix A. -/
private theorem exists_uniform_mixedEndpoint_periodic_long_gap [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ γ : unitInterval, ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N v‖ := by
  have hcompact : IsCompact (Set.univ : Set unitInterval) := isCompact_univ
  obtain ⟨δ, hδ, N₀, hgap⟩ := hcompact.exists_uniform_pos_nat_bounds
    (fun δ N₀ γ => ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N v‖)
    (by
      intro δ δ' N₀ γ hle hgap N hN v hv
      exact (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap N hN v hv))
    (by
      intro δ N₀ N₁ γ hle hgap N hN
      exact hgap N (hle.trans hN))
    (fun γ _ => eventually_mixedEndpoint_periodic_long_gap A₀ A₁ h₀ h₁ γ)
  exact ⟨δ, hδ, N₀, fun γ => hgap γ (Set.mem_univ γ)⟩

/-- The actual extended mixed interpolation of two one-site injective
endpoint tensors has a positive periodic gap uniform over the whole closed
parameter interval and every ring of length at least two. All strict open
windows, endpoint periodic gaps, and fixed-volume kernel continuity are
derived from the endpoint tensors. Source: arXiv:2203.12563, Section 5,
lines 1687–1692; arXiv:1010.3732, Appendix A, lines 2575–2578. -/
theorem exists_uniform_mixedEndpoint_periodic_path_gap [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval, ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N v‖ := by
  obtain ⟨δ₀, hδ₀, N₀, hlong⟩ :=
    exists_uniform_mixedEndpoint_periodic_long_gap A₀ A₁ h₀ h₁
  obtain ⟨δ, hδ, hgap⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N δ => 2 ≤ N → ∀ γ : unitInterval,
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N v‖)
    (fun N η δ hle h hN γ v hv =>
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (h hN γ v hv))
    (fun N => by
      by_cases hN : 2 ≤ N
      · obtain ⟨η, hη, hfixed⟩ :=
          exists_uniform_mixedEndpoint_periodic_gap_fixed_volume A₀ A₁ h₀ h₁ hN
        exact ⟨η, hη, fun _ => hfixed⟩
      · exact ⟨1, one_pos, fun h => (hN h).elim⟩)
    hδ₀ (fun N hN _ γ => hlong γ N hN)
  exact ⟨δ, hδ, fun γ N hN => hgap N hN γ⟩

end MPOSymmetry
end MPSTensor
