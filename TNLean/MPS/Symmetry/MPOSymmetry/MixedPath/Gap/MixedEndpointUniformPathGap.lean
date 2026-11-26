/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Gap.MixedEndpointOpenGap
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Gap.MixedEndpointPeriodicStateContinuity

/-!
# A uniform periodic gap along the closed mixed interpolation

The Hamiltonian of the translates of the extended mixed interaction is gapped at zero, with
one positive gap for the closed parameter interval and every ring of at least two sites: its
kernel is nonzero and every nonzero eigenvalue is at least the gap.
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

open scoped InnerProductSpace Topology ComplexOrder

namespace MPSTensor
namespace MPOSymmetry

open ManyBody.Interaction (translationInvariant chainTranslates)

variable {D₀ D₁ : ℕ}

/-- A point of the unit interval other than its two endpoints lies in the
open interval. -/
private theorem mem_Ioo_of_not_endpoint {γ : unitInterval}
    (hend : ¬((γ : ℝ) = 0 ∨ (γ : ℝ) = 1)) : (γ : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hzero : (γ : ℝ) ≠ 0 := fun h => hend (Or.inl h)
  have hone : (γ : ℝ) ≠ 1 := fun h => hend (Or.inr h)
  exact ⟨lt_of_le_of_ne γ.property.1 (Ne.symm hzero),
    lt_of_le_of_ne γ.property.2 hone⟩

/-- Every parameter of the closed mixed path admits a strict finite open
window for its actual extended interaction. At an endpoint this is derived
from its eventual open gap; in the interior it follows from injectivity
and the exact canonical open kernel. Source: arXiv:2203.12563, Section 5,
lines 1690–1692. -/
private theorem exists_strict_mixedEndpoint_open_window [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (γ : unitInterval) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ η : ℝ, 1 < (m : ℝ) * η ∧ ManyBody.IsGapped
      (chainTranslates 2 (m + 1) (mixedEndpointParentInteraction A₀ A₁ γ)).hamiltonian 0 η := by
  have hne (m : ℕ) (hm : 2 ≤ m) :=
    groundSpace_mixedEndpoint_hamiltonian_chainTranslates_ne_bot A₀ A₁ h₀ h₁
      (NeZero.pos D₀) (NeZero.pos D₁) γ (by omega : 2 ≤ m + 1)
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
    exact ⟨m, hm, η, hnum, ManyBody.isGapped_zero_iff.mpr
      ⟨hne m hm, hgap γ hend (m + 1) (by dsimp only [m]; omega)⟩⟩
  have hγ := mem_Ioo_of_not_endpoint hend
  let : NeZero (D₀ + D₁) := ⟨by have := NeZero.ne D₀; omega⟩
  have hInj := isInjective_mixedEndpointInterpolation A₀ A₁ h₀ h₁ hγ
  obtain ⟨m, hm, η, hnum, hgap⟩ :=
    exists_strict_hamiltonian_parentChainInteraction_two_window_of_isInjective _ hInj
  refine ⟨m, hm, η, hnum, ManyBody.isGapped_zero_iff.mpr ⟨hne m hm, ?_⟩⟩
  rw [mixedEndpoint_hamiltonian_chainTranslates_eq_of_mem_Ioo A₀ A₁ hγ]
  exact hgap

/-- Near every parameter of the closed path, one positive lower bound on the nonzero
eigenvalues and one length threshold work for the actual periodic Hamiltonians. The canonical
Knabe estimate is used only in the interior; the independently derived
endpoint periodic gaps cover the endpoints. Source: arXiv:2203.12563,
Section 5, lines 1690–1692; arXiv:1010.3732, Appendix A. -/
private theorem eventually_mixedEndpoint_periodic_long_gap [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (γ₀ : unitInterval) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ᶠ γ : unitInterval in 𝓝 γ₀,
      ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
        ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin (translationInvariant N
          (mixedEndpointParentInteraction A₀ A₁ γ)).hamiltonian) μ → μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨m, hm, η, hnum, hgap⟩ :=
    exists_strict_mixedEndpoint_open_window A₀ A₁ h₀ h₁ γ₀
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hthreshold : 1 / (m : ℝ) < η :=
    (div_lt_iff₀ hmpos).2 (by simpa only [mul_comm] using hnum)
  obtain ⟨η', hη'lower, hη'upper⟩ := exists_between hthreshold
  have hnearReal := eventually_isGapped_mixedEndpoint_hamiltonian_chainTranslates A₀ A₁ h₀ h₁
    (NeZero.pos D₀) (NeZero.pos D₁) (by omega : 2 ≤ m + 1) hη'upper hgap
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
    exists_uniform_isGapped_mixedEndpoint_hamiltonian_translationInvariant_endpoints
      A₀ A₁ h₀ h₁
  refine ⟨min δK δE, lt_min hδK hδE, 2 * m, ?_⟩
  filter_upwards [hnear] with γ hOpen
  intro N _ hN
  by_cases hend : (γ : ℝ) = 0 ∨ (γ : ℝ) = 1
  · exact ManyBody.forall_hasEigenvalue_mono (min_le_right δK δE)
      (ManyBody.isGapped_zero_iff.mp (hEndpoint γ hend N (by omega))).2
  have hγ := mem_Ioo_of_not_endpoint hend
  have hOpenCanonical : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      (parentChainInteraction (mixedEndpointInterpolation A₀ A₁ γ) 2
        (m + 2 - 1)).hamiltonian) μ → μ = 0 ∨ (η' : ℂ) ≤ μ := by
    rw [show m + 2 - 1 = m + 1 by omega,
      ← mixedEndpoint_hamiltonian_chainTranslates_eq_of_mem_Ioo A₀ A₁ hγ]
    exact (ManyBody.isGapped_zero_iff.mp hOpen).2
  have hKnabe :=
    (hamiltonian_parentRingInteraction_gap_of_hamiltonian_parentChainInteraction_gap
      (mixedEndpointInterpolation A₀ A₁ γ) (R := 2) (m := m) (by norm_num) hm
      (by simpa only [Nat.cast_ofNat, show ((2 : ℝ) - 1) ^ 2 = 1 by norm_num] using hnum')
      hOpenCanonical).2 N hN
  rw [mixedEndpoint_hamiltonian_translationInvariant_eq_of_mem_Ioo A₀ A₁ hγ]
  refine ManyBody.forall_hasEigenvalue_mono (min_le_left δK δE) ?_
  simpa only [δK, Nat.cast_ofNat, show ((2 : ℝ) - 1) ^ 2 = 1 by norm_num,
    show (m : ℝ) - 2 + 1 = (m : ℝ) - 1 by ring] using hKnabe

/-- Compactness gives one lower bound on the nonzero eigenvalues for the actual mixed periodic
path at all sufficiently large lengths, allowing the strict open-window length to
vary with the parameter. Source: arXiv:2203.12563, Section 5,
lines 1690–1692; arXiv:1010.3732, Appendix A. -/
private theorem exists_uniform_mixedEndpoint_periodic_long_gap [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ γ : unitInterval, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin (translationInvariant N
        (mixedEndpointParentInteraction A₀ A₁ γ)).hamiltonian) μ → μ = 0 ∨ (δ : ℂ) ≤ μ := by
  have hcompact : IsCompact (Set.univ : Set unitInterval) := isCompact_univ
  obtain ⟨δ, hδ, N₀, hgap⟩ := hcompact.exists_uniform_pos_nat_bounds
    (fun δ N₀ γ => ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin (translationInvariant N
        (mixedEndpointParentInteraction A₀ A₁ γ)).hamiltonian) μ → μ = 0 ∨ (δ : ℂ) ≤ μ)
    (by
      intro δ δ' N₀ γ hle hgap N _ hN
      exact ManyBody.forall_hasEigenvalue_mono hle (hgap N hN))
    (by
      intro δ N₀ N₁ γ hle hgap N _ hN
      exact hgap N (hle.trans hN))
    (fun γ _ => eventually_mixedEndpoint_periodic_long_gap A₀ A₁ h₀ h₁ γ)
  exact ⟨δ, hδ, N₀, fun γ => hgap γ (Set.mem_univ γ)⟩

/-- The Hamiltonian of the translates of the actual extended mixed interaction of two one-site
injective endpoint tensors is gapped at zero with one positive gap over the whole closed
parameter interval and every ring of length at least two. All strict open
windows, endpoint periodic gaps, and fixed-volume kernel continuity are
derived from the endpoint tensors. Source: arXiv:2203.12563, Section 5,
lines 1687–1692; arXiv:1010.3732, Appendix A, lines 2575–2578. -/
theorem exists_uniform_isGapped_mixedEndpoint_hamiltonian_translationInvariant_path
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval, ∀ (N : ℕ) (hN : 2 ≤ N),
      haveI : NeZero N := ⟨by omega⟩;
      ManyBody.IsGapped
        (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ γ)).hamiltonian 0 δ := by
  obtain ⟨δ₀, hδ₀, N₀, hlong⟩ :=
    exists_uniform_mixedEndpoint_periodic_long_gap A₀ A₁ h₀ h₁
  obtain ⟨δ, hδ, hgap⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N δ => ∀ hN : 2 ≤ N, ∀ γ : unitInterval,
      haveI : NeZero N := ⟨by omega⟩;
      ManyBody.IsGapped
        (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ γ)).hamiltonian 0 δ)
    (fun N η δ hle h hN γ => (h hN γ).mono hle)
    (fun N => by
      by_cases hN : 2 ≤ N
      · obtain ⟨η, hη, hfixed⟩ :=
          exists_uniform_isGapped_mixedEndpoint_hamiltonian_translationInvariant_fixed_volume
            A₀ A₁ h₀ h₁ hN
        exact ⟨η, hη, fun _ => hfixed⟩
      · exact ⟨1, one_pos, fun h => (hN h).elim⟩)
    hδ₀ (fun N hN h2 γ =>
      haveI : NeZero N := ⟨by omega⟩
      ManyBody.isGapped_zero_iff.mpr
        ⟨groundSpace_mixedEndpoint_hamiltonian_translationInvariant_ne_bot A₀ A₁ h₀ h₁ γ h2,
          hlong γ N hN⟩)
  exact ⟨δ, hδ, fun γ N hN => hgap N hN γ⟩

end MPOSymmetry
end MPSTensor
