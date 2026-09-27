/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Norm gaps on the orthogonal complement of a kernel

A linear map \(f\) on a finite-dimensional inner product space is injective on
\((\ker f)^\perp\), hence bounded below there: there is \(\delta>0\) with
\(\delta\|v\|\le\|fv\|\) for every \(v\in(\ker f)^\perp\).

For a sequence of such maps, a lower bound that holds with one constant from
some index on extends to every index: the finitely many earlier indices each
have their own positive constant, and one takes the minimum.

## Main declarations

* `LinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker`: the positive lower
  bound on the orthogonal complement of the kernel.
* `Nat.exists_pos_forall_of_eventually`: an eventual positive constant for a
  downward-closed property, combined with a positive constant at each index,
  gives one positive constant at every index.
-/

namespace LinearMap

/-- A linear map on a finite-dimensional inner product space is bounded below on
the orthogonal complement of its kernel: there is \(\delta>0\) with
\(\delta\|v\|\le\|fv\|\) for all \(v\in(\ker f)^\perp\). -/
theorem exists_pos_mul_norm_le_of_mem_orthogonal_ker {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E →ₗ[𝕜] F) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ (LinearMap.ker f)ᗮ, δ * ‖v‖ ≤ ‖f v‖ := by
  have hi : Function.Injective (f.domRestrict (LinearMap.ker f)ᗮ) :=
    LinearMap.injective_domRestrict_iff.mpr (Submodule.orthogonal_disjoint _).symm
  obtain ⟨K, hK, hbound⟩ := (f.domRestrict (LinearMap.ker f)ᗮ).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr hi)
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr (by exact_mod_cast hK), fun v hv ↦ ?_⟩
  exact (inv_mul_le_iff₀ (show 0 < (K : ℝ) by exact_mod_cast hK)).mpr
    (ZeroHomClass.bound_of_antilipschitz _ hbound ⟨v, hv⟩)

end LinearMap

/-- Let \(P(N,\gamma)\) be a property of an index \(N\) and a constant \(\gamma\)
that is closed under decreasing \(\gamma\). If \(P(N,\delta)\) holds for all
\(N\ge M\) with one \(\delta>0\), and each index has some positive constant, then
one positive constant works at every index. -/
theorem Nat.exists_pos_forall_of_eventually {P : ℕ → ℝ → Prop}
    (hmono : ∀ N {γ δ : ℝ}, γ ≤ δ → P N δ → P N γ)
    (hfix : ∀ N, ∃ η : ℝ, 0 < η ∧ P N η) {M : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hev : ∀ N, M ≤ N → P N δ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N, P N γ := by
  induction M generalizing δ with
  | zero => exact ⟨δ, hδ, fun N ↦ hev N (Nat.zero_le N)⟩
  | succ M ih =>
    obtain ⟨η, hη, hM⟩ := hfix M
    refine ih (lt_min hδ hη) fun N hN ↦ ?_
    rcases eq_or_lt_of_le hN with rfl | hN
    · exact hmono _ (min_le_right δ η) hM
    · exact hmono _ (min_le_left δ η) (hev N hN)
