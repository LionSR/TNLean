/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CompactNormalParentGap

/-!
# Open-chain gaps at and above the quantum Wielandt range

A normal tensor of bond dimension \(D>0\) has a positive open-chain
parent-Hamiltonian gap at every interaction range \(R\ge D^4+1\),
uniformly over all chain lengths \(N\ge R\). The local interaction is
\(1-P_{\mathcal G_R}\), with \(\mathcal G_R\) the original tensor's
boundary-vector space. No normalization or change of physical sites is
required. More generally, injectivity at a positive length \(p\) gives
this conclusion at range \(p+1\).

The long-chain estimate follows from the martingale method and finite-interval
range comparison. The remaining finite set of chain lengths is controlled by
finite dimensionality and the exact open-chain ground-space identity.

**Scope restriction (single block and sufficient interaction range):** the gap
results here concern a single normal block and ranges strictly larger than a
positive injectivity length. The unrestricted assertion in arXiv:2011.12127,
Section IV.C, lines 2183--2187, also permits shorter ranges. For a tensor
with several blocks it fails at such a range (see
`docs/paper-gaps/cpgsv21_short_range_parent_gap.tex`);
shorter ranges for a single normal block are not treated here. The compact
several-block argument is documented in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Injectivity at \(p>0\) gives a uniform positive gap of the original
range-\(p+1\) open parent Hamiltonian at every admissible chain length,
including \(N=p+1\). Source: arXiv:2011.12127, Section IV.C,
lines 2183--2187; arXiv:cond-mat/9410110, Section 6. -/
theorem exists_openParentHamiltonianES_uniform_gap_of_isNBlkInjective_all_lengths
    [NeZero D] (A : MPSTensor d D) {p : ℕ} (hp : 0 < p)
    (hA : Kraus.IsNBlkInjective A p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, p + 1 ≤ N →
      ∀ v ∈ (groundSpaceES A N)ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES A (p + 1) N v‖ := by
  obtain ⟨W, _hW, δ, hδ, hlong⟩ :=
    exists_openParentHamiltonianES_uniform_gap_of_isNBlkInjective A hp hA
  refine Nat.exists_pos_forall_of_eventually
    (P := fun N γ => p + 1 ≤ N → ∀ v ∈ (groundSpaceES A N)ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A (p + 1) N v‖)
    (fun N γ η hle h hN v hv =>
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (h hN v hv))
    ?_ hδ (fun N hN _ => hlong N hN)
  intro N
  by_cases hN : p + 1 ≤ N
  · obtain ⟨η, hη, hgap⟩ :=
      (openParentHamiltonianES A (p + 1) N).exists_pos_mul_norm_le_of_mem_orthogonal_ker
    exact ⟨η, hη, fun _ => by
      simpa only [ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
        hA hp hN] using hgap⟩
  · exact ⟨1, one_pos, fun h => (hN h).elim⟩

/-- Once a tensor is injective at \(p>0\), every larger interaction range
\(R>p\) has a positive open-chain gap uniform over all \(N\ge R\).
Source: arXiv:0909.5347, lines 827--832; arXiv:2011.12127,
Section IV.C, lines 2183--2187. -/
theorem exists_openParentHamiltonianES_uniform_gap_of_isNBlkInjective_of_lt
    [NeZero D] (A : MPSTensor d D) {p R : ℕ} (hp : 0 < p)
    (hA : Kraus.IsNBlkInjective A p) (hR : p < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, R ≤ N →
      ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  have hInj : Kraus.IsNBlkInjective A (R - 1) :=
    isNBlkInjective_of_le hp hA (by omega)
  obtain ⟨δ, hδ, hgap⟩ :=
    exists_openParentHamiltonianES_uniform_gap_of_isNBlkInjective_all_lengths A
      (by omega : 0 < R - 1) hInj
  have hRange : R - 1 + 1 = R := by omega
  refine ⟨δ, hδ, fun N hN => ?_⟩
  have hKer : LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N := by
    simpa only [hRange] using ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
      hInj (by omega : 0 < R - 1) (by omega : R - 1 + 1 ≤ N)
  simpa only [hRange, hKer] using hgap N (by omega : R - 1 + 1 ≤ N)

/-- Every fixed interaction range \(R\ge D^4+1\) gives a uniform
positive open-chain gap for an arbitrary normal tensor of bond dimension
\(D>0\), at all \(N\ge R\). The Hamiltonian is formed from the
original tensor's local ground space. Source: arXiv:0909.5347, Theorem 1
and lines 827--832; arXiv:2011.12127, Section IV.C, lines 2183--2187. -/
theorem exists_openParentHamiltonianES_uniform_gap_of_isNormal_of_le
    [NeZero D] (A : MPSTensor d D) (hA : Kraus.IsNormal A)
    {R : ℕ} (hR : D ^ 4 + 1 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, R ≤ N →
      ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  exact exists_openParentHamiltonianES_uniform_gap_of_isNBlkInjective_of_lt A
    (pow_pos (NeZero.pos D) 4) (isNBlkInjective_pow_four_of_isNormal A hA) (by omega)

/-- A normal tensor has a positive open-chain parent gap at the explicit
interaction range \(D^4+1\), uniformly over every chain length
\(N\ge D^4+1\). No supplied blocking length or finite-window gap is
assumed. Source: arXiv:0909.5347, Theorem 1 and lines 827--832;
arXiv:2011.12127, Section IV.C, lines 2183--2187. -/
theorem exists_openParentHamiltonianES_uniform_gap_of_isNormal_all_lengths
    [NeZero D] (A : MPSTensor d D) (hA : Kraus.IsNormal A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, D ^ 4 + 1 ≤ N →
      ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A (D ^ 4 + 1) N))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES A (D ^ 4 + 1) N v‖ :=
  exists_openParentHamiltonianES_uniform_gap_of_isNormal_of_le A hA le_rfl

end MPSTensor
