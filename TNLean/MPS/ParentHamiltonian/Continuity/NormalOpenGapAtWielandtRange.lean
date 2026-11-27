/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Continuity.CompactNormalParentGap

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

open scoped ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- Injectivity at \(p>0\) gives a uniform positive gap of the original
range-\(p+1\) open parent Hamiltonian at every admissible chain length,
including \(N=p+1\): every eigenvalue is `0` or at least the gap. Source: arXiv:2011.12127,
Section IV.C, lines 2183--2187; arXiv:cond-mat/9410110, Section 6. -/
theorem exists_hamiltonian_parentChainInteraction_uniform_gap_of_isNBlkInjective_all_lengths
    [NeZero D] (A : MPSTensor d D) {p : ℕ} (hp : 0 < p)
    (hA : Kraus.IsNBlkInjective A p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, p + 1 ≤ N →
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A (p + 1) N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨W, _hW, δ, hδ, hlong⟩ :=
    exists_hamiltonian_parentChainInteraction_uniform_gap_of_isNBlkInjective A hp hA
  exact Nat.exists_pos_forall_of_eventually
    (P := fun N γ => p + 1 ≤ N → ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A (p + 1) N).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ)
    (fun N γ η hle h hN => ManyBody.forall_hasEigenvalue_mono hle (h hN))
    (fun N => (ManyBody.exists_pos_forall_hasEigenvalue
      (posSemidef_hamiltonian_parentChainInteraction A (p + 1) N)).imp
        fun η h => ⟨h.1, fun _ => h.2⟩)
    hδ (fun N hN _ => hlong N hN)

/-- Once a tensor is injective at \(p>0\), every larger interaction range
\(R>p\) has a positive open-chain gap uniform over all \(N\ge R\): every eigenvalue is `0` or
at least the gap. Source: arXiv:0909.5347, lines 827--832; arXiv:2011.12127,
Section IV.C, lines 2183--2187. -/
theorem exists_hamiltonian_parentChainInteraction_uniform_gap_of_isNBlkInjective_of_lt
    [NeZero D] (A : MPSTensor d D) {p R : ℕ} (hp : 0 < p)
    (hA : Kraus.IsNBlkInjective A p) (hR : p < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, R ≤ N →
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨q, rfl⟩ : ∃ q, R = q + 1 := ⟨R - 1, by omega⟩
  exact exists_hamiltonian_parentChainInteraction_uniform_gap_of_isNBlkInjective_all_lengths A
    (by omega : 0 < q) (Kraus.isNBlkInjective_of_le hp hA (by omega))

/-- Every fixed interaction range \(R\ge D^4+1\) gives a uniform
positive open-chain gap for an arbitrary normal tensor of bond dimension
\(D>0\), at all \(N\ge R\): every eigenvalue is `0` or at least the gap. The Hamiltonian is
formed from the original tensor's local ground space. Source: arXiv:0909.5347, Theorem 1
and lines 827--832; arXiv:2011.12127, Section IV.C, lines 2183--2187. -/
theorem exists_hamiltonian_parentChainInteraction_uniform_gap_of_isNormal_of_le
    [NeZero D] (A : MPSTensor d D) (hA : Kraus.IsNormal A)
    {R : ℕ} (hR : D ^ 4 + 1 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, R ≤ N →
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ :=
  exists_hamiltonian_parentChainInteraction_uniform_gap_of_isNBlkInjective_of_lt A
    (pow_pos (NeZero.pos D) 4) (isNBlkInjective_pow_four_of_isNormal A hA) (by omega)

/-- A normal tensor has a positive open-chain parent gap at the explicit
interaction range \(D^4+1\), uniformly over every chain length
\(N\ge D^4+1\): every eigenvalue is `0` or at least the gap. No supplied blocking length or
finite-window gap is assumed. Source: arXiv:0909.5347, Theorem 1 and lines 827--832;
arXiv:2011.12127, Section IV.C, lines 2183--2187. -/
theorem exists_hamiltonian_parentChainInteraction_uniform_gap_of_isNormal_all_lengths
    [NeZero D] (A : MPSTensor d D) (hA : Kraus.IsNormal A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, D ^ 4 + 1 ≤ N →
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A (D ^ 4 + 1) N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ :=
  exists_hamiltonian_parentChainInteraction_uniform_gap_of_isNormal_of_le A hA le_rfl

end MPSTensor
