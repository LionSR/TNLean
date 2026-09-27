/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.AKLTParentHamiltonian
import TNLean.MPS.ParentHamiltonian.Martingale.OpenHamiltonian

/-!
# AKLT chain: fourfold open-boundary degeneracy

**Source.** Cirac--Pérez-García--Schuch--Verstraete 2021 (arXiv:2011.12127),
subsubsection "SPT phases and edge modes",
`Papers/2011.12127/TN-Review-main.tex` lines 1171--1174: the ground-state
degeneracy of an MPS parent Hamiltonian with open boundary conditions comes from
boundary vectors on both sides, and "for the case of the AKLT model, this
indeed leads to a \(4\)-fold degeneracy". Line 2095 of the same
file states that the two-site AKLT parent Hamiltonian already suffices, via the
hand check \(\mathcal G_{1,2}\cap\mathcal G_{2,3}=\mathcal G_{1,2,3}\).

**Formalized here.** For every \(N \ge 2\), the kernel of the open-chain
two-site AKLT parent Hamiltonian on \(N\) sites is the open-boundary MPS space
\(\{σ ↦ ⟨l|A^σ|r⟩\}\), spanned by the boundary vectors
\((⟨l|, |r⟩) ∈ ℂ^2 × ℂ^2\), and it is four-dimensional. The three-site open
parent Hamiltonian has the same four-dimensional kernel for \(N \ge 3\).

The tensor is the one of the AKLT example module, which is the review's Pauli
form of lines 2390--2392 rescaled by \(\sqrt{2/3}\) and read in a rotated
physical basis (see the module docstring of the two-site AKLT parent
Hamiltonian). Neither change affects local ground spaces or kernel dimensions.

Line 1174 continues: only one state of this four-dimensional space lies in the
spin-\(0\) sector. That sentence needs the total-spin operator on \(N\) spin-\(1\)
sites and is not formalized here.

## Main results

* `MPSTensor.aklt_ker_openParentHamiltonianES_two_eq_groundSpaceES`
* `MPSTensor.aklt_finrank_ker_openParentHamiltonianES_two`
* `MPSTensor.aklt_ker_openParentHamiltonianES_two_eq_span_boundaryVectors`
* `MPSTensor.aklt_finrank_ker_openParentHamiltonianES_three`

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair
  states: Concepts, symmetries, theorems*
-/

open scoped Matrix

namespace MPSTensor

/-- Every kernel vector of the open-chain two-site AKLT parent Hamiltonian lies
in the open-boundary MPS space.

For \(N = 2\) the Hamiltonian is the local projector itself. For \(N \ge 3\)
every three-site window restricts on both sides to nonwrapping two-site
windows, and the hand check of arXiv:2011.12127, line 2095, grows these
constraints to the three-site window; the open-chain growth theorem for the
block-injective AKLT tensor (\(L_0 = 2\)) then covers the whole chain. -/
theorem aklt_ker_openParentHamiltonianES_two_le_groundSpaceES {N : ℕ} (hN : 2 ≤ N) :
    LinearMap.ker (openParentHamiltonianES akltTensor 2 N) ≤ groundSpaceES akltTensor N := by
  rcases hN.eq_or_lt with rfl | hN3
  · rw [openParentHamiltonianES_self_eq_parentInteractionES akltTensor (by norm_num)]
    intro v hv
    exact (parentInteractionES_apply_eq_zero_iff akltTensor 2 v).1 (LinearMap.mem_ker.1 hv)
  · intro v hv
    have hNpos : 0 < N := by omega
    rw [mem_groundSpaceES_iff]
    apply contiguous_mem_groundSpace_of_isNBlkInjective aklt_isNBlkInjective_two
      (by norm_num) (by omega : 2 + 1 ≤ N)
    intro s hs τ
    let i : Fin N := ⟨s, by omega⟩
    rw [← cyclicRestrictₗ_eq_contiguousRestrictₗ hNpos (by omega) (i := i) hs]
    apply aklt_mem_groundSpace_three_of_inLeftGround_of_inRightGround
    · intro j
      rw [cyclicRestrictₗ_restrictLast]
      exact cyclicRestrictₗ_mem_groundSpace_of_mem_ker_openParentHamiltonianES
        akltTensor hN hv i (by change s + 2 ≤ N; omega) _
    · intro j
      rw [cyclicRestrictₗ_restrictFirst hNpos (by omega)]
      refine cyclicRestrictₗ_mem_groundSpace_of_mem_ker_openParentHamiltonianES
        akltTensor hN hv _ ?_ _
      change (s + 1) % N + 2 ≤ N
      rw [Nat.mod_eq_of_lt (by omega)]
      omega

/-- Source: arXiv:2011.12127, lines 1174 and 2095. For \(N \ge 2\), the kernel
of the open-chain two-site AKLT parent Hamiltonian is the open-boundary MPS
space \(\{σ ↦ \operatorname{tr}(A^σ X)\}\). -/
theorem aklt_ker_openParentHamiltonianES_two_eq_groundSpaceES {N : ℕ} (hN : 2 ≤ N) :
    LinearMap.ker (openParentHamiltonianES akltTensor 2 N) = groundSpaceES akltTensor N :=
  le_antisymm (aklt_ker_openParentHamiltonianES_two_le_groundSpaceES hN)
    (groundSpaceES_le_ker_openParentHamiltonianES akltTensor 2 N)

/-- Source: arXiv:2011.12127, line 1174: **fourfold open-boundary degeneracy of
the AKLT chain.** For \(N \ge 2\), the open-chain two-site AKLT parent
Hamiltonian has a four-dimensional kernel. -/
theorem aklt_finrank_ker_openParentHamiltonianES_two {N : ℕ} (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (openParentHamiltonianES akltTensor 2 N)) = 4 := by
  rw [aklt_ker_openParentHamiltonianES_two_eq_groundSpaceES hN,
    groundSpaceES_finrank_eq_of_isNBlkInjective_of_le aklt_isNBlkInjective_two
      (by norm_num) hN]
  norm_num

/-- Source: arXiv:2011.12127, line 1174 ("we can define boundary vectors on both
sides"). For \(N \ge 2\), the kernel of the open-chain two-site AKLT parent
Hamiltonian is spanned by the open-boundary MPS \(σ ↦ ⟨l|A^σ|r⟩\), with
boundary vectors \((⟨l|, |r⟩)\) ranging over \(ℂ^2 × ℂ^2\). -/
theorem aklt_ker_openParentHamiltonianES_two_eq_span_boundaryVectors {N : ℕ} (hN : 2 ≤ N) :
    LinearMap.ker (openParentHamiltonianES akltTensor 2 N) =
      Submodule.span ℂ (Set.range fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) =>
        WithLp.toLp 2 fun σ : Cfg 3 N =>
          p.1 ⬝ᵥ (Kraus.evalWord akltTensor (List.ofFn σ) *ᵥ p.2)) := by
  rw [aklt_ker_openParentHamiltonianES_two_eq_groundSpaceES hN, groundSpaceES,
    groundSpace_eq_span_boundaryVectors, Submodule.map_span, ← Set.range_comp]
  rfl

/-- Source: arXiv:2011.12127, line 1174, for the three-site open parent
Hamiltonian. For \(N \ge 3\) its kernel is four-dimensional; this is the
general boundary-degeneracy count at the injectivity length \(L_0 = 2\). -/
theorem aklt_finrank_ker_openParentHamiltonianES_three {N : ℕ} (hN : 3 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (openParentHamiltonianES akltTensor 3 N)) = 4 := by
  rw [finrank_ker_openParentHamiltonianES_of_isNBlkInjective (L₀ := 2)
    aklt_isNBlkInjective_two (by norm_num) hN]
  norm_num

end MPSTensor
