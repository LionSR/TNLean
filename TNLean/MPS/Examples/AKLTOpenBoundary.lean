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
file states that the two-site AKLT parent Hamiltonian already has a unique
periodic ground state, via the hand check
\(\mathcal G_{1,2}\cap\mathcal G_{2,3}=\mathcal G_{1,2,3}\).

Primary sources for the open-chain count. Nachtergaele, arXiv:cond-mat/9410110,
`References/cond-mat_9410110/main.tex` lines 1505--1510 and 1545--1558,
summarizing Fannes--Nachtergaele--Werner (lines 1484--1486): the local support
spaces of a pure generalized valence-bond-solid state with auxiliary algebra
\(M_k\) have dimension \(k^2\) on long intervals, and they are the kernels of
the open-interval Hamiltonian (equations (3.12)--(3.13)).
Pérez-García--Verstraete--Wolf--Cirac, arXiv:quant-ph/0608197,
`Papers/quant-ph_0608197/MPSarchive.tex` lines 1211--1233: the growth argument
on an open chain, which places every ground state of the nearest-neighbour
projector Hamiltonian in the span of \(\operatorname{tr}(Y B^{i_j} \cdots B^{i_k})\)
on growing windows.

**Formalized here.** For every \(N \ge 2\), the kernel of the open-chain
two-site AKLT parent Hamiltonian on \(N\) sites is the open-boundary MPS space
\(\{σ ↦ (l|A^σ|r)\}\), spanned by the open-boundary states with boundary vectors
\(((l|, |r)) ∈ ℂ^2 × ℂ^2\), and it is four-dimensional. The three-site open
parent Hamiltonian has the same four-dimensional kernel for \(N \ge 3\).

These statements concern the projector parent Hamiltonian of the AKLT tensor.
The review's line 1174 speaks of the AKLT model, whose Hamiltonian is the
polynomial \(\vec S_i\cdot\vec S_{i+1} + \tfrac13(\vec S_i\cdot\vec S_{i+1})^2\);
the local identification with the spin-\(2\) projector is proved in
`AKLTPolynomialHamiltonian`. The open-chain energy shift and ground-space
identification are proved in `AKLTOpenPolynomialHamiltonian`.
The two-site statements combine line 1174 with the local hand check of line
2095, which the review prints for the periodic chain; the check itself is an
identity of three-site local spaces, and the proof reuses it on nonwrapping
windows.

The tensor is the one of the AKLT example module, which is the review's Pauli
form of lines 2390--2392 rescaled by \(\sqrt{2/3}\) and read in a rotated
physical basis (see the module docstring of the two-site AKLT parent
Hamiltonian). Neither change affects local ground spaces or kernel dimensions.

Line 1174 continues: only one state of this four-dimensional space lies in the
spin-\(0\) sector. That sentence needs the total-spin operator on \(N\) spin-\(1\)
sites. Its singlet and triplet sectors are proved in `AKLTSpinSectors`.

## Main results

* `MPSTensor.aklt_ker_openParentHamiltonianES_two_eq_groundSpaceES`
* `MPSTensor.aklt_finrank_ker_openParentHamiltonianES_two`
* `MPSTensor.aklt_ker_openParentHamiltonianES_two_eq_span_openState`
* `MPSTensor.aklt_finrank_ker_openParentHamiltonianES_three`

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair
  states: Concepts, symmetries, theorems*
- [arXiv:cond-mat/9410110](https://arxiv.org/abs/cond-mat/9410110) -- Nachtergaele,
  *The spectral gap for some spin chains with discrete symmetry breaking*
- [arXiv:quant-ph/0608197](https://arxiv.org/abs/quant-ph/0608197) -- Pérez-García,
  Verstraete, Wolf, Cirac, *Matrix product state representations*
-/

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

/-- Project result: for \(N \ge 2\), the kernel of the open-chain two-site AKLT
parent Hamiltonian is the open-boundary MPS space
\(\{σ ↦ \operatorname{tr}(A^σ X)\}\).

This combines two passages of arXiv:2011.12127 that neither states alone: the
open-boundary ground space of line 1174, and the hand check
\(\mathcal G_{1,2}\cap\mathcal G_{2,3}=\mathcal G_{1,2,3}\) of line 2095, which
the review prints for the periodic chain and which is a local identity reused
here on nonwrapping windows. -/
theorem aklt_ker_openParentHamiltonianES_two_eq_groundSpaceES {N : ℕ} (hN : 2 ≤ N) :
    LinearMap.ker (openParentHamiltonianES akltTensor 2 N) = groundSpaceES akltTensor N :=
  le_antisymm (aklt_ker_openParentHamiltonianES_two_le_groundSpaceES hN)
    (groundSpaceES_le_ker_openParentHamiltonianES akltTensor 2 N)

/-- For \(N \ge 2\), the open-chain two-site projector parent Hamiltonian of
the AKLT tensor has a four-dimensional kernel. The fourfold count in
arXiv:2011.12127, line 1174, concerns the AKLT model. The polynomial
Hamiltonian of that passage is identified with the shifted projector sum in
`AKLTOpenPolynomialHamiltonian`; the present statement concerns the projector kernel. -/
theorem aklt_finrank_ker_openParentHamiltonianES_two {N : ℕ} (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (openParentHamiltonianES akltTensor 2 N)) = 4 := by
  rw [aklt_ker_openParentHamiltonianES_two_eq_groundSpaceES hN,
    groundSpaceES_finrank_eq_of_isNBlkInjective
      (isNBlkInjective_of_le (by norm_num) aklt_isNBlkInjective_two hN)]
  norm_num

/-- Source: arXiv:2011.12127, line 1174 ("we can define boundary vectors on both
sides"). For \(N \ge 2\), the kernel of the open-chain two-site AKLT parent
Hamiltonian is spanned by the open-boundary states \(σ ↦ (l|A^σ|r)\), with
boundary vectors \(((l|, |r))\) ranging over \(ℂ^2 × ℂ^2\). -/
theorem aklt_ker_openParentHamiltonianES_two_eq_span_openState {N : ℕ} (hN : 2 ≤ N) :
    LinearMap.ker (openParentHamiltonianES akltTensor 2 N) =
      Submodule.span ℂ (Set.range fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) =>
        WithLp.toLp 2 (openState p.1 p.2 akltTensor N)) := by
  rw [aklt_ker_openParentHamiltonianES_two_eq_groundSpaceES hN, groundSpaceES,
    groundSpace_eq_span_openState, Submodule.map_span, ← Set.range_comp]
  rfl

/-- Project result: for \(N \ge 3\), the open-chain three-site AKLT parent
Hamiltonian has a four-dimensional kernel. This is the specialization of
`finrank_ker_openParentHamiltonianES_of_isNBlkInjective` to the AKLT tensor at
its injectivity length \(L_0 = 2\); it is a project corollary, not a statement
printed in the review. -/
theorem aklt_finrank_ker_openParentHamiltonianES_three {N : ℕ} (hN : 3 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (openParentHamiltonianES akltTensor 3 N)) = 4 := by
  rw [finrank_ker_openParentHamiltonianES_of_isNBlkInjective (L₀ := 2)
    aklt_isNBlkInjective_two (by norm_num) hN]
  norm_num

end MPSTensor
