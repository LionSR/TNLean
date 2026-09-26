/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Logic.Equiv.Fin.Basic
import TNLean.PEPS.TorusSiteTensor

/-!
# CZX: the CZX ground state as a PEPS and as a product of plaquette GHZ states

**Source.** Chen, Liu, Wen 2011 (arXiv:1106.4752), Section "CZX model",
`References/1106.4752/source/dDSPTmodel.tex` lines 270–323: each site of a square lattice
carries four qubits, one at each corner, and the ground state is the product over plaquettes
of the four-qubit states $\lvert 0000\rangle+\lvert 1111\rangle$.
Review: arXiv:2011.12127, Appendix A, "Two dimensions: PEPS", "The CZX model",
`Papers/2011.12127/TN-Review-main.tex` lines 2502–2514: on a torus of `2N × 2M` qubits the
state $\bigotimes_{i,j}\lvert\mathrm{GHZ}_{ij}\rangle$ is, after blocking the four qubits of
a site, the PEPS with bond dimension `D = d^2 = 4` and tensor
$\sum_{i,j,k,l=0}^{1}\lvert ijkl\rangle((i,j),(j,k),(k,l),(l,i)\rvert$.

**Formalized here.** The review's tensor at every site of the discrete torus generates the
product over plaquettes of the unnormalized GHZ coefficients: its coefficient at `σ` is `1`
when, for every site `v`, the four qubits around the plaquette at the upper right corner of
`v` agree, and `0` otherwise.

The qubits `|ijkl⟩` of a site are its top-left, top-right, bottom-right and bottom-left
corners, and the four virtual legs are ordered top, right, down, left (line 2415), so each
leg carries the pair of corner qubits on its side, listed clockwise around the site.

**Local fix (CZX bond orientation):** the review contracts every bond by the maximally
entangled pair $\sum_n\lvert n)\lvert n)$ (lines 271–276), identifying equal bond labels at
its two ends. With the printed tensor this sets the top-right qubit of a site equal to the
bottom-left qubit of its right neighbour and of its upper neighbour, and the resulting state
is a product of GHZ states along diagonal loops winding around the torus, not the product of
plaquette states. Two neighbouring sites list the qubits of their common side in opposite
orders, so the plaquette state is obtained by identifying the pair `(a, b)` at one end of a
bond with `(b, a)` at the other; `czxPEPS` reads the down and left labels of the printed
tensor in reverse (`czxBondSwap`). Documented in
`docs/paper-gaps/rmp_peps_czx_bond_orientation.tex`.

**Scope restriction (torus size):** the plaquette formula is stated for a torus of width
and height at least three sites. On a torus of width two the two horizontal bonds between a
pair of neighbouring sites are one edge of the simple lattice graph, so the four legs of a
site are not four distinct bonds; the source's torus of `2N × 2M` qubits also allows
`N, M ∈ {1, 2}`. Documented in `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

The review's statement that the CZX model belongs to the non-trivial symmetry-protected
sector of the on-site `ℤ₂` symmetry (line 2516) is not restated here; the anomaly class of
the boundary symmetry is the subject of the matrix product unitary modules
(`TNLean/MPS/Examples/CZX/`).

## Main definitions

* `TNLean.PEPS.czxBond`, `TNLean.PEPS.czxQubits`: the bond label of a pair of qubits and the
  physical label `|ijkl⟩` of a site.
* `TNLean.PEPS.czxSiteTensor`: the review's tensor
  $\sum_{ijkl}\lvert ijkl\rangle((i,j),(j,k),(k,l),(l,i)\rvert$.
* `TNLean.PEPS.czxPEPS`: the tensor at every site of the torus.

## Main results

* `TNLean.PEPS.stateCoeff_czxPEPS`: the PEPS is the product of plaquette GHZ states.

## References

- [arXiv:1106.4752](https://arxiv.org/abs/1106.4752) -- X. Chen, Z.-X. Liu, X.-G. Wen,
  *Two-dimensional symmetry-protected topological orders and their protected gapless edge
  excitations*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

/-! ### Qubit labels -/

/-- The bond label `(a, b)` of a pair of qubits, a basis index of the bond of dimension
`4 = 2 × 2`. -/
def czxBond : Fin 2 × Fin 2 ≃ Fin 4 :=
  finProdFinEquiv

/-- The physical label `|ijkl⟩` of the four qubits of a site, read as `((i, j), (k, l))`. -/
def czxQubits : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) ≃ Fin 16 :=
  (czxBond.prodCongr czxBond).trans finProdFinEquiv

/-- The top-left qubit `i` of a site. -/
def czxTopLeft (s : Fin 16) : Fin 2 := (czxQubits.symm s).1.1

/-- The top-right qubit `j` of a site. -/
def czxTopRight (s : Fin 16) : Fin 2 := (czxQubits.symm s).1.2

/-- The bottom-right qubit `k` of a site. -/
def czxBottomRight (s : Fin 16) : Fin 2 := (czxQubits.symm s).2.1

/-- The bottom-left qubit `l` of a site. -/
def czxBottomLeft (s : Fin 16) : Fin 2 := (czxQubits.symm s).2.2

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2513–2514.
The review's CZX tensor $\sum_{i,j,k,l}\lvert ijkl\rangle((i,j),(j,k),(k,l),(l,i)\rvert$,
virtual arguments ordered top, right, down, left. The sum over `i, j, k, l` collapses to
the four qubits of the physical label `s`. -/
def czxSiteTensor (t r b l : Fin 4) (s : Fin 16) : ℂ :=
  if t = czxBond (czxTopLeft s, czxTopRight s) ∧ r = czxBond (czxTopRight s, czxBottomRight s) ∧
      b = czxBond (czxBottomRight s, czxBottomLeft s) ∧
      l = czxBond (czxBottomLeft s, czxTopLeft s) then 1 else 0

/-- The bond label of the reversed pair: `czxBondSwap (czxBond (a, b)) = czxBond (b, a)`. -/
def czxBondSwap : Fin 4 ≃ Fin 4 :=
  czxBond.symm.trans ((Equiv.prodComm _ _).trans czxBond)

@[simp] theorem czxBondSwap_czxBond (a b : Fin 2) :
    czxBondSwap (czxBond (a, b)) = czxBond (b, a) := by
  simp [czxBondSwap]

variable (width height : ℕ) [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2502–2514.
The CZX tensor at every site of the `width × height` torus, with the down and left labels of
`czxSiteTensor` read in reverse, so that each bond identifies the pair `(a, b)` at one end with
`(b, a)` at the other (the module's local fix on the bond orientation). -/
def czxPEPS : Tensor (torusGraph width height) 16 :=
  torusSiteTensor fun t r b l s => czxSiteTensor t r (czxBondSwap b) (czxBondSwap l) s

variable {width height}

omit [NeZero width] [NeZero height] [Fact (1 < width)] [Fact (1 < height)] in
/-- The bond constraints of the CZX PEPS, stated site by site, are equivalent to the
plaquette constraints: for every site `v`, the top-right qubit of `v`, the top-left qubit of
its right neighbour, the bottom-right qubit of its upper neighbour and the bottom-left qubit
of its upper-right neighbour agree. -/
theorem czx_bond_iff_plaquette {α : Type*} (i j k l : TorusVertex width height → α) :
    (∀ v : TorusVertex width height,
        (j (v.1, v.2 - 1) = k v ∧ i (v.1, v.2 - 1) = l v) ∧
          (k (v.1 - 1, v.2) = l v ∧ j (v.1 - 1, v.2) = i v)) ↔
      ∀ v : TorusVertex width height, j v = i (v.1 + 1, v.2) ∧ j v = k (v.1, v.2 + 1) ∧
        j v = l (v.1 + 1, v.2 + 1) := by
  constructor
  · intro H v
    have h1 := H (v.1 + 1, v.2)
    have h2 := H (v.1, v.2 + 1)
    have h3 := H (v.1 + 1, v.2 + 1)
    simp only [add_sub_cancel_right] at h1 h2 h3
    exact ⟨h1.2.2, h2.1.1, h1.2.2.trans h3.1.2⟩
  · intro H v
    have a := H (v.1, v.2 - 1)
    have b := H (v.1 - 1, v.2)
    have c := H (v.1 - 1, v.2 - 1)
    simp only [sub_add_cancel] at a b c
    exact ⟨⟨a.2.1, c.1.symm.trans c.2.2⟩, ⟨c.2.1.symm.trans c.2.2, b.1⟩⟩

variable [Fact (2 < width)] [Fact (2 < height)]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2502–2514;
arXiv:1106.4752, `References/1106.4752/source/dDSPTmodel.tex` lines 317–321.
The CZX PEPS is the product over plaquettes of the unnormalized four-qubit GHZ states
$\lvert 0000\rangle+\lvert 1111\rangle$: its coefficient at `σ` is the product, over the
plaquettes at the upper right corner of each site `v`, of the indicator that the four qubits
of the plaquette agree. Stated for width and height at least three (the module's scope
restriction on the torus size). -/
theorem stateCoeff_czxPEPS (σ : TorusVertex width height → Fin 16) :
    stateCoeff (czxPEPS width height) σ =
      ∏ v, if czxTopRight (σ v) = czxTopLeft (σ (v.1 + 1, v.2)) ∧
          czxTopRight (σ v) = czxBottomRight (σ (v.1, v.2 + 1)) ∧
          czxTopRight (σ v) = czxBottomLeft (σ (v.1 + 1, v.2 + 1)) then 1 else 0 := by
  rw [czxPEPS, stateCoeff_torusSiteTensor,
    Fintype.sum_eq_single (fun v => czxBond (czxTopRight (σ v), czxBottomRight (σ v))),
    Fintype.sum_eq_single (fun v => czxBond (czxTopLeft (σ v), czxTopRight (σ v)))]
  · simp only [czxSiteTensor, czxBondSwap_czxBond, EmbeddingLike.apply_eq_iff_eq,
      Prod.mk.injEq, true_and, Finset.prod_boole, Finset.mem_univ, forall_const]
    have key := czx_bond_iff_plaquette (fun v => czxTopLeft (σ v)) (fun v => czxTopRight (σ v))
      (fun v => czxBottomRight (σ v)) (fun v => czxBottomLeft (σ v))
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (key.mp h1) h2
    · exact absurd (key.mpr h2) h1
    · rfl
  · intro vb hvb
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hvb
    exact Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_right fun h => hv h.1)
  · intro hb hhb
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hhb
    exact Finset.sum_eq_zero fun vb _ =>
      Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_right fun h => hv h.2.1)

end PEPS
end TNLean
