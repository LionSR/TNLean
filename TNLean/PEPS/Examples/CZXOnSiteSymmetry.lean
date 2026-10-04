/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.CZX
import TNLean.PEPS.OnSiteOperator

/-!
# CZX physical symmetry and local tensor pull-through

The on-site symmetry is the product of four Pauli flips and the four cyclic
controlled-phase gates. Its action on the actual CZX tensor pulls through to
`(X ⊗ X) CZ` on each virtual leg. These local identities and the torus-state
invariance are independent of the matrix-product representation of the boundary.

**Local fix (CZX bond orientation):** bottom and left virtual pairs are reversed
in the native torus PEPS. This is the bond orientation used by the source's
plaquette state; see `docs/paper-gaps/rmp_peps_czx_bond_orientation.tex`.

**Scope restriction (torus size):** the global invariance theorem assumes both
periods are at least three, so all four native bonds are distinct. See
`docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

## References

- [arXiv:1106.4752](https://arxiv.org/abs/1106.4752), CZX model, source lines 283–312.
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127), Appendix A, source lines 2502–2516.
-/

open scoped BigOperators Matrix
open Matrix

namespace TNLean
namespace PEPS

/-! ### The on-site symmetry -/

/-- The Pauli `X` on each of the four qubits of a site. -/
def czxSiteFlip : Equiv.Perm (Fin 16) :=
  czxQubits.permCongr
    ((Fin.revPerm.prodCongr Fin.revPerm).prodCongr (Fin.revPerm.prodCongr Fin.revPerm))

@[simp] theorem czxTopLeft_czxSiteFlip (s : Fin 16) :
    czxTopLeft (czxSiteFlip s) = (czxTopLeft s).rev := by
  simp [czxSiteFlip, czxTopLeft, Equiv.permCongr_apply]

@[simp] theorem czxTopRight_czxSiteFlip (s : Fin 16) :
    czxTopRight (czxSiteFlip s) = (czxTopRight s).rev := by
  simp [czxSiteFlip, czxTopRight, Equiv.permCongr_apply]

@[simp] theorem czxBottomRight_czxSiteFlip (s : Fin 16) :
    czxBottomRight (czxSiteFlip s) = (czxBottomRight s).rev := by
  simp [czxSiteFlip, czxBottomRight, Equiv.permCongr_apply]

@[simp] theorem czxBottomLeft_czxSiteFlip (s : Fin 16) :
    czxBottomLeft (czxSiteFlip s) = (czxBottomLeft s).rev := by
  simp [czxSiteFlip, czxBottomLeft, Equiv.permCongr_apply]

@[simp] theorem czxSiteFlip_czxQubits (i j k l : Fin 2) :
    czxSiteFlip (czxQubits ((i, j), (k, l))) = czxQubits ((i.rev, j.rev), (k.rev, l.rev)) := by
  simp [czxSiteFlip, Equiv.permCongr_apply]

theorem czxSiteFlip_czxSiteFlip (s : Fin 16) : czxSiteFlip (czxSiteFlip s) = s := by
  obtain ⟨⟨⟨i, j⟩, ⟨k, l⟩⟩, rfl⟩ := czxQubits.surjective s
  simp

theorem czxSiteFlip_symm : czxSiteFlip.symm = czxSiteFlip :=
  Equiv.ext fun s => by rw [Equiv.symm_apply_eq, czxSiteFlip_czxSiteFlip]

/-- The exponent of the phase of `U_{CZ} = CZ₁₂CZ₂₃CZ₃₄CZ₄₁` on the state `|ijkl⟩` of a site,
`ij + jk + kl + li`. -/
def czxCZExponent (s : Fin 16) : ℕ :=
  (czxTopLeft s).val * (czxTopRight s).val + (czxTopRight s).val * (czxBottomRight s).val +
    (czxBottomRight s).val * (czxBottomLeft s).val +
      (czxBottomLeft s).val * (czxTopLeft s).val

/-- Source: arXiv:1106.4752, `References/1106.4752/source/dDSPTmodel.tex` lines 283–294. The
on-site symmetry `U_{CZX} = U_X U_{CZ}` of a site: first the controlled-`Z` gates on the four
pairs of neighbouring qubits of the site, then the Pauli `X` on each qubit. -/
noncomputable def czxOnSite : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.monomial czxSiteFlip 1 * Matrix.diagonal fun s => (-1 : ℂ) ^ czxCZExponent s

/-- `U_{CZX}` is the monomial matrix that flips all four qubits with the controlled-`Z` sign of
the input. -/
theorem czxOnSite_eq_monomial :
    czxOnSite = Matrix.monomial czxSiteFlip fun s => (-1 : ℂ) ^ czxCZExponent s := by
  ext t s
  simp [czxOnSite, Matrix.mul_diagonal, Matrix.monomial_apply]

/-! ### Invariance of the CZX PEPS -/

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]

/-- On a plaquette-constant configuration of the torus, the product of the controlled-`Z` signs
of all sites is `1`: each pair of neighbouring plaquettes meets at two sites, and their
controlled-`Z` gates cancel (arXiv:1106.4752, `References/1106.4752/source/dDSPTmodel.tex`
line 312). -/
theorem prod_neg_one_pow_czxCZExponent (σ : TorusVertex width height → Fin 16)
    (h : ∀ v : TorusVertex width height, czxTopRight (σ v) = czxTopLeft (σ (v.1 + 1, v.2)) ∧
      czxTopRight (σ v) = czxBottomRight (σ (v.1, v.2 + 1)) ∧
      czxTopRight (σ v) = czxBottomLeft (σ (v.1 + 1, v.2 + 1))) :
    ∏ v, (-1 : ℂ) ^ czxCZExponent (σ v) = 1 := by
  set P : TorusVertex width height → ℕ := fun v => (czxTopRight (σ v)).val with hP
  have htl : ∀ v : TorusVertex width height, (czxTopLeft (σ v)).val = P (v.1 - 1, v.2) := by
    intro v
    have := (h (v.1 - 1, v.2)).1
    simp only [sub_add_cancel] at this
    simp [hP, this]
  have hbr : ∀ v : TorusVertex width height, (czxBottomRight (σ v)).val = P (v.1, v.2 - 1) := by
    intro v
    have := (h (v.1, v.2 - 1)).2.1
    simp only [sub_add_cancel] at this
    simp [hP, this]
  have hbl : ∀ v : TorusVertex width height,
      (czxBottomLeft (σ v)).val = P (v.1 - 1, v.2 - 1) := by
    intro v
    have := (h (v.1 - 1, v.2 - 1)).2.2
    simp only [sub_add_cancel] at this
    simp [hP, this]
  have hexp : ∀ v : TorusVertex width height, czxCZExponent (σ v) =
      P (v.1 - 1, v.2) * P v + P v * P (v.1, v.2 - 1) +
        P (v.1, v.2 - 1) * P (v.1 - 1, v.2 - 1) + P (v.1 - 1, v.2 - 1) * P (v.1 - 1, v.2) := by
    intro v
    simp only [czxCZExponent, htl, hbr, hbl]
    rfl
  -- the third and fourth sums are the first two, shifted down and to the left
  have h3 : ∑ v : TorusVertex width height, P (v.1, v.2 - 1) * P (v.1 - 1, v.2 - 1) =
      ∑ v : TorusVertex width height, P (v.1 - 1, v.2) * P v :=
    Fintype.sum_equiv ((Equiv.refl _).prodCongr (Equiv.subRight 1)) _ _ fun ⟨x, y⟩ => by
      simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, Equiv.subRight_apply]
      ring
  have h4 : ∑ v : TorusVertex width height, P (v.1 - 1, v.2 - 1) * P (v.1 - 1, v.2) =
      ∑ v : TorusVertex width height, P v * P (v.1, v.2 - 1) :=
    Fintype.sum_equiv ((Equiv.subRight 1).prodCongr (Equiv.refl _)) _ _ fun ⟨x, y⟩ => by
      simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, Equiv.subRight_apply]
      ring
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [hexp, Finset.sum_add_distrib, h3, h4]
  rw [show ∀ a b : ℕ, a + b + a + b = 2 * (a + b) from fun a b => by ring, pow_mul]
  simp

variable [Fact (1 < width)] [Fact (1 < height)] [Fact (2 < width)] [Fact (2 < height)]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2502–2516, and
arXiv:1106.4752, `References/1106.4752/source/dDSPTmodel.tex` lines 310–312: the CZX PEPS is
invariant under the on-site symmetry `U_{CZX}` applied at every site. Stated for width and
height at least three (the module's scope restriction on the torus size). -/
theorem onSiteOperator_czxOnSite_mulVec_stateCoeff_czxPEPS :
    onSiteOperator czxOnSite *ᵥ stateCoeff (czxPEPS width height) =
      stateCoeff (czxPEPS width height) := by
  rw [czxOnSite_eq_monomial, onSiteOperator_monomial, Matrix.monomial_mulVec]
  funext σ'
  set σ := (Equiv.piCongrRight fun _ : TorusVertex width height => czxSiteFlip).symm σ' with hσ
  have hσ' : σ' = fun v => czxSiteFlip (σ v) := by
    funext v
    simp [hσ, czxSiteFlip_symm, Equiv.piCongrRight_symm_apply, czxSiteFlip_czxSiteFlip]
  rw [hσ', stateCoeff_czxPEPS, stateCoeff_czxPEPS, Finset.prod_boole, Finset.prod_boole]
  simp only [czxTopLeft_czxSiteFlip, czxTopRight_czxSiteFlip, czxBottomRight_czxSiteFlip,
    czxBottomLeft_czxSiteFlip, Fin.rev_inj]
  split_ifs with hc
  · rw [mul_one]
    exact prod_neg_one_pow_czxCZExponent σ fun v => hc v (Finset.mem_univ v)
  · rw [mul_zero]

end Torus

/-! ### Pulling the symmetry through one site tensor -/

/-- The Pauli `X` on both qubits of a bond. -/
def czxLegFlip : Equiv.Perm (Fin 4) :=
  czxBond.permCongr (Fin.revPerm.prodCongr Fin.revPerm)

@[simp] theorem czxLegFlip_czxBond (a b : Fin 2) :
    czxLegFlip (czxBond (a, b)) = czxBond (a.rev, b.rev) := by
  simp [czxLegFlip, Equiv.permCongr_apply]

/-- The controlled-`Z` sign `(-1)^{ab}` of the bond state `|ab⟩`. -/
def czxLegPhase (x : Fin 4) : ℂ :=
  (-1 : ℂ) ^ ((czxBond.symm x).1.val * (czxBond.symm x).2.val)

@[simp] theorem czxLegPhase_czxBond (a b : Fin 2) :
    czxLegPhase (czxBond (a, b)) = (-1 : ℂ) ^ (a.val * b.val) := by
  simp [czxLegPhase]

/-- The operator `V = (X ⊗ X) CZ` on the two qubits carried by one virtual leg. -/
noncomputable def czxLegOperator : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.monomial czxLegFlip czxLegPhase

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 1462–1466 (the
pulling-through of an on-site symmetry to the virtual level) and lines 2513–2516: the on-site
symmetry `U_{CZX}` applied to the physical index of the CZX tensor equals the operator
`V = (X ⊗ X) CZ` applied to each of its four virtual legs,
`∑_s (U_{CZX})_{s' s} A_{t r b l}^{s} = ∑_{t' r' b' l'} A_{t' r' b' l'}^{s'} V_{t' t} V_{r' r}
V_{b' b} V_{l' l}`, the right side written out for the monomial matrix `V`. -/
theorem czxOnSite_mul_czxSiteTensor (t r b l : Fin 4) (s' : Fin 16) :
    ∑ s, czxOnSite s' s * czxSiteTensor t r b l s =
      czxLegPhase t * czxLegPhase r * czxLegPhase b * czxLegPhase l *
        czxSiteTensor (czxLegFlip t) (czxLegFlip r) (czxLegFlip b) (czxLegFlip l) s' := by
  rw [czxOnSite_eq_monomial, Finset.sum_eq_single (czxSiteFlip s')]
  · obtain ⟨⟨⟨i, j⟩, ⟨k, m⟩⟩, rfl⟩ := czxQubits.surjective s'
    obtain ⟨⟨t₁, t₂⟩, rfl⟩ := czxBond.surjective t
    obtain ⟨⟨r₁, r₂⟩, rfl⟩ := czxBond.surjective r
    obtain ⟨⟨b₁, b₂⟩, rfl⟩ := czxBond.surjective b
    obtain ⟨⟨l₁, l₂⟩, rfl⟩ := czxBond.surjective l
    simp only [Matrix.monomial_apply, czxSiteFlip_czxQubits,
      czxSiteTensor, czxLegFlip_czxBond, czxLegPhase_czxBond, czxCZExponent, czxTopLeft,
      czxTopRight, czxBottomRight, czxBottomLeft, Equiv.symm_apply_apply,
      EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, Fin.rev_eq_iff, mul_ite, mul_one, mul_zero]
    by_cases hc : (t₁ = i.rev ∧ t₂ = j.rev) ∧ (r₁ = j.rev ∧ r₂ = k.rev) ∧
        (b₁ = k.rev ∧ b₂ = m.rev) ∧ l₁ = m.rev ∧ l₂ = i.rev
    · obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩ := hc
      simp only [Fin.rev_rev, and_self, ↓reduceIte, ← pow_add]
    · simp only [hc, ↓reduceIte]
  · intro s _ hs
    have hne : s' ≠ czxSiteFlip s := fun h => hs (by rw [h, czxSiteFlip_czxSiteFlip])
    simp [Matrix.monomial_apply, hne]
  · simp

end PEPS
end TNLean
