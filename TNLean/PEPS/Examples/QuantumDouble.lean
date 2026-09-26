/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Group
import TNLean.PEPS.GInjective

/-!
# Quantum double models: the primal and dual PEPS tensors

**Source.** Kitaev 1997 (arXiv:quant-ph/9707021), Section "The model based on a group
algebra", `References/quant-ph_9707021/source/anyons.tex` lines 662–690: for a finite group
`G` the spins on the edges of the lattice take values in `ℂ[G]`, with basis `|g⟩`; for
`G = ℤ₂` this is the toric code of Section "Toric codes and the corresponding Hamiltonians",
lines 189–226.
Schuch, Cirac, Pérez-García 2010 (arXiv:1001.3807), Section "The double models",
`Papers/1001.3807/paper_v3.tex` lines 2858–2921: after blocking and renormalization the
quantum-double PEPS tensor is
`K = ∑ |pq⁻¹, qr⁻¹, rs⁻¹, sp⁻¹⟩_p ⊗ |p,q⟩_v⟨r,s|_v`, colors on the bonds and every spin
the difference of its two adjacent colors, and it is `G`-isometric.
Review: arXiv:2011.12127, Appendix A, "The Toric Code and quantum double models",
`Papers/2011.12127/TN-Review-main.tex` lines 2450–2467. In the primal representation (the
figure `fig_app_tc-primal`, line 2456) a tensor carries the four edge spins
`g₁, g₂, g₃, g₄` of a plaquette and has the virtual labels `g₁g₂` (top), `g₂⁻¹g₃` (right),
`g₄g₃` (down) and `g₁g₄⁻¹` (left), which "fuse to the identity" (line 2465). In the dual
representation (lines 2460–2463, figure `fig_app_tc-dual`) the virtual legs carry plaquette
colors `h₁` (left), `h₂` (top), `h₃` (right), `h₄` (down) and the four physical spins are
`h₂h₁⁻¹, h₃h₂⁻¹, h₃h₄⁻¹, h₄h₁⁻¹`; this tensor "is `G`-injective (in fact, `G`-isometric)
with respect to the regular representation, as shifting all plaquette colors does not
affect the physical state" (line 2465).

**Formalized here.** For every finite group `G`:
* the dual tensor is invariant under shifting all four colors by the same group element and
  is `G`-injective and `G`-isometric (with factor `|G|`) for this regular representation;
* the virtual labels of the primal tensor satisfy `t r b⁻¹ l⁻¹ = 1` on its support, so for
  every representation `π` of `G`, in particular every irreducible one, the primal tensor
  absorbs the virtual operator `π(t) π(r) π(b)⁻¹ π(l)⁻¹` acting on its four legs; for a
  one-dimensional representation this is a scalar invariance of the tensor.
The toric code is the instance `G = ℤ₂`.

**Local fix (normalization and representation):** colours are shifted by right
multiplication, `h ↦ h g`, which leaves the differences `h h'⁻¹` unchanged for non-abelian `G`
as well; on each leg this is the right-regular representation, unitarily equivalent to the
left-regular one of arXiv:1001.3807, line 1697, through `h ↦ h⁻¹`. Neither source normalizes
the tensor, so `G`-isometry holds with the factor `|G|` (see `TNLean.PEPS.IsGIsometric`).
Documented in `docs/paper-gaps/scp10_quantum_double_g_isometry.tex`.

**Scope restriction (single tensor):** the review's statements about the whole network are
not formalized: the virtual symmetry of the primal PEPS under every irreducible representation
is proved as an identity of one tensor, not as a matrix product operator symmetry of the
contracted lattice, and the identification of the equal-weight superposition of plaquette
colorings with that of the Gauss-law configurations (lines 2460–2461) is not stated; on a
torus the differences of plaquette colorings are the Gauss-law configurations of trivial
holonomy. Documented in `docs/paper-gaps/scp10_quantum_double_g_isometry.tex`.

## Main definitions

* `TNLean.PEPS.quantumDoubleDualSpins`, `TNLean.PEPS.quantumDoubleDualTensor`: the dual
  tensor of the review.
* `TNLean.PEPS.colorShiftRep`: the simultaneous shift of the four colors.
* `TNLean.PEPS.quantumDoublePrimalLabels`, `TNLean.PEPS.quantumDoublePrimalTensor`: the
  primal tensor of the review.

## Main results

* `TNLean.PEPS.isGInjective_quantumDoubleDualTensor`,
  `TNLean.PEPS.isGIsometric_quantumDoubleDualTensor`,
  `TNLean.PEPS.isGIsometric_toricCodeDualTensor`.
* `TNLean.PEPS.quantumDoublePrimalTensor_ne_zero_mul_eq_one`,
  `TNLean.PEPS.quantumDoublePrimalTensor_ne_zero_map_mul_eq_one`,
  `TNLean.PEPS.quantumDoublePrimalTensor_smul_map_mul`,
  `TNLean.PEPS.character_mul_quantumDoublePrimalTensor`.

## References

- [arXiv:quant-ph/9707021](https://arxiv.org/abs/quant-ph/9707021) -- A. Yu. Kitaev,
  *Fault-tolerant quantum computation by anyons*
- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

/-! ### The dual tensor -/

section Dual

variable (G : Type*) [Group G]

/-- The coloring `(g, g, g, g)` of the four legs by one group element, by which all
plaquette colors are shifted. -/
def colorDiag (g : G) : G × G × G × G := (g, g, g, g)

@[simp] theorem colorDiag_one : colorDiag G 1 = 1 := rfl

theorem colorDiag_mul (g h : G) : colorDiag G (g * h) = colorDiag G g * colorDiag G h := rfl

variable {G}

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2460–2463 (figure
`fig_app_tc-dual`). The four physical spins `(h₂h₁⁻¹, h₃h₂⁻¹, h₃h₄⁻¹, h₄h₁⁻¹)` of the dual
tensor, the differences of adjacent plaquette colors, for the colors `(t, r, b, l)` on the
top, right, down and left legs, that is `(h₂, h₃, h₄, h₁)`. -/
def quantumDoubleDualSpins (c : G × G × G × G) : G × G × G × G :=
  (c.1 * c.2.2.2⁻¹, c.2.1 * c.1⁻¹, c.2.1 * c.2.2.1⁻¹, c.2.2.1 * c.2.2.2⁻¹)

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2465: shifting all
plaquette colors does not change the physical spins. -/
@[simp] theorem quantumDoubleDualSpins_mul_colorDiag (c : G × G × G × G) (g : G) :
    quantumDoubleDualSpins (c * colorDiag G g) = quantumDoubleDualSpins c := by
  obtain ⟨t, r, b, l⟩ := c
  simp [quantumDoubleDualSpins, colorDiag, mul_inv_rev, mul_assoc]

/-- Two colorings have the same physical spins exactly when they differ by a global shift. -/
theorem quantumDoubleDualSpins_eq_iff (c c' : G × G × G × G) :
    quantumDoubleDualSpins c' = quantumDoubleDualSpins c ↔
      ∃ g : G, c' = c * colorDiag G g := by
  constructor
  · obtain ⟨t, r, b, l⟩ := c
    obtain ⟨t', r', b', l'⟩ := c'
    intro h
    simp only [quantumDoubleDualSpins, Prod.mk.injEq] at h
    obtain ⟨h1, h2, -, h4⟩ := h
    refine ⟨l⁻¹ * l', ?_⟩
    have ht : t' = t * (l⁻¹ * l') := by
      rw [← mul_assoc, ← h1]; group
    have hb : b' = b * (l⁻¹ * l') := by
      rw [← mul_assoc, ← h4]; group
    have hr : r' = r * (l⁻¹ * l') := by
      calc r' = r' * t'⁻¹ * t' := by group
        _ = r * t⁻¹ * (t * (l⁻¹ * l')) := by rw [h2, ← ht]
        _ = r * (l⁻¹ * l') := by group
    simp [colorDiag, ht, hr, hb]
  · rintro ⟨g, rfl⟩
    exact quantumDoubleDualSpins_mul_colorDiag c g

variable (G)

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2465: the regular
representation of `G` on the virtual level of the dual tensor, shifting all four plaquette
colors, `(ρ_g x)(c) = x(c g)`. On each leg this is the right-regular representation. -/
def colorShiftRep : Representation ℂ G ((G × G × G × G) → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ fun c => c * colorDiag G g
  map_one' := by
    refine LinearMap.ext fun x => funext fun c => ?_
    simp [LinearMap.funLeft]
  map_mul' g h := by
    refine LinearMap.ext fun x => funext fun c => ?_
    simp [colorDiag_mul, LinearMap.funLeft, mul_assoc]

variable {G}

theorem colorShiftRep_apply (g : G) (x : (G × G × G × G) → ℂ) (c : G × G × G × G) :
    colorShiftRep G g x c = x (c * colorDiag G g) := rfl

theorem mem_invariants_colorShiftRep_iff (x : (G × G × G × G) → ℂ) :
    x ∈ (colorShiftRep G).invariants ↔ ∀ c g, x (c * colorDiag G g) = x c := by
  simp only [Representation.mem_invariants, funext_iff, colorShiftRep_apply]
  exact forall_comm

variable (G) [DecidableEq G]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2460–2463. The
dual quantum-double tensor with virtual colors `t, r, b, l` on the top, right, down and left
legs: it is `1` at the physical configuration `quantumDoubleDualSpins (t, r, b, l)` of
differences of adjacent colors and `0` elsewhere. This is the tensor `K` of
arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 2906–2911, up to the orientation of the
differences. -/
def quantumDoubleDualTensor (t r b l : G) (s : G × G × G × G) : ℂ :=
  if s = quantumDoubleDualSpins (t, r, b, l) then 1 else 0

variable {G} [Fintype G]

theorem siteMap_quantumDoubleDualTensor_apply (x : (G × G × G × G) → ℂ)
    (s : G × G × G × G) :
    siteMap (quantumDoubleDualTensor G) x s =
      ∑ c : G × G × G × G, if s = quantumDoubleDualSpins c then x c else 0 := by
  rw [siteMap_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [quantumDoubleDualTensor]

/-- The value of the dual tensor's map at the spins of a coloring `c` is the sum of the
virtual vector over the global shifts of `c`. -/
theorem siteMap_quantumDoubleDualTensor_apply_spins (x : (G × G × G × G) → ℂ)
    (c : G × G × G × G) :
    siteMap (quantumDoubleDualTensor G) x (quantumDoubleDualSpins c) =
      ∑ g : G, x (c * colorDiag G g) := by
  rw [siteMap_quantumDoubleDualTensor_apply, ← Finset.sum_filter]
  symm
  refine Finset.sum_bij' (fun g _ => c * colorDiag G g) (fun c' _ => c.2.2.2⁻¹ * c'.2.2.2)
    ?_ ?_ ?_ ?_ ?_
  · intro g _
    simp
  · intro _ _
    exact Finset.mem_univ _
  · intro g _
    simp [colorDiag]
  · intro c' hc'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
    obtain ⟨g, rfl⟩ := (quantumDoubleDualSpins_eq_iff c c').1 hc'.symm
    simp [colorDiag]
  · intro _ _
    rfl

theorem siteMap_quantumDoubleDualTensor_apply_spins_of_mem_invariants
    {x : (G × G × G × G) → ℂ} (hx : x ∈ (colorShiftRep G).invariants) (c : G × G × G × G) :
    siteMap (quantumDoubleDualTensor G) x (quantumDoubleDualSpins c) =
      (Fintype.card G : ℂ) * x c := by
  rw [siteMap_quantumDoubleDualTensor_apply_spins]
  simp [(mem_invariants_colorShiftRep_iff x).1 hx c, Finset.card_univ]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2465: the dual
quantum-double tensor is `G`-injective with respect to the regular representation that
shifts all plaquette colors. -/
theorem isGInjective_quantumDoubleDualTensor :
    IsGInjective (colorShiftRep G) (siteMap (quantumDoubleDualTensor G)) where
  invariant g := by
    refine LinearMap.ext fun x => funext fun s => ?_
    simp only [LinearMap.comp_apply, siteMap_quantumDoubleDualTensor_apply,
      colorShiftRep_apply]
    rw [← Equiv.sum_comp (Equiv.mulRight (colorDiag G g))
      fun c => if s = quantumDoubleDualSpins c then x c else 0]
    simp
  injOn_invariants x hx hTx := by
    funext c
    have h := siteMap_quantumDoubleDualTensor_apply_spins_of_mem_invariants hx c
    rw [hTx] at h
    have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simpa [hG] using h.symm

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2465, and
arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 2904–2911: the dual quantum-double
tensor is `G`-isometric, `⟪𝒫 x, 𝒫 y⟫ = |G| ⟪x, y⟫` on color-shift invariant vectors. -/
theorem isGIsometric_quantumDoubleDualTensor :
    IsGIsometric (colorShiftRep G) (siteMap (quantumDoubleDualTensor G)) where
  toIsGInjective := isGInjective_quantumDoubleDualTensor
  exists_inner_eq := by
    refine ⟨Fintype.card G, by exact_mod_cast Fintype.card_pos, fun x hx y _ => ?_⟩
    simp only [dotProduct, siteMap_quantumDoubleDualTensor_apply (x := y), Finset.mul_sum,
      Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [mul_ite, mul_zero, Fintype.sum_ite_eq',
      siteMap_quantumDoubleDualTensor_apply_spins_of_mem_invariants hx, Complex.star_def,
      map_mul, Complex.conj_natCast, Complex.ofReal_natCast]
    ring

/-- The group `ℤ₂` of the toric code, written multiplicatively. -/
abbrev ToricCodeGroup : Type := Multiplicative (ZMod 2)

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2450–2465, and
arXiv:quant-ph/9707021, `References/quant-ph_9707021/source/anyons.tex` lines 189–226: the
dual PEPS tensor of the toric code, `G = ℤ₂`, is `ℤ₂`-isometric. -/
theorem isGIsometric_toricCodeDualTensor :
    IsGIsometric (colorShiftRep ToricCodeGroup)
      (siteMap (quantumDoubleDualTensor ToricCodeGroup)) :=
  isGIsometric_quantumDoubleDualTensor

end Dual

/-! ### The primal tensor -/

section Primal

variable (G : Type*) [Group G]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2451–2457 (figure
`fig_app_tc-primal`). The virtual labels `(g₁g₂, g₂⁻¹g₃, g₄g₃, g₁g₄⁻¹)` on the top, right,
down and left legs of the primal tensor with edge spins `(g₁, g₂, g₃, g₄)` (top left, top
right, bottom right, bottom left). -/
def quantumDoublePrimalLabels (g : G × G × G × G) : G × G × G × G :=
  (g.1 * g.2.1, g.2.1⁻¹ * g.2.2.1, g.2.2.2 * g.2.2.1, g.1 * g.2.2.2⁻¹)

variable [DecidableEq G]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2451–2457. The
primal quantum-double tensor: `1` when the virtual labels are those of the edge spins `g`,
and `0` otherwise. -/
def quantumDoublePrimalTensor (t r b l : G) (g : G × G × G × G) : ℂ :=
  if (t, r, b, l) = quantumDoublePrimalLabels G g then 1 else 0

variable {G}

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2465: on the
support of the primal tensor the four virtual labels fuse to the identity,
`t r b⁻¹ l⁻¹ = 1`. -/
theorem quantumDoublePrimalTensor_ne_zero_mul_eq_one {t r b l : G} {g : G × G × G × G}
    (h : quantumDoublePrimalTensor G t r b l g ≠ 0) : t * r * b⁻¹ * l⁻¹ = 1 := by
  obtain ⟨g₁, g₂, g₃, g₄⟩ := g
  simp only [quantumDoublePrimalTensor, quantumDoublePrimalLabels, ne_eq, ite_eq_right_iff,
    Prod.mk.injEq, one_ne_zero, imp_false, not_not] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  group

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2465: every
representation `π` of `G`, evaluated on the four virtual labels in the support of the primal
tensor, fuses to the identity, `π(t) π(r) π(b)⁻¹ π(l)⁻¹ = 1`. -/
theorem quantumDoublePrimalTensor_ne_zero_map_mul_eq_one {M : Type*} [Monoid M]
    (π : G →* M) {t r b l : G} {g : G × G × G × G}
    (h : quantumDoublePrimalTensor G t r b l g ≠ 0) :
    π t * π r * π b⁻¹ * π l⁻¹ = 1 := by
  rw [← map_mul, ← map_mul, ← map_mul, quantumDoublePrimalTensor_ne_zero_mul_eq_one h, map_one]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2465, for one
tensor. For every representation `π` of `G` by elements of a `ℂ`-algebra `M`, such as the
matrices of an irreducible representation, the primal tensor absorbs the virtual operator
`π(t) π(r) π(b)⁻¹ π(l)⁻¹` that acts by `π` on the top and right legs and by `π⁻¹` on the down
and left legs: each entry times this operator equals the same entry times the identity of `M`.
The matrix product operator symmetry of the contracted lattice is not stated (see the scope
restriction in the module docstring). -/
theorem quantumDoublePrimalTensor_smul_map_mul {M : Type*} [Ring M] [Algebra ℂ M]
    (π : G →* M) (t r b l : G) (g : G × G × G × G) :
    quantumDoublePrimalTensor G t r b l g • (π t * π r * π b⁻¹ * π l⁻¹) =
      quantumDoublePrimalTensor G t r b l g • (1 : M) := by
  by_cases h : quantumDoublePrimalTensor G t r b l g = 0
  · simp [h]
  · rw [quantumDoublePrimalTensor_ne_zero_map_mul_eq_one π h]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2465: the primal
tensor is invariant under the virtual action of every one-dimensional representation `χ`,
acting by `χ` on the top and right legs and by `χ⁻¹` on the down and left legs. -/
theorem character_mul_quantumDoublePrimalTensor (χ : G →* ℂˣ) (t r b l : G)
    (g : G × G × G × G) :
    ((χ t * χ r * (χ b)⁻¹ * (χ l)⁻¹ : ℂˣ) : ℂ) * quantumDoublePrimalTensor G t r b l g =
      quantumDoublePrimalTensor G t r b l g := by
  by_cases h : quantumDoublePrimalTensor G t r b l g = 0
  · rw [h, mul_zero]
  · rw [← map_inv, ← map_inv, quantumDoublePrimalTensor_ne_zero_map_mul_eq_one χ h,
      Units.val_one, one_mul]

end Primal

end PEPS
end TNLean
