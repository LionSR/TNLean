/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Basic.Complex.Basic

/-!
# Dual quantum-double tensor coordinates

The dual tensor records the four adjacent color differences for an arbitrary group.
The toric-code group is its binary instance; no torus geometry is needed here.
-/

namespace TNLean.PEPS

variable {G : Type*} [Group G]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2460–2463 (figure
`fig_app_tc-dual`). The four physical spins `(h₂h₁⁻¹, h₃h₂⁻¹, h₃h₄⁻¹, h₄h₁⁻¹)` of the dual
tensor, the differences of adjacent plaquette colors, for the colors `(t, r, b, l)` on the
top, right, down and left legs, that is `(h₂, h₃, h₄, h₁)`. -/
def quantumDoubleDualSpins (c : G × G × G × G) : G × G × G × G :=
  (c.1 * c.2.2.2⁻¹, c.2.1 * c.1⁻¹, c.2.1 * c.2.2.1⁻¹, c.2.2.1 * c.2.2.2⁻¹)

variable (G) [DecidableEq G]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2460–2463. The
dual quantum-double tensor with virtual colors `t, r, b, l` on the top, right, down and left
legs: it is `1` at the physical configuration `quantumDoubleDualSpins (t, r, b, l)` of
differences of adjacent colors and `0` elsewhere. This is the tensor `K` of
arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 2906–2911, up to the orientation of the
differences. -/
def quantumDoubleDualTensor (t r b l : G) (s : G × G × G × G) : ℂ :=
  if s = quantumDoubleDualSpins (t, r, b, l) then 1 else 0

/-- The group `ℤ₂` of the toric code, written multiplicatively. -/
abbrev ToricCodeGroup : Type := Multiplicative (ZMod 2)

end TNLean.PEPS
