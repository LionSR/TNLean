/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.QuantumDoublePlaquetteConstraint

/-!
# Coherent color changes on the full periodic quantum-double lattice

SCP10, arXiv:1001.3807v3, Section 7.2, equation (7.10) and source lines
2918–2923. Every physical site retains the full four-spin alphabet. A group
label on each native torus bond acts by left and right multiplication on
its adjacent physical spins. The local and hole holonomies transform by
conjugation. Distinct bond actions commute even for a nonabelian group.
The native simple torus has both periods at least three.

**Scope restriction (native simple torus):** Both periods are at least three.
See `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "E" => Edge (torusGraph width height)
variable {G : Type*} [Group G]

/-- The full ambient physical alphabet of the periodic blocked model. -/
abbrev QuantumDoubleKLatticeConfig (width height : ℕ) (G : Type*) :=
  TorusVertex width height → G × G × G × G

/-- Simultaneous changes of all native bond colors. Each corner spin is
multiplied by its first bond label on the left and the inverse second label
on the right, exactly as in SCP10 equation (7.10). -/
def quantumDoubleKLatticeGauge (u : E → G) (x : QuantumDoubleKLatticeConfig width height G) :
    QuantumDoubleKLatticeConfig width height G := fun v =>
  (u (torusUpEdge v) * (x v).1 * (u (torusRightEdge v))⁻¹,
    u (torusRightEdge v) * (x v).2.1 * (u (torusDownEdge v))⁻¹,
    u (torusDownEdge v) * (x v).2.2.1 * (u (torusLeftEdge v))⁻¹,
    u (torusLeftEdge v) * (x v).2.2.2 * (u (torusUpEdge v))⁻¹)

@[simp]
theorem quantumDoubleKLatticeGauge_one (x : QuantumDoubleKLatticeConfig width height G) :
    quantumDoubleKLatticeGauge 1 x = x := by
  funext v
  simp [quantumDoubleKLatticeGauge]

theorem quantumDoubleKLatticeGauge_mul (u w : E → G)
    (x : QuantumDoubleKLatticeConfig width height G) :
    quantumDoubleKLatticeGauge (u * w) x =
      quantumDoubleKLatticeGauge u (quantumDoubleKLatticeGauge w x) := by
  funext v
  simp [quantumDoubleKLatticeGauge, mul_inv_rev, mul_assoc]

/-- Bond color changes form a genuine permutation representation. -/
def quantumDoubleKLatticeGaugePermutation : (E → G) →*
    Equiv.Perm (QuantumDoubleKLatticeConfig width height G) where
  toFun u :=
    { toFun := quantumDoubleKLatticeGauge u
      invFun := quantumDoubleKLatticeGauge u⁻¹
      left_inv x := by rw [← quantumDoubleKLatticeGauge_mul, inv_mul_cancel]; simp
      right_inv x := by rw [← quantumDoubleKLatticeGauge_mul, mul_inv_cancel]; simp }
  map_one' := by apply Equiv.ext; exact quantumDoubleKLatticeGauge_one
  map_mul' u w := by apply Equiv.ext; exact quantumDoubleKLatticeGauge_mul u w

/-- The full-lattice placement of one coherent bond action, including bonds
crossing either periodic seam. -/
def quantumDoubleKLatticeBondPermutation (e : E) : G →*
    Equiv.Perm (QuantumDoubleKLatticeConfig width height G) :=
  quantumDoubleKLatticeGaugePermutation.comp (MonoidHom.mulSingle (fun _ : E => G) e)

/-- Different bonds commute on every physical configuration. No local or
plaquette product-one constraint is used. -/
theorem quantumDoubleKLatticeBondPermutation_commute {e f : E} (hef : e ≠ f) (u w : G) :
    Commute (quantumDoubleKLatticeBondPermutation e u)
      (quantumDoubleKLatticeBondPermutation f w) :=
  (show Commute (Pi.mulSingle e u : E → G) (Pi.mulSingle f w) from
    Pi.mulSingle_commute (f := fun _ : E => G) hef u w).map quantumDoubleKLatticeGaugePermutation

/-- The right-edge action restricts to the previously proved left-block action. -/
theorem quantumDoubleKLatticeBondPermutation_right_at_left (u : G)
    (x : QuantumDoubleKLatticeConfig width height G) (v : X) :
    quantumDoubleKLatticeBondPermutation (torusRightEdge v) u x v =
      quantumDoubleKBondLeft u (x v) := by
  have hv : (v.1 - 1, v.2) ≠ v := by
    intro h
    have hh := congrArg Prod.fst h
    have hn : (1 : ZMod width) ≠ 0 := one_ne_zero
    apply hn
    exact sub_eq_self.mp hh
  simp [quantumDoubleKLatticeBondPermutation, quantumDoubleKLatticeGaugePermutation,
    quantumDoubleKLatticeGauge, quantumDoubleKBondLeft,
    torusDownEdge, torusLeftEdge,
    Ne.symm (torusRightEdge_ne_torusUpEdge _ _), torusRightEdge_injective.eq_iff, hv]

/-- The same shared right-edge label acts on the adjacent right block. -/
theorem quantumDoubleKLatticeBondPermutation_right_at_right (u : G)
    (x : QuantumDoubleKLatticeConfig width height G) (v : X) :
    quantumDoubleKLatticeBondPermutation (torusRightEdge v) u x (v.1 + 1, v.2) =
      quantumDoubleKBondRight u (x (v.1 + 1, v.2)) := by
  have hv : (v.1 + 1, v.2) ≠ v := by
    intro h
    have hh := congrArg Prod.fst h
    exact one_ne_zero (add_left_cancel (hh.trans (add_zero _).symm))
  simp [quantumDoubleKLatticeBondPermutation, quantumDoubleKLatticeGaugePermutation,
    quantumDoubleKLatticeGauge, quantumDoubleKBondRight, Pi.mulSingle_apply,
    torusDownEdge, torusLeftEdge,
    Ne.symm (torusRightEdge_ne_torusUpEdge _ _), torusRightEdge_injective.eq_iff, hv]

/-- An up-edge color change acts on the north-facing corners of its lower block. -/
theorem quantumDoubleKLatticeBondPermutation_up_at_bottom (u : G)
    (x : QuantumDoubleKLatticeConfig width height G) (v : X) :
    quantumDoubleKLatticeBondPermutation (torusUpEdge v) u x v =
      (u * (x v).1, (x v).2.1, (x v).2.2.1, (x v).2.2.2 * u⁻¹) := by
  have hv : (v.1, v.2 - 1) ≠ v := by
    intro h
    exact one_ne_zero (sub_eq_self.mp (congrArg Prod.snd h))
  simp [quantumDoubleKLatticeBondPermutation, quantumDoubleKLatticeGaugePermutation,
    quantumDoubleKLatticeGauge, torusDownEdge, torusLeftEdge,
    torusRightEdge_ne_torusUpEdge, torusUpEdge_injective.eq_iff, hv]

/-- The same up-edge color change acts on the south-facing corners of its upper block. -/
theorem quantumDoubleKLatticeBondPermutation_up_at_top (u : G)
    (x : QuantumDoubleKLatticeConfig width height G) (v : X) :
    quantumDoubleKLatticeBondPermutation (torusUpEdge v) u x (v.1, v.2 + 1) =
      ((x (v.1, v.2 + 1)).1, (x (v.1, v.2 + 1)).2.1 * u⁻¹,
        u * (x (v.1, v.2 + 1)).2.2.1, (x (v.1, v.2 + 1)).2.2.2) := by
  have hv : (v.1, v.2 + 1) ≠ v := by
    intro h
    exact one_ne_zero (add_left_cancel ((congrArg Prod.snd h).trans (add_zero _).symm))
  simp [quantumDoubleKLatticeBondPermutation, quantumDoubleKLatticeGaugePermutation,
    quantumDoubleKLatticeGauge, Pi.mulSingle_apply, torusDownEdge, torusLeftEdge,
    torusRightEdge_ne_torusUpEdge, torusUpEdge_injective.eq_iff, hv]

/-- A bond which is not incident to a site leaves all four of its spins fixed. -/
theorem quantumDoubleKLatticeBondPermutation_spectator (e : E) (u : G)
    (x : QuantumDoubleKLatticeConfig width height G) (v : X)
    (hn : torusUpEdge v ≠ e) (he : torusRightEdge v ≠ e)
    (hs : torusDownEdge v ≠ e) (hw : torusLeftEdge v ≠ e) :
    quantumDoubleKLatticeBondPermutation e u x v = x v := by
  simp [quantumDoubleKLatticeBondPermutation, quantumDoubleKLatticeGaugePermutation,
    quantumDoubleKLatticeGauge, hn, he, hs, hw]

/-- The ordered product around a full-lattice hole, with lower-left corner
`v`, using the same clockwise order as the four-block calculation. -/
def quantumDoubleKLatticePlaquetteHolonomy
    (x : QuantumDoubleKLatticeConfig width height G) (v : X) : G :=
  (x (v.1, v.2 + 1)).2.1 * (x v).1 *
    (x (v.1 + 1, v.2)).2.2.2 * (x (v.1 + 1, v.2 + 1)).2.2.1

/-- Every local holonomy transforms by conjugation by its north bond label. -/
theorem quantumDoubleKHolonomy_latticeGauge (u : E → G)
    (x : QuantumDoubleKLatticeConfig width height G) (v : X) :
    quantumDoubleKHolonomy (quantumDoubleKLatticeGauge u x v) =
      u (torusUpEdge v) * quantumDoubleKHolonomy (x v) * (u (torusUpEdge v))⁻¹ := by
  simp [quantumDoubleKHolonomy, quantumDoubleKLatticeGauge, mul_assoc]

/-- Every hole holonomy transforms by conjugation by its top horizontal
bond label. The statement includes plaquettes crossing the periodic seams. -/
theorem quantumDoubleKLatticePlaquetteHolonomy_gauge (u : E → G)
    (x : QuantumDoubleKLatticeConfig width height G) (v : X) :
    quantumDoubleKLatticePlaquetteHolonomy (quantumDoubleKLatticeGauge u x) v =
      u (torusRightEdge (v.1, v.2 + 1)) * quantumDoubleKLatticePlaquetteHolonomy x v *
        (u (torusRightEdge (v.1, v.2 + 1)))⁻¹ := by
  simp [quantumDoubleKLatticePlaquetteHolonomy, quantumDoubleKLatticeGauge,
    torusDownEdge, torusLeftEdge, mul_assoc]

/-- Product-one is preserved by conjugation; holonomy itself need not be. -/
theorem quantumDoubleKHolonomy_latticeGauge_eq_one_iff (u : E → G)
    (x : QuantumDoubleKLatticeConfig width height G) (v : X) :
    quantumDoubleKHolonomy (quantumDoubleKLatticeGauge u x v) = 1 ↔
      quantumDoubleKHolonomy (x v) = 1 := by
  rw [quantumDoubleKHolonomy_latticeGauge]
  simp [mul_eq_one_iff_eq_inv]

/-- The physical hole constraint is invariant under all bond color changes. -/
theorem quantumDoubleKLatticePlaquetteHolonomy_gauge_eq_one_iff (u : E → G)
    (x : QuantumDoubleKLatticeConfig width height G) (v : X) :
    quantumDoubleKLatticePlaquetteHolonomy (quantumDoubleKLatticeGauge u x) v = 1 ↔
      quantumDoubleKLatticePlaquetteHolonomy x v = 1 := by
  rw [quantumDoubleKLatticePlaquetteHolonomy_gauge]
  simp [mul_eq_one_iff_eq_inv]

/-- A coloring of the actual native torus edges produces the four physical
spins of K at every lattice site. -/
def quantumDoubleKLatticeSpins (c : E → G) : QuantumDoubleKLatticeConfig width height G :=
  fun v => quantumDoubleKSpins
    (c (torusUpEdge v), c (torusRightEdge v), c (torusDownEdge v), c (torusLeftEdge v))

/-- The physical gauge action is induced by actual multiplication of each
shared virtual bond color, rather than stipulated invariance of a state. -/
theorem quantumDoubleKLatticeSpins_mul (u c : E → G) :
    quantumDoubleKLatticeSpins (u * c) =
      quantumDoubleKLatticeGauge u (quantumDoubleKLatticeSpins c) := by
  funext v
  simp [quantumDoubleKLatticeSpins, quantumDoubleKSpins, quantumDoubleKLatticeGauge,
    mul_inv_rev, mul_assoc]

@[simp]
theorem quantumDoubleKHolonomy_latticeSpins (c : E → G) (v : X) :
    quantumDoubleKHolonomy (quantumDoubleKLatticeSpins c v) = 1 :=
  quantumDoubleKHolonomy_spins _

@[simp]
theorem quantumDoubleKLatticePlaquetteHolonomy_spins (c : E → G) (v : X) :
    quantumDoubleKLatticePlaquetteHolonomy (quantumDoubleKLatticeSpins c) v = 1 := by
  simp [quantumDoubleKLatticePlaquetteHolonomy, quantumDoubleKLatticeSpins,
    quantumDoubleKSpins, torusDownEdge, torusLeftEdge, mul_assoc]

end TNLean.PEPS
