/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusLatticeGraph
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.Tactic.Abel

/-!
# Oriented dual-lattice paths and flux-string crossing numbers

Plaquettes are labelled by their lower-left primal vertex. A dual step to the
right crosses the downward native bond to its right; an upward dual step
crosses the rightward native bond above it. Both contribute +1. Reversing a
step contributes -1. Multiplicities are retained, including repeated crossings
and the separately labelled bonds of small tori.

Source: SCP10, arXiv:1001.3807, Definition 6.13, equation
`eq:anyons:fluxon-def`, and Lemma 6.14, local source lines 2181–2214.
-/

namespace TNLean.PEPS

variable {width height : ℕ}

/-- Four oriented unit steps between dual plaquettes. The labels retain
parallel edges when a period is two. Source: SCP10, Definition 6.13. -/
inductive TorusDualStep : TorusVertex width height → TorusVertex width height → Type
  | east (x : ZMod width) (y : ZMod height) : TorusDualStep (x, y) (x + 1, y)
  | west (x : ZMod width) (y : ZMod height) : TorusDualStep (x + 1, y) (x, y)
  | north (x : ZMod width) (y : ZMod height) : TorusDualStep (x, y) (x, y + 1)
  | south (x : ZMod width) (y : ZMod height) : TorusDualStep (x, y + 1) (x, y)

/-- The directed square dual lattice. -/
@[instance_reducible]
def torusDualQuiver (width height : ℕ) : Quiver (TorusVertex width height) where
  Hom := TorusDualStep

/-- An actual finite sequence of adjacent dual plaquettes, with fixed endpoints. -/
abbrev TorusDualPath (a b : TorusVertex width height) :=
  @Quiver.Path _ (torusDualQuiver width height) a b

local instance : Quiver (TorusVertex width height) := torusDualQuiver width height

/-- Reversal of a directed dual step. -/
def TorusDualStep.reverse {a b : TorusVertex width height} :
    TorusDualStep a b → TorusDualStep b a
  | .east x y => .west x y
  | .west x y => .east x y
  | .north x y => .south x y
  | .south x y => .north x y

@[simp]
theorem TorusDualStep.reverse_reverse {a b : TorusVertex width height}
    (e : TorusDualStep a b) : e.reverse.reverse = e := by cases e <;> rfl

/-- Step reversal gives the standard involutive quiver reversal. -/
instance torusDualInvolutiveReverse : Quiver.HasInvolutiveReverse
    (TorusVertex width height) where
  reverse' := TorusDualStep.reverse
  inv' := TorusDualStep.reverse_reverse

/-- Integer point mass at a primal vertex or dual plaquette. -/
def torusPointMass (a q : TorusVertex width height) : ℤ := if q = a then 1 else 0

/-- Signed crossings of the native horizontal and downward vertical bonds. -/
def TorusDualStep.crossings {a b : TorusVertex width height} :
    TorusDualStep a b → (TorusVertex width height → ℤ) × (TorusVertex width height → ℤ)
  | .east x y => (0, torusPointMass (x + 1, y))
  | .west x y => (0, -torusPointMass (x + 1, y))
  | .north x y => (torusPointMass (x, y + 1), 0)
  | .south x y => (-torusPointMass (x, y + 1), 0)

/-- Reversing a crossing negates both native bond counts. -/
@[simp]
theorem TorusDualStep.crossings_reverse {a b : TorusVertex width height}
    (e : TorusDualStep a b) : e.reverse.crossings = -e.crossings := by
  cases e <;> simp [reverse, crossings]

/-- Add the signed crossings of all steps, retaining multiplicity. -/
def torusDualPathCrossings {a : TorusVertex width height} :
    {b : TorusVertex width height} → TorusDualPath a b →
      (TorusVertex width height → ℤ) × (TorusVertex width height → ℤ)
  | _, .nil => 0
  | _, .cons p e => (torusDualPathCrossings p) + e.crossings

@[simp]
theorem TorusDualPath.crossings_nil (a : TorusVertex width height) :
    torusDualPathCrossings (Quiver.Path.nil : TorusDualPath a a) = 0 := rfl

@[simp]
theorem TorusDualPath.crossings_cons {a b c : TorusVertex width height}
    (p : TorusDualPath a b) (e : TorusDualStep b c) :
    torusDualPathCrossings (p.cons e) = (torusDualPathCrossings p) + e.crossings := rfl

/-- Concatenation adds the crossing counts. -/
@[simp]
theorem TorusDualPath.crossings_comp {a b c : TorusVertex width height}
    (p : TorusDualPath a b) (q : TorusDualPath b c) :
    torusDualPathCrossings (p.comp q) =
      torusDualPathCrossings p + torusDualPathCrossings q := by
  induction q with
  | nil => simp
  | cons q e ih => simp [ih, add_assoc]

/-- Reversing an entire path negates its signed bond crossings. -/
@[simp]
theorem TorusDualPath.crossings_reverse {a b : TorusVertex width height}
    (p : TorusDualPath a b) :
    torusDualPathCrossings p.reverse = -torusDualPathCrossings p := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [Quiver.Path.reverse, crossings_comp, Quiver.Hom.toPath,
      crossings_cons, crossings_nil, zero_add, ih]
    change e.reverse.crossings + -torusDualPathCrossings p =
      -(torusDualPathCrossings p + e.crossings)
    rw [TorusDualStep.crossings_reverse]
    abel

/-- The oriented clockwise plaquette exponent in native bond conventions. -/
def torusFluxCurl (n : (TorusVertex width height → ℤ) ×
    (TorusVertex width height → ℤ)) (q : TorusVertex width height) : ℤ :=
  n.1 (q.1, q.2 + 1) + n.2 (q.1 + 1, q.2) - n.1 q - n.2 q

@[simp]
theorem torusFluxCurl_zero (q : TorusVertex width height) : torusFluxCurl 0 q = 0 := by
  simp [torusFluxCurl]

/-- Clockwise plaquette exponents add under superposition of crossing counts. -/
@[simp]
theorem torusFluxCurl_add (m n : (TorusVertex width height → ℤ) ×
    (TorusVertex width height → ℤ)) (q : TorusVertex width height) :
    torusFluxCurl (m + n) q = torusFluxCurl m q + torusFluxCurl n q := by
  simp only [torusFluxCurl, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  abel

/-- One crossed bond has opposite fluxes in precisely its two adjacent
plaquettes. This includes the cancellation when these plaquettes coincide. -/
theorem TorusDualStep.fluxCurl {a b : TorusVertex width height}
    (e : TorusDualStep a b) (q : TorusVertex width height) :
    torusFluxCurl e.crossings q = torusPointMass a q - torusPointMass b q := by
  rcases q with ⟨u, v⟩
  cases e <;>
    simp [torusFluxCurl, crossings, torusPointMass, Prod.mk.injEq] <;> omega

/-- All interior dual vertices cancel: the clockwise flux exponent is +1 at
the initial plaquette, -1 at the final plaquette, and zero elsewhere.
Source: SCP10, Definition 6.13 and Lemma 6.14. -/
theorem TorusDualPath.fluxCurl {a b : TorusVertex width height}
    (p : TorusDualPath a b) (q : TorusVertex width height) :
    torusFluxCurl (torusDualPathCrossings p) q = torusPointMass a q - torusPointMass b q := by
  induction p with
  | nil => simp
  | cons p e ih => rw [crossings_cons, torusFluxCurl_add, ih, e.fluxCurl]; omega

end TNLean.PEPS
