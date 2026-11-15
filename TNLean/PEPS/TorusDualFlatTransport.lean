/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualHomotopy

/-!
# Completeness of restricted homotopy for locally flat transports

Reversible transports between arbitrary vertex fibres are required to agree
on the two sides of each allowed square. These local conditions do not refer
to a pair of paths. Two parallel paths are generated-homotopic exactly when
every such transport agrees on them. The separating transport is constructed
from path classes; no classification by displacement is asserted.

This is a semantic completeness result for the restricted-support reading of
SCP10, arXiv:1001.3807v3, Lemma 6.14, lines 2199–2214. It does not supply a
finite decision procedure or close the general noncentral density claim.
See `docs/paper-gaps/scp10_dual_flat_transport.tex`.
-/

namespace TNLean.PEPS

variable {width height : ℕ}
local notation "X" => TorusVertex width height
local instance flatTransportQuiver : Quiver X := torusDualQuiver width height

/-- Reversible fibre transports, flat on each square allowed by the swept
support. All conditions are local and independent of the compared paths.
Semantic classification for the restricted reading of SCP10, Lemma 6.14. -/
structure TorusDualFlatTransport (R : Set X) (Y : X → Type*) where
  step : {a b : X} → TorusDualStep a b → Y a → Y b
  reverse_step : ∀ {a b : X} (e : TorusDualStep a b) (z : Y a),
    step e.reverse (step e z) = z
  square : ∀ (x : ZMod width) (y : ZMod height), (x + 1, y + 1) ∈ R →
    ∀ z : Y (x, y),
      step (.north (x + 1) y) (step (.east x y) z) =
        step (.east x (y + 1)) (step (.north x y) z)

/-- Compose a locally flat transport along an actual labelled dual path.
Semantic classification for SCP10, Lemma 6.14. -/
def TorusDualFlatTransport.eval {R : Set X} {Y : X → Type*}
    (F : TorusDualFlatTransport R Y) {a : X} :
    {b : X} → TorusDualPath a b → Y a → Y b
  | _, .nil => id
  | _, .cons p e => fun z => F.step e (F.eval p z)

private theorem eval_comp {R : Set X} {Y : X → Type*}
    (F : TorusDualFlatTransport R Y) {a b c : X}
    (p : TorusDualPath a b) (q : TorusDualPath b c) (z : Y a) :
    F.eval (p.comp q) z = F.eval q (F.eval p z) := by
  induction q with
  | nil => rfl
  | cons q e ih => simp only [Quiver.Path.comp_cons, TorusDualFlatTransport.eval, ih]

private theorem eval_reverse_apply {R : Set X} {Y : X → Type*}
    (F : TorusDualFlatTransport R Y) {a b : X}
    (p : TorusDualPath a b) (z : Y a) : F.eval p.reverse (F.eval p z) = z := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Quiver.Path.reverse, eval_comp, Quiver.Hom.toPath,
      TorusDualFlatTransport.eval, id_eq]
    change F.eval p.reverse (F.step e.reverse (F.step e (F.eval p z))) = z
    rw [F.reverse_step, ih]

private theorem eval_apply_reverse {R : Set X} {Y : X → Type*}
    (F : TorusDualFlatTransport R Y) {a b : X}
    (p : TorusDualPath a b) (z : Y b) : F.eval p (F.eval p.reverse z) = z := by
  simpa only [Quiver.Path.reverse_reverse] using eval_reverse_apply F p.reverse z

/-- Every generated supported homotopy preserves every locally flat transport.
The transport is constrained only by reversal and allowed elementary squares.
Semantic classification for the restricted reading of SCP10, Lemma 6.14. -/
theorem TorusDualHomotopy.flatTransport_eval_eq {R : Set X} {a b : X}
    {p q : TorusDualPath a b} (h : TorusDualHomotopy R p q)
    {Y : X → Type*} (F : TorusDualFlatTransport R Y) (z : Y a) :
    F.eval p z = F.eval q z := by
  induction h with
  | refl p => rfl
  | symm h ih => exact (ih z).symm
  | trans h k ih ik => exact (ih z).trans (ik z)
  | comp h k ih ik => simp only [eval_comp, ih, ik]
  | @reverse a b p q h ih =>
    have hinj : Function.Injective (F.eval q) :=
      (show Function.LeftInverse (F.eval q.reverse) (F.eval q) from
        fun w => eval_reverse_apply F q w).injective
    apply hinj
    calc
      F.eval q (F.eval p.reverse z) = F.eval p (F.eval p.reverse z) := (ih _).symm
      _ = z := eval_apply_reverse F p z
      _ = F.eval q (F.eval q.reverse z) := (eval_apply_reverse F q z).symm
  | backtrack e => exact F.reverse_step e z
  | square x y hxy => exact F.square x y hxy z

private def pathClassSetoid (R : Set X) (a b : X) : Setoid (TorusDualPath a b) where
  r := TorusDualHomotopy R
  iseqv := ⟨fun p => .refl p, fun h => .symm h, fun h k => .trans h k⟩

private abbrev PathClass (R : Set X) (a b : X) := Quotient (pathClassSetoid R a b)

private def appendClass {R : Set X} {a b c : X} (e : TorusDualStep b c) :
    PathClass R a b → PathClass R a c :=
  Quotient.lift (fun p => Quotient.mk _ (p.cons e))
    (fun _ _ h => Quotient.sound (h.comp (.refl (Quiver.Hom.toPath e))))

private def classTransport (R : Set X) (a : X) :
    TorusDualFlatTransport R (PathClass R a) where
  step := appendClass
  reverse_step := by
    intro b c e z
    induction z using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      exact (TorusDualHomotopy.refl p).comp (.backtrack e)
  square := by
    intro x y hxy z
    induction z using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      exact (TorusDualHomotopy.refl p).comp (.square x y hxy)

private theorem classTransport_eval (R : Set X) {a b c : X}
    (p : TorusDualPath b c) (r : TorusDualPath a b) :
    (classTransport R a).eval p (Quotient.mk _ r) = Quotient.mk _ (r.comp p) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [TorusDualFlatTransport.eval, ih]
    rfl

/-- Positive restricted-support completeness: equality under every reversible
transport flat on the allowed squares is equivalent to generated homotopy.
The quantified fibres live in the base universe `Type`, whereas the transport
structure and its homotopy-invariance theorem are universe-polymorphic. This is
not a finite family, a displacement criterion, or an assumed homotopy witness. No period
size assumptions are needed. Semantic refinement of SCP10, Lemma 6.14. -/
theorem torusDualHomotopy_iff_flatTransport {R : Set X} {a b : X}
    (p q : TorusDualPath a b) :
    TorusDualHomotopy R p q ↔
      ∀ (Y : X → Type) (F : TorusDualFlatTransport R Y) (z : Y a),
        F.eval p z = F.eval q z := by
  constructor
  · intro h Y F z
    exact h.flatTransport_eval_eq F z
  · intro h
    have he := h (PathClass R a) (classTransport R a) (Quotient.mk _ .nil)
    rw [classTransport_eval, classTransport_eval, Quiver.Path.nil_comp,
      Quiver.Path.nil_comp] at he
    exact Quotient.exact he

end TNLean.PEPS
