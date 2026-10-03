/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusOperatorString
import TNLean.PEPS.PairConjugacy

/-!
# Torus PEPS with group-valued closures

The vector with closures `(g,h)` is obtained by inserting `U_h` on each horizontal
bond crossing the horizontal seam and `U_g` on each vertical bond crossing the
vertical seam. Simultaneous conjugation of `g` and `h` gives the same vector when
the site tensor is invariant under the virtual group action.

Source: Schuch, Cirac, Pérez-García, arXiv:1001.3807, Definition 5.6,
equation `eq:2d:peps-with-ug-uh`, and Definition 5.8, `def:2d:pair-cc`,
lines 1515–1525 and 1560–1580 of `Papers/1001.3807/paper_v3.tex`.
The horizontal and vertical orientations are those of `TorusOperatorString`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable {G V Phys : Type*} [Group G] [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- A horizontal closure inserts `U_h` on every bond from the last column to
the first. Source: arXiv:1001.3807, equation `eq:2d:peps-with-ug-uh`. -/
def torusHorizontalClosure (U : G →* Matrix V V ℂ) (h : G)
    (v : TorusVertex width height) : Matrix V V ℂ :=
  if v.1 + 1 = 0 then U h else 1

/-- A vertical closure inserts `U_g` on every bond from the bottom row to the
top, along the downward orientation. Source: arXiv:1001.3807,
equation `eq:2d:peps-with-ug-uh`. -/
def torusVerticalClosure (U : G →* Matrix V V ℂ) (g : G)
    (v : TorusVertex width height) : Matrix V V ℂ :=
  if v.2 + 1 = 0 then U g else 1

/-- The torus PEPS vector with closures `(g,h)`, coefficient by coefficient.
Source: arXiv:1001.3807, Definition 5.6, equation `eq:2d:peps-with-ug-uh`.
The source uses a square lattice; this definition also allows rectangles. -/
def torusGClosure (U : G →* Matrix V V ℂ) (a : V → V → V → V → Phys → ℂ)
    (g h : G) (σ : TorusVertex width height → Phys) : ℂ :=
  torusBondNetwork (fun v c ↦ a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
    (torusHorizontalClosure U h) (torusVerticalClosure U g)

/-- A virtual symmetry conjugates all bond operators without changing the
contracted vector. This is the invariance argument after Definition 5.8 in
arXiv:1001.3807, lines 1575–1580. -/
theorem torusBondNetwork_conjugate (U : G →* Matrix V V ℂ)
    (a : V → V → V → V → Phys → ℂ)
    (ha : ∀ x, siteMap a ∘ₗ torusLegRep U x = siteMap a)
    (σ : TorusVertex width height → Phys) (x : G)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ) :
    torusBondNetwork (fun v c ↦ a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (fun v ↦ U x * Oh v * U x⁻¹) (fun v ↦ U x * Ov v * U x⁻¹) =
      torusBondNetwork (fun v c ↦ a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) Oh Ov := by
  rw [torusBondNetwork_gauge _ Oh Ov (fun _ ↦ U x) (fun _ ↦ U x⁻¹)]
  congr 1
  funext v
  exact vecMul_torusLegMatrix_of_comp_eq U a ha x (σ v)

/-- Simultaneously conjugate closures define the same torus PEPS vector.
Source: arXiv:1001.3807, Definition 5.8, lines 1575–1580. -/
theorem torusGClosure_conjugate (U : G →* Matrix V V ℂ)
    (a : V → V → V → V → Phys → ℂ)
    (ha : ∀ x, siteMap a ∘ₗ torusLegRep U x = siteMap a)
    (σ : TorusVertex width height → Phys) (x g h : G) :
    torusGClosure U a (x * g * x⁻¹) (x * h * x⁻¹) σ = torusGClosure U a g h σ := by
  unfold torusGClosure
  convert torusBondNetwork_conjugate U a ha σ x
    (torusHorizontalClosure U h) (torusVerticalClosure U g) using 1
  congr 1 <;> funext v
  all_goals simp [torusHorizontalClosure, torusVerticalClosure, mul_ite, ite_mul, ← map_mul]

/-- Equal pair-conjugacy classes give the same torus PEPS vector, as stated
after Definition 5.8 of arXiv:1001.3807. -/
theorem torusGClosure_eq_of_pairConjugacyClass_eq (U : G →* Matrix V V ℂ)
    (a : V → V → V → V → Phys → ℂ)
    (ha : ∀ x, siteMap a ∘ₗ torusLegRep U x = siteMap a)
    (σ : TorusVertex width height → Phys) {p q : G × G}
    (hpq : pairConjugacyClass G p = pairConjugacyClass G q) :
    torusGClosure U a p.1 p.2 σ = torusGClosure U a q.1 q.2 σ := by
  obtain ⟨x, h₁, h₂⟩ := (pairConjugacyClass_eq_iff p q).mp hpq
  rw [h₁, h₂, torusGClosure_conjugate U a ha]

/-- The torus vector indexed by a pair-conjugacy class. Its independence of the
representative is the assertion following Definition 5.8 of arXiv:1001.3807.
Only the virtual invariance clause of G-injectivity is needed. -/
def torusGClosureClass (U : G →* Matrix V V ℂ) (a : V → V → V → V → Phys → ℂ)
    (ha : ∀ x, siteMap a ∘ₗ torusLegRep U x = siteMap a)
    (C : PairConjugacyClass G) : (TorusVertex width height → Phys) → ℂ :=
  Quotient.lift (fun p : G × G ↦ torusGClosure U a p.1 p.2)
    (fun _ _ h ↦ funext fun σ ↦
      torusGClosure_eq_of_pairConjugacyClass_eq U a ha σ (Quotient.sound h)) C

@[simp]
theorem torusGClosureClass_pairConjugacyClass (U : G →* Matrix V V ℂ)
    (a : V → V → V → V → Phys → ℂ)
    (ha : ∀ x, siteMap a ∘ₗ torusLegRep U x = siteMap a) (p : G × G) :
    torusGClosureClass (width := width) (height := height) U a ha (pairConjugacyClass G p) =
      torusGClosure U a p.1 p.2 := rfl

end TNLean.PEPS
