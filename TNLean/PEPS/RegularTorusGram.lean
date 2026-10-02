/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FiniteIndicatorSum
import TNLean.PEPS.RegularTorusGramExpansion
import TNLean.PEPS.RegularTorusSite
import TNLean.PEPS.RegularTorusBondCounting

/-!
# Overlaps of actual regular torus closure states

The overlap is obtained from the literal site Gram kernels of the torus network.
Their normalized regular-group averages produce one translation at each vertex.
Every compatible bond has one independent group label; the two bond families
supply two factors of the group order per site. Compatibility across the seams
then reduces all vertex translations to one simultaneous closure intertwiner.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, equation
`eq:2d:peps-with-ug-uh`, lines 1515–1525, Definition 6.1, lines 1692–1702,
and the pair-conjugacy argument in lines 1560–1580. These contraction identities
do not assume that either closure pair commutes. Parent-Hamiltonian membership
is a separate assertion.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {width height : ℕ} [NeZero width] [NeZero height]
variable {Phys : Type*} [Fintype Phys]

/-- The product of the local regular Gram kernels is the sum over one group
translation per torus vertex, with the local normalization factors retained.
Source: SCP10, Definition 6.1 and equation `eq:2d:peps-with-ug-uh`. -/
theorem prod_torusSiteGram_eq_sum_translation
    (a : TorusVertex width height → (G × G × G × G) → Phys → ℂ)
    (c : TorusVertex width height → ℂ)
    (hlocal : ∀ v η θ, (∑ s : Phys, star (a v η s) * a v θ s) =
      (c v / (Fintype.card G : ℂ)) * ∑ g : G, if η = g • θ then (1 : ℂ) else 0)
    (η θ : TorusVertex width height → G × G × G × G) :
    (∏ v, ∑ s : Phys, star (a v (η v) s) * a v (θ v) s) =
      ((∏ v, c v) / (Fintype.card G : ℂ) ^ Fintype.card (TorusVertex width height)) *
        ∑ q : TorusVertex width height → G,
          if ∀ v, η v = q v • θ v then (1 : ℂ) else 0 := by
  classical
  simp only [hlocal, Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ]
  congr 1
  exact Fintype.prod_sum_boole _

private theorem sum_last_first_five {I J : Type*} [Fintype I] [Fintype J]
    (f : I → I → I → I → J → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ q, f a b c d q) =
      ∑ q, ∑ a, ∑ b, ∑ c, ∑ d, f a b c d q := by
  have h : (∑ p : ((I × I) × I) × I, ∑ q : J, f p.1.1.1 p.1.1.2 p.1.2 p.2 q) =
      ∑ q : J, ∑ p : ((I × I) × I) × I, f p.1.1.1 p.1.1.2 p.1.2 p.2 q :=
    Finset.sum_comm
  simpa only [Fintype.sum_prod_type] using h

/-- Source: SCP10, equation `eq:2d:peps-with-ug-uh` and Definition 6.1.
The overlap of the actual torus networks with regular closures is determined by
the simultaneous intertwiners of the two closure pairs. Every local Gram kernel
is supplied at one site; no identity for the contracted network is assumed. -/
theorem sum_star_torusBondNetwork_regularClosure_mul
    (a : TorusVertex width height → (G × G × G × G) → Phys → ℂ)
    (c : TorusVertex width height → ℂ)
    (hlocal : ∀ v η θ, (∑ s : Phys, star (a v η s) * a v θ s) =
      (c v / (Fintype.card G : ℂ)) * ∑ z : G, if η = z • θ then (1 : ℂ) else 0)
    (g h g' h' : G) :
    (∑ σ : TorusVertex width height → Phys,
      star (torusBondNetwork (fun v η => a v η (σ v))
        (torusHorizontalClosure (leftRegularMatrix G) h)
        (torusVerticalClosure (leftRegularMatrix G) g)) *
      torusBondNetwork (fun v η => a v η (σ v))
        (torusHorizontalClosure (leftRegularMatrix G) h')
        (torusVerticalClosure (leftRegularMatrix G) g')) =
      (∏ v, c v) * (Fintype.card G : ℂ) ^ Fintype.card (TorusVertex width height) *
        ∑ x : G, if h * x = x * h' ∧ g * x = x * g' then (1 : ℂ) else 0 := by
  classical
  have hH (k : G) : torusHorizontalClosure (leftRegularMatrix G) k =
      fun (v : TorusVertex width height) => Matrix.permMatrixHom (R := ℂ)
        (MulAction.toPermHom G G (torusHorizontalClosureElement k v)) := by
    funext v
    rw [torusHorizontalClosure_eq_map_element]
    rfl
  have hV (k : G) : torusVerticalClosure (leftRegularMatrix G) k =
      fun (v : TorusVertex width height) => Matrix.permMatrixHom (R := ℂ)
        (MulAction.toPermHom G G (torusVerticalClosureElement k v)) := by
    funext v
    rw [torusVerticalClosure_eq_map_element]
    rfl
  rw [hH, hV, hH, hV, sum_star_torusBondNetwork_perm_mul]
  simp only [prod_torusSiteGram_eq_sum_translation a c hlocal, ← Finset.mul_sum]
  rw [sum_last_first_five]
  change ((∏ v, c v) / (Fintype.card G : ℂ) ^ Fintype.card (TorusVertex width height)) *
    (∑ q : TorusVertex width height → G,
      ∑ ηh : TorusVertex width height → G, ∑ ηv : TorusVertex width height → G,
        ∑ θh : TorusVertex width height → G, ∑ θv : TorusVertex width height → G,
          if ∀ v, torusRegularSiteLabels (torusHorizontalClosureElement h)
            (torusVerticalClosureElement g) ηh ηv v =
              q v • torusRegularSiteLabels (torusHorizontalClosureElement h')
                (torusVerticalClosureElement g') θh θv v then (1 : ℂ) else 0) = _
  simp only [sum_torusClosureSiteLabels_translation_eq_card]
  have hif (q : TorusVertex width height → G) :
      (if IsTorusClosureCompatible g h g' h' q then
        (Fintype.card G : ℂ) ^ (2 * Fintype.card (TorusVertex width height)) else 0) =
      (Fintype.card G : ℂ) ^ (2 * Fintype.card (TorusVertex width height)) *
        (if IsTorusClosureCompatible g h g' h' q then (1 : ℂ) else 0) := by
    split_ifs <;> simp
  simp only [hif, ← Finset.mul_sum]
  rw [sum_torusClosureCompatible_eq_sum_intertwiner]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [two_mul, pow_add]
  simp only [div_eq_mul_inv, mul_assoc]
  field_simp

/-- Source: SCP10, equation `eq:2d:peps-with-ug-uh` and Definition 6.1.
For one tensor repeated over the torus, the actual closure overlap is its site
Gram scalar to the number of sites, times the regular-bond count and the
number of simultaneous closure intertwiners. -/
theorem sum_star_torusGClosure_regular_mul
    (a : G → G → G → G → Phys → ℂ) (c : ℂ)
    (hlocal : ∀ η θ : G × G × G × G,
      (∑ s : Phys, star (a η.1 η.2.1 η.2.2.1 η.2.2.2 s) *
        a θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 s) =
        (c / (Fintype.card G : ℂ)) * ∑ z : G, if η = z • θ then (1 : ℂ) else 0)
    (g h g' h' : G) :
    (∑ σ : TorusVertex width height → Phys,
      star (torusGClosure (leftRegularMatrix G) a g h σ) *
        torusGClosure (leftRegularMatrix G) a g' h' σ) =
      c ^ Fintype.card (TorusVertex width height) *
        (Fintype.card G : ℂ) ^ Fintype.card (TorusVertex width height) *
          ∑ x : G, if h * x = x * h' ∧ g * x = x * g' then (1 : ℂ) else 0 := by
  simpa only [torusGClosure, Finset.prod_const, Finset.card_univ] using
    sum_star_torusBondNetwork_regularClosure_mul
      (fun _ η s => a η.1 η.2.1 η.2.2.1 η.2.2.2 s) (fun _ => c)
      (fun _ η θ => hlocal η θ) g h g' h'

/-- Source: SCP10, Definition 6.1 and equation `eq:2d:peps-with-ug-uh`.
Actual regular G-isometric torus closure vectors have the explicit overlap
kernel of simultaneous closure intertwiners, with a positive site scalar
provided by the existing isometry predicate. No Gram identity for the torus
network is assumed. -/
theorem IsGIsometric.exists_torusGClosure_overlap
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) :
    ∃ c : ℝ, 0 < c ∧ ∀ g h g' h' : G,
      (∑ σ : TorusVertex width height → Phys,
        star (torusGClosure (leftRegularMatrix G) a g h σ) *
          torusGClosure (leftRegularMatrix G) a g' h' σ) =
        (c : ℂ) ^ Fintype.card (TorusVertex width height) *
          (Fintype.card G : ℂ) ^ Fintype.card (TorusVertex width height) *
            ∑ x : G, if h * x = x * h' ∧ g * x = x * g' then (1 : ℂ) else 0 := by
  obtain ⟨c, hc, hlocal⟩ := ha.exists_torusRegularSiteGram
  exact ⟨c, hc, sum_star_torusGClosure_regular_mul a (c : ℂ) hlocal⟩

end TNLean.PEPS


