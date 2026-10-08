/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusTwoByTwoBlocking
import TNLean.PEPS.RegularTorusGramExpansion
import TNLean.PEPS.TorusGClosure
import TNLean.PEPS.RegularTorusSite

/-!
# Exact two-by-two blocking of regular torus closures

The native torus contraction is regrouped with its inserted seams intact.
A horizontal insertion acts at the head, on the receiving site's left leg;
a vertical insertion acts at the head, on the site's top leg. Both labels
of a paired coarse bond therefore carry the same original permutation.
Internal bonds carry identities. All positive coarse periods are allowed.

Source: SCP10, arXiv:1001.3807, Definition 5.6, lines 1515–1525, and
Observation 6.6, lines 1888–1915. This is the geometric reblocking step;
no local or global factorization hypothesis is assumed.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable {X P : Type*}
local notation "TV" => TorusVertex width height
local notation "FV" => TorusVertex (width * 2) (height * 2)

/-- Lift a coarse horizontal permutation to both actual crossing fine bonds,
leaving the two internal horizontal bonds unchanged.
Source: SCP10, two-by-two blocking diagram, lines 1888–1906. -/
def twoByTwoHorizontalPerm (s : TV → Equiv.Perm X) (v : FV) : Equiv.Perm X :=
  let p := (kitaevPeriodicTilingEquiv (width := width) (height := height)).symm v
  ![s p.1, s p.1, Equiv.refl X, Equiv.refl X] p.2

/-- Lift a coarse vertical permutation to both actual crossing fine bonds,
leaving the two internal vertical bonds unchanged.
Source: SCP10, two-by-two blocking diagram, lines 1888–1906. -/
def twoByTwoVerticalPerm (s : TV → Equiv.Perm X) (v : FV) : Equiv.Perm X :=
  let p := (kitaevPeriodicTilingEquiv (width := width) (height := height)).symm v
  ![s p.1, Equiv.refl X, Equiv.refl X, s p.1] p.2

/-- The four paired boundary legs with the coarse permutations inserted at
exactly the heads prescribed by the native bond convention.
Source: SCP10, Definition 5.6 and two-by-two blocking diagram. -/
def twoByTwoPermutationBoundary (sh sv : TV → Equiv.Perm X)
    (hb vb : TV → X × X) (v : TV) : Fin 4 → X × X :=
  ![((sv v).prodCongr (sv v)) (vb v), hb v, vb (v.1, v.2 - 1),
    ((sh (v.1 - 1, v.2)).prodCongr (sh (v.1 - 1, v.2))) (hb (v.1 - 1, v.2))]

/-- In tile coordinates the inserted boundary matches all fine endpoints,
including the two different orientations of horizontal and vertical bonds.
Source: SCP10, Definition 5.6 and two-by-two blocking diagram. -/
theorem twoByTwoSiteLegs_permutation
    (sh sv : TV → Equiv.Perm X)
    (p : ((TV → X × X) × (TV → X × X)) × (TV → Fin 4 → X))
    (v : TV × Fin 4) :
    twoByTwoSiteLegs (twoByTwoPermutationBoundary sh sv p.1.1 p.1.2 v.1)
        (p.2 v.1) v.2 =
      ![twoByTwoVerticalPerm sv (kitaevPeriodicTilingEquiv v)
          ((twoByTwoTiledBondEquiv p).2 v),
        (twoByTwoTiledBondEquiv p).1 v,
        (twoByTwoTiledBondEquiv p).2 (kitaevTiledDown v),
        twoByTwoHorizontalPerm sh (kitaevPeriodicTilingEquiv (kitaevTiledLeft v))
          ((twoByTwoTiledBondEquiv p).1 (kitaevTiledLeft v))] := by
  rcases v with ⟨v, i⟩
  simp only [twoByTwoHorizontalPerm, twoByTwoVerticalPerm, Equiv.symm_apply_apply]
  fin_cases i <;> rfl

/-- Reindex the native inserted fine network by the actual disjoint tiles.
The sum still contains exactly one index for every fine bond.
Source: SCP10, Definition 5.6 and Observation 6.6. -/
theorem torusBondNetwork_perm_eq_twoByTwoTiledSum [Fintype X] [DecidableEq X]
    (a : FV → (Fin 4 → X) → P → ℂ) (sh sv : TV → Equiv.Perm X) (σ : FV → P) :
    torusBondNetwork (fun v c => a v ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v))
        (fun v => Matrix.permMatrixHom (R := ℂ) (twoByTwoHorizontalPerm sh v))
        (fun v => Matrix.permMatrixHom (R := ℂ) (twoByTwoVerticalPerm sv v)) =
      ∑ q : (TV × Fin 4 → X) × (TV × Fin 4 → X),
        ∏ p : TV × Fin 4, a (kitaevPeriodicTilingEquiv p)
          ![twoByTwoVerticalPerm sv (kitaevPeriodicTilingEquiv p) (q.2 p), q.1 p,
            q.2 (kitaevTiledDown p),
            twoByTwoHorizontalPerm sh (kitaevPeriodicTilingEquiv (kitaevTiledLeft p))
              (q.1 (kitaevTiledLeft p))] (σ (kitaevPeriodicTilingEquiv p)) := by
  let E := kitaevPeriodicTilingEquiv (width := width) (height := height)
  let C := E.arrowCongr (Equiv.refl X)
  rw [torusBondNetwork_perm, ← Fintype.sum_prod_type', ← (C.prodCongr C).sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  rw [← E.prod_comp]
  apply Finset.prod_congr rfl
  intro p _
  simp [C, E, Equiv.arrowCongr_apply, torusPermutationSiteLabels,
    ← kitaevPeriodicTilingEquiv_down, ← kitaevPeriodicTilingEquiv_left]

/-- Exact geometric regrouping for arbitrary crossing permutation operators.
There are no graph-simplicity, symmetry, or state-factorization premises.
Source: SCP10, geometric step of Observation 6.6, lines 1888–1906. -/
theorem torusBondNetwork_perm_eq_twoByTwoBlocked [Fintype X] [DecidableEq X]
    (a : FV → (Fin 4 → X) → P → ℂ) (sh sv : TV → Equiv.Perm X) (σ : FV → P) :
    torusBondNetwork (fun v c => a v ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v))
        (fun v => Matrix.permMatrixHom (R := ℂ) (twoByTwoHorizontalPerm sh v))
        (fun v => Matrix.permMatrixHom (R := ℂ) (twoByTwoVerticalPerm sv v)) =
      torusBondNetwork (fun v c => twoByTwoTensor
        (fun i => a (kitaevPeriodicTilingEquiv (v, i)))
        ![c.1, c.2.1, c.2.2.1, c.2.2.2] (twoByTwoPhysicalEquiv σ v))
        (fun v => Matrix.permMatrixHom (R := ℂ) ((sh v).prodCongr (sh v)))
        (fun v => Matrix.permMatrixHom (R := ℂ) ((sv v).prodCongr (sv v))) := by
  rw [torusBondNetwork_perm_eq_twoByTwoTiledSum]
  rw [← twoByTwoTiledBondEquiv.sum_comp, torusBondNetwork_perm]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro hb _
  apply Finset.sum_congr rfl
  intro vb _
  simp_rw [← twoByTwoSiteLegs_permutation sh sv ((hb, vb), _)]
  simp only [twoByTwoTensor, twoByTwoPhysicalEquiv, Equiv.coe_fn_mk]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_prod_type]
  rfl

omit [NeZero width] [NeZero height] in
/-- A doubled coordinate crosses its periodic seam exactly on the second
member of the last pair. This includes a coarse period of one.
Source: SCP10, periodic two-by-two grouping, lines 1888–1906. -/
theorem kitaevDoubleCoordinateEquiv_seam (n : ℕ) [NeZero n]
    (x : ZMod n) (b : Fin 2) :
    kitaevDoubleCoordinateEquiv n (x, b) + 1 = 0 ↔ b = 1 ∧ x + 1 = 0 := by
  have hx := ZMod.val_lt x
  have hb := b.isLt
  have hn := NeZero.pos n
  have he : ∀ (a : ℕ), 0 < a → a ≤ n * 2 → (n * 2 ∣ a ↔ a = n * 2) := by
    intro a ha hle
    exact ⟨fun h => Nat.le_antisymm hle (Nat.le_of_dvd ha h), fun h => h ▸ dvd_rfl⟩
  have he' : n ∣ x.val + 1 ↔ x.val + 1 = n :=
    ⟨fun h => Nat.le_antisymm (by omega) (Nat.le_of_dvd (by omega) h),
      fun h => by rw [h]⟩
  rw [kitaevDoubleCoordinateEquiv_apply, ← Nat.cast_one, ← Nat.cast_add,
    ZMod.natCast_eq_zero_iff, he _ (by omega) (by omega)]
  have hs : x + 1 = 0 ↔ x.val + 1 = n := by
    calc
      x + 1 = 0 ↔ ((x.val + 1 : ℕ) : ZMod n) = 0 := by simp
      _ ↔ x.val + 1 = n := (ZMod.natCast_eq_zero_iff _ _).trans he'
  rw [hs]
  constructor
  · intro h
    exact ⟨Fin.ext (by simp only [Fin.val_one]; omega), by omega⟩
  · rintro ⟨rfl, h⟩
    simp only [Fin.val_one]
    omega

/-- Horizontal fine seams agree with the two crossing bonds of the coarse
seam; neither internal bond acquires an insertion.
Source: SCP10, Definition 5.6 and Observation 6.6. -/
theorem twoByTwoHorizontalPerm_seam (s : Equiv.Perm X) (v : FV) :
    twoByTwoHorizontalPerm (fun p : TV => if p.1 + 1 = 0 then s else Equiv.refl X) v =
      if v.1 + 1 = 0 then s else Equiv.refl X := by
  obtain ⟨⟨p, i⟩, rfl⟩ := kitaevPeriodicTilingEquiv.surjective v
  simp only [twoByTwoHorizontalPerm, Equiv.symm_apply_apply]
  fin_cases i <;>
    simp [kitaevPeriodicTilingEquiv, kitaevCornerEquiv, kitaevDoubleCoordinateEquiv_seam]

/-- Vertical fine seams agree with both top crossing bonds of the coarse
seam, in the native downward orientation.
Source: SCP10, Definition 5.6 and Observation 6.6. -/
theorem twoByTwoVerticalPerm_seam (s : Equiv.Perm X) (v : FV) :
    twoByTwoVerticalPerm (fun p : TV => if p.2 + 1 = 0 then s else Equiv.refl X) v =
      if v.2 + 1 = 0 then s else Equiv.refl X := by
  obtain ⟨⟨p, i⟩, rfl⟩ := kitaevPeriodicTilingEquiv.surjective v
  simp only [twoByTwoVerticalPerm, Equiv.symm_apply_apply]
  fin_cases i <;>
    simp [kitaevPeriodicTilingEquiv, kitaevCornerEquiv, kitaevDoubleCoordinateEquiv_seam]

variable (G : Type*) [Group G] [Fintype G] [DecidableEq G]

/-- The paired regular representation acts on both labels of a coarse bond
by the same left multiplication, with no inverse or transpose introduced.
Source: SCP10, Observation 6.5, lines 1840–1874. -/
def pairedLeftRegularMatrix : G →* Matrix (G × G) (G × G) ℂ :=
  Matrix.permMatrixHom.comp (MulAction.toPermHom G (G × G))

variable {G}

/-- Entrywise form of the paired regular bond action.
Source: SCP10, Observation 6.5, lines 1840–1874. -/
theorem pairedLeftRegularMatrix_apply (g : G) (x y : G × G) :
    pairedLeftRegularMatrix G g x y =
      if x = (g * y.1, g * y.2) then 1 else 0 := by
  exact permMatrixHom_apply_eq_ite _ _ _

/-- The paired regular action is exactly the tensor product of the two
original regular actions. Source: SCP10, Observation 6.5. -/
theorem pairedLeftRegularMatrix_eq_kronecker (g : G) :
    pairedLeftRegularMatrix G g =
      (leftRegularMatrix G g).kronecker (leftRegularMatrix G g) := by
  ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
  simp only [pairedLeftRegularMatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    leftRegularMatrix_apply, Prod.mk.injEq, ite_zero_mul_ite_zero, mul_one]

/-- Exact native closure-preserving two-by-two blocking. Every fine seam
insertion becomes the same insertion on both labels of its coarse bond.
The physical coordinates are the four original registers in clockwise order.
No commutation, invariance, normalization, or state-factorization assumption
is needed, and both coarse periods may be one or two.
Source: SCP10, Definition 5.6 and the geometric step of Observation 6.6. -/
theorem torusGClosure_leftRegular_eq_twoByTwoBlocked
    (a : G → G → G → G → P → ℂ) (g h : G) (σ : FV → P) :
    torusGClosure (leftRegularMatrix G) a g h σ =
      torusGClosure (pairedLeftRegularMatrix G)
        (fun t r b l => twoByTwoTensor (fun _ α => a (α 0) (α 1) (α 2) (α 3))
          ![t, r, b, l]) g h (twoByTwoPhysicalEquiv σ) := by
  let sh : TV → Equiv.Perm G :=
    fun v => if v.1 + 1 = 0 then MulAction.toPermHom G G h else Equiv.refl G
  let sv : TV → Equiv.Perm G :=
    fun v => if v.2 + 1 = 0 then MulAction.toPermHom G G g else Equiv.refl G
  have hh : torusHorizontalClosure (leftRegularMatrix G) h =
      fun v : FV => Matrix.permMatrixHom (R := ℂ) (twoByTwoHorizontalPerm sh v) := by
    funext v
    rw [show twoByTwoHorizontalPerm sh v =
      if v.1 + 1 = 0 then MulAction.toPermHom G G h else Equiv.refl G from
        twoByTwoHorizontalPerm_seam _ _]
    simp only [torusHorizontalClosure]
    split_ifs
    · rfl
    · exact (map_one (Matrix.permMatrixHom (R := ℂ))).symm
  have hv : torusVerticalClosure (leftRegularMatrix G) g =
      fun v : FV => Matrix.permMatrixHom (R := ℂ) (twoByTwoVerticalPerm sv v) := by
    funext v
    rw [show twoByTwoVerticalPerm sv v =
      if v.2 + 1 = 0 then MulAction.toPermHom G G g else Equiv.refl G from
        twoByTwoVerticalPerm_seam _ _]
    simp only [torusVerticalClosure]
    split_ifs
    · rfl
    · exact (map_one (Matrix.permMatrixHom (R := ℂ))).symm
  unfold torusGClosure
  rw [hh, hv]
  have hb := torusBondNetwork_perm_eq_twoByTwoBlocked
    (fun (_ : FV) α => a (α 0) (α 1) (α 2) (α 3)) sh sv σ
  dsimp at hb
  rw [hb]
  congr 1
  · funext v
    simp only [sh, torusHorizontalClosure]
    split_ifs
    · rfl
    · exact map_one (Matrix.permMatrixHom (R := ℂ))
  · funext v
    simp only [sv, torusVerticalClosure]
    split_ifs
    · rfl
    · exact map_one (Matrix.permMatrixHom (R := ℂ))

end TNLean.PEPS
