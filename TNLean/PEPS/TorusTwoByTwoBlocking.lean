/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.KitaevPeriodicTiling

/-!
# Geometric two-by-two blocking with arbitrary virtual and physical alphabets

The actual bond-indexed torus contraction is regrouped into four-site blocks.
The result has four paired virtual legs and all four original physical registers.
Every internal and crossing bond is accounted for by an explicit bijection.
No symmetry, Gram matrix, support, or global factorization is assumed.

Source: SCP10, arXiv:1001.3807, Observations 6.5–6.6, lines 1818–1915,
particularly the two-by-two diagram `figs4/renorm-fixedpoint.pdf`.

This is the geometric contraction step, not the complete fixed-point theorem.
The model keeps one outgoing horizontal and vertical bond per site, including
coarse periods one and two. It never identifies these small tori with a simple
graph. All bonds have the identity operator; inserted closure operators are
outside the scope of this statement.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable {X P : Type*}
local notation "TV" => TorusVertex width height
local notation "FV" => TorusVertex (width * 2) (height * 2)

/-- Identify four paired boundary legs with the eight separate boundary legs.
Top and bottom pairs are ordered left to right; right and left pairs are ordered
top to bottom. Source: SCP10, two-by-two blocking diagram, lines 1888–1906. -/
def twoByTwoBoundaryEquiv : (Fin 4 → X × X) ≃ (Fin 4 × Fin 2 → X) where
  toFun α p := ![(α p.1).1, (α p.1).2] p.2
  invFun β i := (β (i, 0), β (i, 1))
  left_inv α := rfl
  right_inv β := by
    funext p
    rcases p with ⟨i, j⟩
    fin_cases j <;> rfl

/-- The four corner leg configurations, in top-right-bottom-left order.
Corners run clockwise from upper right. The four internal variables label
upper, right, lower, and left internal bonds in that order.
Source: SCP10, two-by-two blocking diagram, lines 1888–1906. -/
def twoByTwoSiteLegs (α : Fin 4 → X × X) (x : Fin 4 → X) :
    Fin 4 → Fin 4 → X :=
  ![![(α 0).2, (α 1).1, x 1, x 0],
    ![x 1, (α 1).2, (α 2).2, x 2],
    ![x 3, x 2, (α 2).1, (α 3).2],
    ![(α 0).1, x 0, x 3, (α 3).1]]

/-- Contract exactly the four internal bonds of a two-by-two block, retaining
all eight boundary coordinates and all four physical registers.
Source: SCP10, lines 1888–1906. -/
def twoByTwoTensor [Fintype X]
    (a : Fin 4 → (Fin 4 → X) → P → ℂ)
    (α : Fin 4 → X × X) (σ : Fin 4 → P) : ℂ :=
  ∑ x : Fin 4 → X, ∏ i, a i (twoByTwoSiteLegs α x i) (σ i)

/-- Read the four paired crossing bonds of an actual periodic block.
The incoming pairs use the same coordinate ordering as their outgoing ends;
no crossing bond is discarded or identified with another bond.
Source: SCP10, lines 1888–1906. -/
def twoByTwoPeriodicBoundary (hb vb : TV → X × X) (v : TV) : Fin 4 → X × X :=
  ![vb v, hb v, vb (v.1, v.2 - 1), hb (v.1 - 1, v.2)]

/-- Bijection between all coarse crossing pairs plus four internal bonds per
block and the actual fine horizontal and vertical bonds in tile coordinates.
This also applies at periodic seams and for coarse periods one and two.
Source: SCP10, two-by-two blocking diagram, lines 1888–1906. -/
def twoByTwoTiledBondEquiv :
    (((TV → X × X) × (TV → X × X)) × (TV → Fin 4 → X)) ≃
      ((TV × Fin 4 → X) × (TV × Fin 4 → X)) where
  toFun p :=
    (fun q => ![(p.1.1 q.1).1, (p.1.1 q.1).2, p.2 q.1 2, p.2 q.1 0] q.2,
     fun q => ![(p.1.2 q.1).2, p.2 q.1 1, p.2 q.1 3, (p.1.2 q.1).1] q.2)
  invFun q :=
    ((fun v => (q.1 (v, 0), q.1 (v, 1)), fun v => (q.2 (v, 3), q.2 (v, 0))),
      fun v => ![q.1 (v, 3), q.2 (v, 1), q.1 (v, 2), q.2 (v, 2)])
  left_inv p := by
    apply Prod.ext
    · apply Prod.ext <;> funext v <;> rfl
    · funext v i
      fin_cases i <;> rfl
  right_inv q := by
    apply Prod.ext
    · funext p
      rcases p with ⟨v, i⟩
      fin_cases i <;> rfl
    · funext p
      rcases p with ⟨v, i⟩
      fin_cases i <;> rfl

omit [NeZero width] [NeZero height] in
/-- The local eight-leg convention agrees with the neighbors of the fine torus.
Source: SCP10, lines 1888–1906. -/
theorem twoByTwoSiteLegs_periodic
    (p : ((TV → X × X) × (TV → X × X)) × (TV → Fin 4 → X))
    (v : TV × Fin 4) :
    twoByTwoSiteLegs (twoByTwoPeriodicBoundary p.1.1 p.1.2 v.1) (p.2 v.1) v.2 =
      ![(twoByTwoTiledBondEquiv p).2 v, (twoByTwoTiledBondEquiv p).1 v,
        (twoByTwoTiledBondEquiv p).2 (kitaevTiledDown v),
        (twoByTwoTiledBondEquiv p).1 (kitaevTiledLeft v)] := by
  rcases v with ⟨v, i⟩
  fin_cases i <;> rfl

/-- Regroup the full physical basis into one four-register basis per block.
All original directions, including unused local physical directions, remain.
Source: SCP10, physical grouping in lines 1888–1906. -/
def twoByTwoPhysicalEquiv : (FV → P) ≃ (TV → Fin 4 → P) where
  toFun σ v i := σ (kitaevPeriodicTilingEquiv (v, i))
  invFun τ p :=
    τ ((kitaevPeriodicTilingEquiv (width := width) (height := height)).symm p).1
      ((kitaevPeriodicTilingEquiv (width := width) (height := height)).symm p).2
  left_inv σ := by funext p; simp
  right_inv τ := by funext v i; simp

/-- The native fine network in disjoint tile coordinates, for an arbitrary
site-dependent tensor. This is a reindexing of genuine bond sums.
Source: SCP10, two-by-two blocking diagram, lines 1888–1906. -/
theorem torusBondNetwork_eq_twoByTwoTiledSum [Fintype X] [DecidableEq X]
    (a : FV → (Fin 4 → X) → P → ℂ) (σ : FV → P) :
    torusBondNetwork (fun v c => a v ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v)) 1 1 =
      ∑ q : (TV × Fin 4 → X) × (TV × Fin 4 → X),
        ∏ p : TV × Fin 4, a (kitaevPeriodicTilingEquiv p)
          ![q.2 p, q.1 p, q.2 (kitaevTiledDown p), q.1 (kitaevTiledLeft p)]
          (σ (kitaevPeriodicTilingEquiv p)) := by
  let E := kitaevPeriodicTilingEquiv (width := width) (height := height)
  let C := E.arrowCongr (Equiv.refl X)
  rw [torusBondNetwork_one, ← Fintype.sum_prod_type', ← (C.prodCongr C).sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  rw [← E.prod_comp]
  apply Finset.prod_congr rfl
  intro p _
  simp [C, E, Equiv.arrowCongr_apply,
    ← kitaevPeriodicTilingEquiv_down, ← kitaevPeriodicTilingEquiv_left]

/-- Exact geometric reblocking of the actual fine torus state into the
actual coarse torus state with four paired bonds per block. Both periods are
merely positive; no simplicity or lower bound three is required. No scalar
normalization is inserted: this is precisely the original contraction.
Source: SCP10, geometric step of Observation 6.6, lines 1888–1906. -/
theorem torusBondNetwork_eq_twoByTwoBlocked [Fintype X] [DecidableEq X]
    (a : FV → (Fin 4 → X) → P → ℂ) (σ : FV → P) :
    torusBondNetwork (fun v c => a v ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v)) 1 1 =
      torusBondNetwork (fun v c => twoByTwoTensor
        (fun i => a (kitaevPeriodicTilingEquiv (v, i)))
        ![c.1, c.2.1, c.2.2.1, c.2.2.2]
        (twoByTwoPhysicalEquiv σ v)) 1 1 := by
  rw [torusBondNetwork_eq_twoByTwoTiledSum, ← twoByTwoTiledBondEquiv.sum_comp,
    torusBondNetwork_one]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro hb _
  apply Finset.sum_congr rfl
  intro vb _
  simp_rw [← twoByTwoSiteLegs_periodic ((hb, vb), _)]
  simp only [twoByTwoTensor, twoByTwoPhysicalEquiv, Equiv.coe_fn_mk]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_prod_type]
  rfl

section PhysicalMatrix
variable [Fintype P] [DecidableEq P]

/-- The permutation matrix of physical four-site grouping. This acts on the
entire original physical Hilbert space, without dropping any direction.
Source: SCP10, lines 1888–1906. -/
def twoByTwoPhysicalMatrix : Matrix (TV → Fin 4 → P) (FV → P) ℂ :=
  endpointEmbeddingMatrix
    (twoByTwoPhysicalEquiv (width := width) (height := height)).toEmbedding

/-- Physical grouping is an isometry on the entire physical space. -/
theorem twoByTwoPhysicalMatrix_isIsometry :
    Matrix.IsIsometry (twoByTwoPhysicalMatrix (P := P) (width := width) (height := height)) :=
  endpointEmbeddingMatrix_isIsometry _

/-- The inverse physical grouping is also an isometry, so the change of basis
is unitary and retains even directions not used by the state. -/
theorem twoByTwoPhysicalMatrix_conjTranspose_isIsometry :
    Matrix.IsIsometry
      (twoByTwoPhysicalMatrix (P := P) (width := width) (height := height)).conjTranspose := by
  have h : (twoByTwoPhysicalMatrix (P := P) (width := width)
      (height := height)).conjTranspose =
      endpointEmbeddingMatrix
        (twoByTwoPhysicalEquiv (width := width) (height := height)).symm.toEmbedding := by
    ext σ τ
    simp [twoByTwoPhysicalMatrix, endpointEmbeddingMatrix, Matrix.conjTranspose_apply,
      Equiv.eq_symm_apply, eq_comm]
  rw [h]
  exact endpointEmbeddingMatrix_isIsometry _

/-- The physical unitary regrouping takes the actual fine state to its exact
four-site blocked state. This statement includes all periodic crossing bonds;
no global equality or state-support premise is supplied.
Source: SCP10, geometric step of Observation 6.6, lines 1888–1906. -/
theorem twoByTwoPhysicalMatrix_mulVec_network [Fintype X] [DecidableEq X]
    (a : FV → (Fin 4 → X) → P → ℂ) :
    (twoByTwoPhysicalMatrix (width := width) (height := height)) *ᵥ
        (fun σ => torusBondNetwork
          (fun v c => a v ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v)) 1 1) =
      fun τ => torusBondNetwork (fun v c => twoByTwoTensor
        (fun i => a (kitaevPeriodicTilingEquiv (v, i)))
        ![c.1, c.2.1, c.2.2.1, c.2.2.2] (τ v)) 1 1 := by
  funext τ
  let E := twoByTwoPhysicalEquiv (width := width) (height := height) (P := P)
  rw [Matrix.mulVec, dotProduct]
  rw [← E.symm.sum_comp]
  simp only [twoByTwoPhysicalMatrix, endpointEmbeddingMatrix,
    Equiv.toEmbedding_apply, E, Equiv.apply_symm_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [torusBondNetwork_eq_twoByTwoBlocked]
  simp only [Equiv.apply_symm_apply]

end PhysicalMatrix
end TNLean.PEPS
