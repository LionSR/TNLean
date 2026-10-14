/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.RestoringVectors

/-!
# Physical coordinates for the two ancillary copies of the target

The restoring operator of the amplification proof acts on two ancillary copies `s', e'`
of the target `X` and on the physical system, written in the coordinates
`((s', e'), (X, Y)), Z'` with `X` in a full eigenbasis `{|x⟩}` of `ρ_X`. The constraint
products act on the physical system with the ancillas as spectators, in the original
physical coordinates. This module identifies the two descriptions.

Let `U` be the unitary whose columns are the eigenbasis, and `rs` an identification of
the physical configurations with `(X × Y) × Z`. The transport `𝒲` reorders the factors
into `physical × (s', e')`, undoes the basis change on the physical `X`, and applies the
same basis change on `e'`. It is a unitary between the two coordinate systems. Under `𝒲`:

* a physical operator written in the eigenbasis becomes `L ⊗ 1` on the ancillas;
* an operator `(A ⊗ M) ⊗ 1_Z` with `A` on the ancillas and `M` on `X × Y` becomes a
  physical operator on `X ∪ Y` tensored with `A` rotated on `e'`;
* the restored vector `Ω ⊗ ∑_x √p_x |x⟩_{s'}|x⟩_{e'}` becomes `Ω` tensored with an
  ancillary vector, and the vector with blanks on both ancillas becomes `Ω` tensored with
  the two blanks;
* the copied vector `ℛ_X Ω`, which moves the target to `e'`, becomes the original vector
  with its `X` coordinates read on `e'` and a blank on the physical `X`.

## Main definitions

* `TNLean.PEPS.AreaLaw.ancillaRotation`, `TNLean.PEPS.AreaLaw.ancillaTransport`.

## Main statements

* `TNLean.PEPS.AreaLaw.ancillaTransport_mul_conjTranspose`,
  `TNLean.PEPS.AreaLaw.conjTranspose_mul_ancillaTransport`: the transport is unitary.
* `TNLean.PEPS.AreaLaw.ancillaTransport_conj_physicalLift`: physical operators.
* `TNLean.PEPS.AreaLaw.ancillaTransport_conj_kronecker`: operators on the ancillas and `X × Y`.
* `TNLean.PEPS.AreaLaw.ancillaTransport_mulVec_restored`,
  `TNLean.PEPS.AreaLaw.ancillaTransport_mulVec_initial`,
  `TNLean.PEPS.AreaLaw.ancillaTransport_mulVec_copy`: the three vectors.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 324–371:
  the eigenbasis of `ρ_X`, the two copies `s', e'` with blank vectors,
  `eq:amplification-swapped-state`, `eq:amplification-restored-state`,
  `eq:amplification-restoring-operator` and `eq:amplification-column-operator`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped Kronecker

namespace TNLean.PEPS.AreaLaw

variable {X Y Z P : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

/-- The basis change `(1_{s'} ⊗ U_{e'}) ⊗ ((U_X ⊗ 1_Y) ⊗ 1_Z)` in the coordinates
`(s', e'), ((X, Y), Z)`. Source: `09-amplification.tex`, lines 324–332. -/
def ancillaRotation (U : Matrix X X ℂ) :
    Matrix ((X × X) × ((X × Y) × Z)) ((X × X) × ((X × Y) × Z)) ℂ :=
  ((1 : Matrix X X ℂ) ⊗ₖ U) ⊗ₖ ((U ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ))

/-- The transport from the restoring coordinates `((s', e'), (X, Y)), Z` to the
coordinates `physical × (s', e')`, for an identification `rs` of the physical
configurations with `(X × Y) × Z`. It undoes the basis change `U` on the physical `X`
and applies it on `e'`. Source: `09-amplification.tex`, lines 324–332 and 342–347. -/
def ancillaTransport (U : Matrix X X ℂ) (rs : P ≃ (X × Y) × Z) :
    Matrix (P × (X × X)) (((X × X) × (X × Y)) × Z) ℂ :=
  (ancillaRotation (Y := Y) (Z := Z) U).submatrix
    (fun c => (c.2, rs c.1)) Entropy.restoringPhysicalGrouping

/-- The reordering `physical × (s', e') ≃ (s', e') × ((X, Y), Z)`. -/
private def ancillaSwap (rs : P ≃ (X × Y) × Z) : P × (X × X) ≃ (X × X) × ((X × Y) × Z) :=
  (Equiv.prodComm P (X × X)).trans (Equiv.prodCongr (Equiv.refl _) rs)

omit [Fintype X] [Fintype Y] [Fintype Z] in
private theorem ancillaTransport_eq (U : Matrix X X ℂ) (rs : P ≃ (X × Y) × Z) :
    ancillaTransport U rs =
      (ancillaRotation (Y := Y) (Z := Z) U).submatrix (ancillaSwap rs)
        Entropy.restoringPhysicalGrouping :=
  rfl

private theorem ancillaRotation_unitary {U : Matrix X X ℂ} (hU : U * Uᴴ = 1)
    (hU' : Uᴴ * U = 1) :
    ancillaRotation (Y := Y) (Z := Z) U * (ancillaRotation U)ᴴ = 1 ∧
      (ancillaRotation (Y := Y) (Z := Z) U)ᴴ * ancillaRotation U = 1 := by
  refine ⟨?_, ?_⟩ <;> simp only [ancillaRotation, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.one_mul, hU, hU', one_kronecker_one]

/-- The transport is unitary: `𝒲 𝒲ᴴ = 1`. -/
theorem ancillaTransport_mul_conjTranspose [DecidableEq P] {U : Matrix X X ℂ} (hU : U * Uᴴ = 1)
    (hU' : Uᴴ * U = 1) (rs : P ≃ (X × Y) × Z) :
    ancillaTransport U rs * (ancillaTransport U rs)ᴴ = 1 := by
  rw [ancillaTransport_eq, conjTranspose_submatrix, submatrix_mul_equiv _ _ _
    Entropy.restoringPhysicalGrouping, (ancillaRotation_unitary hU hU').1,
    submatrix_one_equiv]

omit [Fintype Y] [Fintype Z] in
/-- The transport is unitary: `𝒲ᴴ 𝒲 = 1`. -/
theorem conjTranspose_mul_ancillaTransport [Fintype P] [Finite Y] [Finite Z] {U : Matrix X X ℂ}
    (hU : U * Uᴴ = 1)
    (hU' : Uᴴ * U = 1) (rs : P ≃ (X × Y) × Z) :
    (ancillaTransport U rs)ᴴ * ancillaTransport U rs = 1 := by
  have : Fintype Y := Fintype.ofFinite Y
  have : Fintype Z := Fintype.ofFinite Z
  rw [ancillaTransport_eq, conjTranspose_submatrix, submatrix_mul_equiv _ _ _
    (ancillaSwap rs), (ancillaRotation_unitary hU hU').2, submatrix_one_equiv]

/-- Conjugating a matrix by the transport, in the reordered coordinates. -/
private theorem ancillaTransport_conj (U : Matrix X X ℂ) (rs : P ≃ (X × Y) × Z)
    (K : Matrix (((X × X) × (X × Y)) × Z) (((X × X) × (X × Y)) × Z) ℂ) :
    ancillaTransport U rs * K * (ancillaTransport U rs)ᴴ =
      (ancillaRotation U * K.submatrix Entropy.restoringPhysicalGrouping.symm
        Entropy.restoringPhysicalGrouping.symm * (ancillaRotation U)ᴴ).submatrix
          (ancillaSwap rs) (ancillaSwap rs) := by
  rw [ancillaTransport_eq, conjTranspose_submatrix]
  have hK : K = (K.submatrix Entropy.restoringPhysicalGrouping.symm
      Entropy.restoringPhysicalGrouping.symm).submatrix Entropy.restoringPhysicalGrouping
        Entropy.restoringPhysicalGrouping := by simp
  conv_lhs => rw [hK]
  rw [submatrix_mul_equiv _ _ _ Entropy.restoringPhysicalGrouping,
    submatrix_mul_equiv _ _ _ Entropy.restoringPhysicalGrouping]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] in
/-- Conjugating a Kronecker product by a Kronecker product. -/
private theorem kronecker_conj {m n m' n' : Type*} [Fintype m] [Fintype n]
    (A : Matrix m' m ℂ) (B : Matrix n' n ℂ) (A' : Matrix m m ℂ) (B' : Matrix n n ℂ) :
    (A ⊗ₖ B) * (A' ⊗ₖ B') * (A ⊗ₖ B)ᴴ = (A * A' * Aᴴ) ⊗ₖ (B * B' * Bᴴ) := by
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] in
/-- Reordering a Kronecker product `A ⊗ M` on `(s', e') × ((X, Y), Z)` into
`physical × (s', e')`. -/
private theorem kronecker_submatrix_ancillaSwap (rs : P ≃ (X × Y) × Z)
    (A : Matrix (X × X) (X × X) ℂ) (M : Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ) :
    (A ⊗ₖ M).submatrix (ancillaSwap rs) (ancillaSwap rs) = M.submatrix rs rs ⊗ₖ A := by
  ext ⟨c, a⟩ ⟨c', a'⟩
  simp [ancillaSwap, kroneckerMap_apply, mul_comm]

/-- **Physical operators.** A physical operator `L`, written in the eigenbasis of the
target as `(Uᴴ ⊗ 1) L (U ⊗ 1)` and acting trivially on both ancillas, is transported to
`L ⊗ 1` on the original physical coordinates. Source: `09-amplification.tex`,
lines 399–408. -/
theorem ancillaTransport_conj_physicalLift {U : Matrix X X ℂ} (hU : U * Uᴴ = 1)
    (rs : P ≃ (X × Y) × Z) (L : Matrix P P ℂ) :
    ancillaTransport U rs * Entropy.restoringPhysicalLift
        (((Uᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) * L.submatrix rs.symm rs.symm *
          ((U ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ))) *
        (ancillaTransport U rs)ᴴ =
      L ⊗ₖ (1 : Matrix (X × X) (X × X) ℂ) := by
  rw [ancillaTransport_conj]
  have hlift : (Entropy.restoringPhysicalLift
      (((Uᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) * L.submatrix rs.symm rs.symm *
        ((U ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)))).submatrix
          Entropy.restoringPhysicalGrouping.symm Entropy.restoringPhysicalGrouping.symm =
      (1 : Matrix (X × X) (X × X) ℂ) ⊗ₖ
        (((Uᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) * L.submatrix rs.symm rs.symm *
          ((U ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ))) := by
    simp [Entropy.restoringPhysicalLift]
  have h1 : (U ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ) *
      ((Uᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) = 1 := by
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, hU]
    simp
  have hs : ((1 : Matrix X X ℂ) ⊗ₖ U) * ((1 : Matrix X X ℂ) ⊗ₖ U)ᴴ = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU]
    simp
  have hphys : (U ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ) *
      (((Uᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) * L.submatrix rs.symm rs.symm *
        ((U ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ))) *
      ((U ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ))ᴴ = L.submatrix rs.symm rs.symm := by
    rw [conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_one, conjTranspose_one]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [hlift, ancillaRotation, kronecker_conj, Matrix.mul_one, hs, hphys,
    kronecker_submatrix_ancillaSwap]
  simp

/-- **Operators on the ancillas and on `X × Y`.** The operator `(A ⊗ M) ⊗ 1_Z`, with `A`
on the ancillas `(s', e')` and `M` on `X × Y` in the eigenbasis of the target, is
transported to the physical operator `((U ⊗ 1) M (U ⊗ 1)ᴴ ⊗ 1_Z)` tensored with `A`
rotated on `e'`. Source: `09-amplification.tex`, lines 348–368. -/
theorem ancillaTransport_conj_kronecker {U : Matrix X X ℂ} (rs : P ≃ (X × Y) × Z)
    (A : Matrix (X × X) (X × X) ℂ) (M : Matrix (X × Y) (X × Y) ℂ) :
    ancillaTransport U rs * ((A ⊗ₖ M) ⊗ₖ (1 : Matrix Z Z ℂ)) * (ancillaTransport U rs)ᴴ =
      (((U ⊗ₖ (1 : Matrix Y Y ℂ)) * M * (U ⊗ₖ (1 : Matrix Y Y ℂ))ᴴ) ⊗ₖ
          (1 : Matrix Z Z ℂ)).submatrix rs rs ⊗ₖ
        (((1 : Matrix X X ℂ) ⊗ₖ U) * A * ((1 : Matrix X X ℂ) ⊗ₖ U)ᴴ) := by
  rw [ancillaTransport_conj]
  have hK : ((A ⊗ₖ M) ⊗ₖ (1 : Matrix Z Z ℂ)).submatrix Entropy.restoringPhysicalGrouping.symm
      Entropy.restoringPhysicalGrouping.symm = A ⊗ₖ (M ⊗ₖ (1 : Matrix Z Z ℂ)) := by
    ext ⟨a, ⟨m, z⟩⟩ ⟨a', ⟨m', z'⟩⟩
    simp [Entropy.restoringPhysicalGrouping, kroneckerMap_apply, mul_assoc]
  rw [hK, ancillaRotation, kronecker_conj, kronecker_conj, kronecker_submatrix_ancillaSwap]
  simp

/-- A Kronecker product acting on a product vector. -/
private theorem kronecker_mulVec_prod {m n m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m m' ℂ) (B : Matrix n n' ℂ) (a : m' → ℂ) (b : n' → ℂ) :
    (A ⊗ₖ B) *ᵥ (fun p : m' × n' => a p.1 * b p.2) =
      fun p : m × n => (A *ᵥ a) p.1 * (B *ᵥ b) p.2 := by
  ext ⟨i, j⟩
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply,
    Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => by ring

/-- Writing a vector in the restoring coordinates through the reordering. -/
private theorem ancillaTransport_mulVec (U : Matrix X X ℂ) (rs : P ≃ (X × Y) × Z)
    (v : ((X × X) × (X × Y)) × Z → ℂ) :
    ancillaTransport U rs *ᵥ v =
      (ancillaRotation U *ᵥ (v ∘ Entropy.restoringPhysicalGrouping.symm)) ∘ ancillaSwap rs := by
  rw [ancillaTransport_eq]
  ext c
  simp only [mulVec, dotProduct, submatrix_apply, Function.comp_apply]
  rw [← Entropy.restoringPhysicalGrouping.sum_comp]
  simp

/-- The rotated physical vector `ψ = (Uᴴ ⊗ 1 ⊗ 1) Ω` is returned to `Ω` by the inverse
rotation. -/
private theorem rotation_mulVec_rotated {U : Matrix X X ℂ} (hU : U * Uᴴ = 1)
    (rs : P ≃ (X × Y) × Z) (Ω : P → ℂ) :
    ((U ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) *ᵥ
        (((Uᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) *ᵥ fun i => Ω (rs.symm i)) =
      fun i => Ω (rs.symm i) := by
  rw [mulVec_mulVec, ← mul_kronecker_mul, ← mul_kronecker_mul, hU]
  simp

/-- **The restored vector.** The vector `ψ ⊗ ∑_x √p_x |x⟩_{s'}|x⟩_{e'}`, with `ψ` the
physical vector `Ω` in the eigenbasis of the target, is transported to `Ω` tensored with
the ancillary vector `(1 ⊗ U) ∑_x √p_x |x, x⟩`.
Source: `eq:amplification-restored-state`, `09-amplification.tex`, lines 338–341. -/
theorem ancillaTransport_mulVec_restored {U : Matrix X X ℂ} (hU : U * Uᴴ = 1)
    (rs : P ≃ (X × Y) × Z) (p : X → ℝ) (Ω : P → ℂ) :
    ancillaTransport U rs *ᵥ (Entropy.restoringRestored p (WithLp.toLp 2
        (((Uᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) *ᵥ fun i => Ω (rs.symm i)))).ofLp =
      fun c => Ω c.1 * (((1 : Matrix X X ℂ) ⊗ₖ U) *ᵥ
        fun a : X × X => if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0) c.2 := by
  rw [ancillaTransport_mulVec]
  have hv : (Entropy.restoringRestored p (WithLp.toLp 2
      (((Uᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) *ᵥ
        fun i => Ω (rs.symm i)))).ofLp ∘ Entropy.restoringPhysicalGrouping.symm =
      fun h => (fun a : X × X => if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0) h.1 *
        (((Uᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) *ᵥ
          fun i => Ω (rs.symm i)) h.2 := by
    ext ⟨⟨s, e⟩, ⟨x, y⟩, z⟩
    rfl
  rw [hv, ancillaRotation, kronecker_mulVec_prod ((1 : Matrix X X ℂ) ⊗ₖ U)
    ((U ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ))
    (fun a : X × X => if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0),
    rotation_mulVec_rotated hU]
  ext ⟨c, a⟩
  simp [ancillaSwap, mul_comm]

/-- **Blanks on both ancillas.** The vector `|0⟩_{s'}|0⟩_{e'} ⊗ ψ` is transported to `Ω`
tensored with the blanks, the second rotated by `U`.
Source: `eq:amplification-column-identity`, `09-amplification.tex`, lines 366–369. -/
theorem ancillaTransport_mulVec_initial {U : Matrix X X ℂ} (hU : U * Uᴴ = 1)
    (rs : P ≃ (X × Y) × Z) (sBlank eBlank : X → ℂ) (Ω : P → ℂ) :
    ancillaTransport U rs *ᵥ (Entropy.restoringInitial sBlank eBlank (WithLp.toLp 2
        (((Uᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) *ᵥ fun i => Ω (rs.symm i)))).ofLp =
      fun c => Ω c.1 * (sBlank c.2.1 * (U *ᵥ eBlank) c.2.2) := by
  rw [ancillaTransport_mulVec]
  have hv : (Entropy.restoringInitial sBlank eBlank (WithLp.toLp 2
      (((Uᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) *ᵥ
        fun i => Ω (rs.symm i)))).ofLp ∘ Entropy.restoringPhysicalGrouping.symm =
      fun h => (fun a : X × X => sBlank a.1 * eBlank a.2) h.1 *
        (((Uᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) *ᵥ
          fun i => Ω (rs.symm i)) h.2 := by
    ext ⟨⟨s, e⟩, ⟨x, y⟩, z⟩
    rfl
  have hblank : ((1 : Matrix X X ℂ) ⊗ₖ U) *ᵥ (fun a : X × X => sBlank a.1 * eBlank a.2) =
      fun a => sBlank a.1 * (U *ᵥ eBlank) a.2 := by
    rw [kronecker_mulVec_prod, one_mulVec]
  rw [hv, ancillaRotation, kronecker_mulVec_prod ((1 : Matrix X X ℂ) ⊗ₖ U)
    ((U ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) (fun a : X × X => sBlank a.1 * eBlank a.2),
    rotation_mulVec_rotated hU, hblank]
  ext ⟨c, a⟩
  simp [ancillaSwap, mul_comm]

/-- **The copied vector.** The vector `ℛ_X ψ`, with blanks on `s'` and on `X` and the
target moved to `e'`, is transported to the vector whose value at a physical
configuration `c` and ancillary pair `(s, e)` is `|0⟩(s) (U |0⟩)(c_X) Ω(c')`, where `c'`
agrees with `c` off `X` and reads `e` on `X`.
Source: `eq:amplification-swapped-state`, `09-amplification.tex`, lines 334–347. -/
theorem ancillaTransport_mulVec_copy {U : Matrix X X ℂ} (hU : U * Uᴴ = 1)
    (rs : P ≃ (X × Y) × Z) (sBlank xBlank : X → ℂ) (Ω : P → ℂ) :
    ancillaTransport U rs *ᵥ (Entropy.restoringCopy sBlank xBlank (WithLp.toLp 2
        (((Uᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) *ᵥ fun i => Ω (rs.symm i)))).ofLp =
      fun c => sBlank c.2.1 * (U *ᵥ xBlank) (rs c.1).1.1 *
        Ω (rs.symm ((c.2.2, (rs c.1).1.2), (rs c.1).2)) := by
  rw [ancillaTransport_mulVec]
  set ψ : (X × Y) × Z → ℂ := ((Uᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) *ᵥ
    fun i => Ω (rs.symm i) with hψ
  have hrot : ((U ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) *ᵥ ψ =
      fun i => Ω (rs.symm i) := rotation_mulVec_rotated hU rs Ω
  ext ⟨c, ⟨s, e⟩⟩
  have hrot' := congrFun hrot ((e, (rs c).1.2), (rs c).2)
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply, one_apply,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] at hrot'
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, Function.comp_apply, ancillaSwap,
    Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map_apply, id_eq, Entropy.restoringPhysicalGrouping,
    Equiv.prodAssoc_symm_apply, Entropy.restoringCopy, ancillaRotation,
    kroneckerMap_apply, one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_eq_single s (fun b _ hb => by simp [Ne.symm hb]) (by simp), ← hrot',
    Finset.mul_sum]
  simp only [↓reduceIte, one_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The physical operator `((U ⊗ 1) M (U ⊗ 1)ᴴ) ⊗ 1_Z` on the original physical coordinates,
for an operator `M` on `X × Y` written in the eigenbasis of the target.
Source: `09-amplification.tex`, lines 348–353. -/
def ancillaPhysical (U : Matrix X X ℂ) (rs : P ≃ (X × Y) × Z) (M : Matrix (X × Y) (X × Y) ℂ) :
    Matrix P P ℂ :=
  (((U ⊗ₖ (1 : Matrix Y Y ℂ)) * M * (U ⊗ₖ (1 : Matrix Y Y ℂ))ᴴ) ⊗ₖ
    (1 : Matrix Z Z ℂ)).submatrix rs rs

omit [DecidableEq Y] [Fintype Z] in
/-- The restoring operator `R₀` with the remote system explicit, as a sum over the selected
indices of operators `A ⊗ M ⊗ 1_Z`, with `A` acting on `s'` alone.
Source: `eq:amplification-restoring-operator`, `09-amplification.tex`, lines 350–355. -/
theorem restoringGlobal_eq_sum (E : Finset X) (p : X → ℝ) (sBlank xBlank : X → ℂ)
    (Q : Matrix (X × Y) (X × Y) ℂ) (T : Matrix Y Y ℂ) :
    Entropy.restoringGlobal (Z := Z) E p sBlank xBlank Q T =
      ∑ x ∈ E, ((Entropy.restoringWeight (p x) • (Entropy.basisColumn x sBlank ⊗ₖ
        (1 : Matrix X X ℂ))) ⊗ₖ (Q * (Entropy.basisColumn x xBlank ⊗ₖ T))) ⊗ₖ
          (1 : Matrix Z Z ℂ) := by
  ext ⟨⟨⟨s, e⟩, x, y⟩, z⟩ ⟨⟨⟨s', e'⟩, x', y'⟩, z'⟩
  simp only [Entropy.restoringGlobal, Entropy.restoringOperatorWithAncilla,
    Entropy.restoringOperator, Entropy.restoringAncillaGrouping, kroneckerMap_apply,
    submatrix_apply, Equiv.coe_fn_mk, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

omit [DecidableEq Y] [Fintype Z] in
/-- The column operator `B₀` with the remote system explicit, as a sum of operators
`A ⊗ M ⊗ 1_Z`. Source: `eq:amplification-column-operator`, `09-amplification.tex`,
lines 359–364. -/
theorem restoringColumnGlobal_eq_sum (E : Finset X) (p : X → ℝ) (sBlank eBlank : X → ℂ)
    (Q : Matrix (X × Y) (X × Y) ℂ) (T : Matrix Y Y ℂ) :
    Entropy.restoringColumnGlobal (Z := Z) E p sBlank eBlank Q T =
      ∑ x ∈ E, ∑ y : X, ((Entropy.restoringWeight (p x) • (Entropy.basisColumn x sBlank ⊗ₖ
        Entropy.basisColumn y eBlank)) ⊗ₖ (Q * (single x y 1 ⊗ₖ T))) ⊗ₖ
          (1 : Matrix Z Z ℂ) := by
  ext i j
  simp only [Entropy.restoringColumnGlobal, Entropy.columnOperator, kroneckerMap_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **The transported restoring operator.** Under the transport, `R₀` becomes
`∑_{x selected} P_x ⊗ (p_x^{-1/2} |x⟩⟨0|_{s'} ⊗ 1_{e'})`, where each `P_x` is the physical
operator obtained from `Q (|x⟩⟨0|_X ⊗ T)`. Source: `09-amplification.tex`, lines 350–356. -/
theorem ancillaTransport_conj_restoringGlobal {U : Matrix X X ℂ} (hU : U * Uᴴ = 1)
    (rs : P ≃ (X × Y) × Z) (E : Finset X) (p : X → ℝ) (sBlank xBlank : X → ℂ)
    (Q : Matrix (X × Y) (X × Y) ℂ) (T : Matrix Y Y ℂ) :
    ancillaTransport U rs * Entropy.restoringGlobal E p sBlank xBlank Q T *
        (ancillaTransport U rs)ᴴ =
      ∑ x ∈ E, ancillaPhysical U rs (Q * (Entropy.basisColumn x xBlank ⊗ₖ T)) ⊗ₖ
        (Entropy.restoringWeight (p x) • (Entropy.basisColumn x sBlank ⊗ₖ
          (1 : Matrix X X ℂ))) := by
  rw [restoringGlobal_eq_sum, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ancillaTransport_conj_kronecker, ancillaPhysical, Matrix.mul_smul, Matrix.smul_mul,
    kronecker_conj, Matrix.mul_one, hU]
  simp

/-- **The transported column operator.** Under the transport, `B₀` becomes a sum of
physical operators obtained from `Q (|x⟩⟨y|_X ⊗ T)`, tensored with operators on the
ancillas. Source: `09-amplification.tex`, lines 359–364. -/
theorem ancillaTransport_conj_restoringColumnGlobal {U : Matrix X X ℂ}
    (rs : P ≃ (X × Y) × Z) (E : Finset X) (p : X → ℝ) (sBlank eBlank : X → ℂ)
    (Q : Matrix (X × Y) (X × Y) ℂ) (T : Matrix Y Y ℂ) :
    ancillaTransport U rs * Entropy.restoringColumnGlobal E p sBlank eBlank Q T *
        (ancillaTransport U rs)ᴴ =
      ∑ x ∈ E, ∑ y : X, ancillaPhysical U rs (Q * (single x y 1 ⊗ₖ T)) ⊗ₖ
        (((1 : Matrix X X ℂ) ⊗ₖ U) * (Entropy.restoringWeight (p x) •
          (Entropy.basisColumn x sBlank ⊗ₖ Entropy.basisColumn y eBlank)) *
            ((1 : Matrix X X ℂ) ⊗ₖ U)ᴴ) := by
  rw [restoringColumnGlobal_eq_sum, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ancillaTransport_conj_kronecker, ancillaPhysical]

end TNLean.PEPS.AreaLaw
