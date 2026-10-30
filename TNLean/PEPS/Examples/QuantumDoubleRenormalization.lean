/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.QuantumDoubleLocalConstraint
import QICLean.Algebra.PermutationMatrixUnitary

/-!
# Physical renormalization of four elementary quantum-double tensors

Source: SCP10, arXiv:1001.3807v3, lines 2886–2916 and
`figs6/tc-lattice.pdf`, `figs6/tc-2x2-renorm.pdf`. Boundary pairs are north,
east, south, west; physical sites are NE, SE, SW, NW. All eight virtual
registers and all four physical registers are retained. The original arrows
produce inverse clockwise spins. A physical permutation inverts those spins
and extracts their ordered holonomy into the last register.

**Scope restriction:** This is a local four-site statement, without a lattice
tiling assertion. **Local fix (orientation):** The physical basis inversion is
explicit; the surplus virtual factors are identity-basis covectors, not uniform
vectors. See `docs/paper-gaps/scp10_quantum_double_local_hamiltonian.tex`.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G]

/-- The source pair operation on the entire two-register space, with its
nonabelian inverse. SCP10, lines 2900–2903. -/
def quantumDoubleRenormPair : Equiv.Perm (G × G) where
  toFun x := (x.1, x.2⁻¹ * x.1)
  invFun x := (x.1, x.1 * x.2⁻¹)
  left_inv x := by rcases x with ⟨a, b⟩; simp
  right_inv x := by rcases x with ⟨a, b⟩; simp

/-- Four original doubled boundary legs, ordered N,E,S,W. -/
abbrev QuantumDoubleRenormBoundary (G : Type*) := (G × G) × (G × G) × (G × G) × (G × G)

/-- The four independent pair operations; no surplus boundary register is removed. -/
def quantumDoubleRenormBoundary : Equiv.Perm (QuantumDoubleRenormBoundary G) :=
  quantumDoubleRenormPair.prodCongr
    (quantumDoubleRenormPair.prodCongr
      (quantumDoubleRenormPair.prodCongr quantumDoubleRenormPair))

/-- First register of each doubled boundary leg. -/
def quantumDoubleRenormColors (α : QuantumDoubleRenormBoundary G) : G × G × G × G :=
  (α.1.1, α.2.1.1, α.2.2.1.1, α.2.2.2.1)

/-- The four second boundary registers, retained as independent coordinates. -/
def quantumDoubleRenormSurplus (α : QuantumDoubleRenormBoundary G) : G × G × G × G :=
  (α.1.2, α.2.1.2, α.2.2.1.2, α.2.2.2.2)

/-- Full physical permutation: invert the original-arrow spins, then extract
clockwise holonomy. Its inverse reconstructs the fourth spin in the stated order. -/
def quantumDoubleRenormPhysical : Equiv.Perm (G × G × G × G) where
  toFun x := (x.1⁻¹, x.2.1⁻¹, x.2.2.1⁻¹, x.1⁻¹ * x.2.1⁻¹ * x.2.2.1⁻¹ * x.2.2.2⁻¹)
  invFun y := (y.1⁻¹, y.2.1⁻¹, y.2.2.1⁻¹,
    (y.2.2.2⁻¹ * (y.1 * y.2.1 * y.2.2.1)))
  left_inv x := by
    rcases x with ⟨a, b, c, d⟩
    simp only [inv_inv, Prod.mk.injEq, true_and]
    group
  right_inv x := by
    rcases x with ⟨a, b, c, d⟩
    simp only [inv_inv, Prod.mk.injEq, true_and]
    group

/-- Reconstruct the four clockwise spins from the three retained spins and
an identity holonomy register. No physical dimension is dropped. -/
def quantumDoubleRenormReconstruct (y : G × G × G × G) : G × G × G × G :=
  (y.1, y.2.1, y.2.2.1, (y.1 * y.2.1 * y.2.2.1)⁻¹ * y.2.2.2)

variable [DecidableEq G]

/-- The actual elementary tensor: its two virtual colors are copied from input
to output, and the physical spin is `L_s R_r |1⟩ = |s r⁻¹⟩`.
SCP10, lines 2886–2894. -/
def quantumDoubleElementaryTensor (r r' s s' x : G) : ℂ :=
  if r = r' ∧ s = s' ∧ x = s * r⁻¹ then 1 else 0

variable [Fintype G]

/-- The elementary tensor is the coefficient of the existing right-regular
matrix acting on `|s⟩ = L_s |1⟩`, with both virtual copies retained. Thus its
physical output is the source's `R_r L_s |1⟩ = L_s R_r |1⟩`. -/
theorem quantumDoubleElementaryTensor_eq_regular (r r' s s' x : G) :
    quantumDoubleElementaryTensor r r' s s' x =
      if r = r' ∧ s = s' then
        (rightRegularMatrix G r *ᵥ Pi.single s 1) x else 0 := by
  change quantumDoubleElementaryTensor r r' s s' x =
    if r = r' ∧ s = s' then
      ((Equiv.mulRight r : Equiv.Perm G).permMatrix ℂ *ᵥ Pi.single s 1) x else 0
  rw [Matrix.permMatrix_mulVec]
  simp [quantumDoubleElementaryTensor, Pi.single_apply, eq_mul_inv_iff_mul_eq, ite_and,
    eq_comm]

/-- Contract the four literal internal bonds of the A plaquette. N,E,S,W
boundary pairs are read clockwise; physical order is NE,SE,SW,NW.
SCP10, lines 2896–2911 and `figs6/tc-2x2-renorm.pdf`. -/
def quantumDoubleElementaryBlock (α : QuantumDoubleRenormBoundary G)
    (x : G × G × G × G) : ℂ :=
  ∑ c : G × G × G × G,
    let p := c.1
    let q := c.2.1
    let r := c.2.2.1
    let s := c.2.2.2
    quantumDoubleElementaryTensor α.1.2 p α.2.1.1 q x.1 *
    quantumDoubleElementaryTensor α.2.1.2 q α.2.2.1.1 r x.2.1 *
    quantumDoubleElementaryTensor α.2.2.1.2 r α.2.2.2.1 s x.2.2.1 *
    quantumDoubleElementaryTensor α.2.2.2.2 s α.1.1 p x.2.2.2

/-- Direct evaluation of the elementary contraction. Every compatible column
has coefficient exactly one, rather than an implicit normalization factor. -/
theorem quantumDoubleElementaryBlock_apply (α : QuantumDoubleRenormBoundary G)
    (x : G × G × G × G) :
    quantumDoubleElementaryBlock α x =
      if quantumDoubleRenormSurplus α = quantumDoubleRenormColors α ∧
        x = (α.2.1.1 * α.1.1⁻¹, α.2.2.1.1 * α.2.1.1⁻¹,
          α.2.2.2.1 * α.2.2.1.1⁻¹, α.1.1 * α.2.2.2.1⁻¹) then 1 else 0 := by
  have ht (c : G × G × G × G) :
      quantumDoubleElementaryTensor α.1.2 c.1 α.2.1.1 c.2.1 x.1 *
        quantumDoubleElementaryTensor α.2.1.2 c.2.1 α.2.2.1.1 c.2.2.1 x.2.1 *
        quantumDoubleElementaryTensor α.2.2.1.2 c.2.2.1 α.2.2.2.1 c.2.2.2 x.2.2.1 *
        quantumDoubleElementaryTensor α.2.2.2.2 c.2.2.2 α.1.1 c.1 x.2.2.2 =
      if c = quantumDoubleRenormColors α ∧
          quantumDoubleRenormSurplus α = quantumDoubleRenormColors α ∧
          x = (α.2.1.1 * α.1.1⁻¹, α.2.2.1.1 * α.2.1.1⁻¹,
            α.2.2.2.1 * α.2.2.1.1⁻¹, α.1.1 * α.2.2.2.1⁻¹)
        then 1 else 0 := by
    simp only [quantumDoubleElementaryTensor, ite_zero_mul_ite_zero, one_mul]
    congr 1
    apply propext
    rcases c with ⟨p, q, r, s⟩
    rcases x with ⟨a, b, c, d⟩
    simp only [quantumDoubleRenormColors, quantumDoubleRenormSurplus, Prod.mk.injEq]
    constructor <;> intro h <;> simp_all
  unfold quantumDoubleElementaryBlock
  simp_rw [ht]
  by_cases h : quantumDoubleRenormSurplus α = quantumDoubleRenormColors α ∧
      x = (α.2.1.1 * α.1.1⁻¹, α.2.2.1.1 * α.2.1.1⁻¹,
        α.2.2.2.1 * α.2.2.1.1⁻¹, α.1.1 * α.2.2.2.1⁻¹)
  · simp [h]
  · simp [h]

/-- Three independent clockwise physical differences, before reinserting the
identity holonomy spin. -/
def quantumDoubleRenormReducedSpins (c : G × G × G × G) : G × G × G :=
  (c.1 * c.2.1⁻¹, c.2.1 * c.2.2.1⁻¹, c.2.2.1 * c.2.2.2⁻¹)

/-- The retained physical tensor, with precisely three independent spins. -/
def quantumDoubleRenormReducedTensor : Matrix (G × G × G) (G × G × G × G) ℂ :=
  fun x c => if x = quantumDoubleRenormReducedSpins c then 1 else 0

private def originalSpins (c : G × G × G × G) : G × G × G × G :=
  (c.2.1 * c.1⁻¹, c.2.2.1 * c.2.1⁻¹, c.2.2.2 * c.2.2.1⁻¹, c.1 * c.2.2.2⁻¹)

omit [DecidableEq G] [Fintype G] in
private theorem physical_original (c : G × G × G × G) :
    quantumDoubleRenormPhysical (originalSpins c) =
      ((quantumDoubleRenormReducedSpins c).1,
        (quantumDoubleRenormReducedSpins c).2.1,
        (quantumDoubleRenormReducedSpins c).2.2, 1) := by
  rcases c with ⟨p, q, r, s⟩
  simp [quantumDoubleRenormPhysical, originalSpins, quantumDoubleRenormReducedSpins,
    mul_assoc]

/-- Physical disentangling of the literal elementary block, with every surplus
factor retained. The pair permutation must be inverted when evaluating an old
coefficient at a new ket label; it is not generally an involution. -/
theorem quantumDoubleElementaryBlock_physicalRG (α : QuantumDoubleRenormBoundary G)
    (y : G × G × G × G) :
    quantumDoubleElementaryBlock (quantumDoubleRenormBoundary.symm α)
        (quantumDoubleRenormPhysical.symm y) =
      (if quantumDoubleRenormSurplus α = 1 then (1 : ℂ) else 0) *
      (if y.2.2.2 = 1 then (1 : ℂ) else 0) *
      quantumDoubleRenormReducedTensor (y.1, y.2.1, y.2.2.1)
        (quantumDoubleRenormColors α) := by
  rcases y with ⟨a, b, c, d⟩
  rw [quantumDoubleElementaryBlock_apply]
  change (if quantumDoubleRenormSurplus (quantumDoubleRenormBoundary.symm α) =
        quantumDoubleRenormColors (quantumDoubleRenormBoundary.symm α) ∧
      quantumDoubleRenormPhysical.symm (a, b, c, d) =
        originalSpins (quantumDoubleRenormColors (quantumDoubleRenormBoundary.symm α))
    then (1 : ℂ) else 0) = _
  have hc : quantumDoubleRenormColors (quantumDoubleRenormBoundary.symm α) =
      quantumDoubleRenormColors α := rfl
  have hd : quantumDoubleRenormSurplus (quantumDoubleRenormBoundary.symm α) =
      quantumDoubleRenormColors α ↔
        quantumDoubleRenormSurplus α = 1 := by
    simp [quantumDoubleRenormBoundary, quantumDoubleRenormPair,
      quantumDoubleRenormSurplus, quantumDoubleRenormColors, Prod.mk.injEq,
      mul_eq_left]
  simp only [hd, hc, Equiv.symm_apply_eq, physical_original]
  simp only [quantumDoubleRenormReducedTensor, Prod.ext_iff]
  split_ifs <;> simp_all [Prod.ext_iff]

/-- The physical and virtual changes of coordinates are unitary on their full
spaces, including configurations outside the tensor support. -/
theorem quantumDoubleRenorm_unitary :
    Equiv.Perm.permMatrix ℂ (quantumDoubleRenormPhysical (G := G)).symm ∈
        Matrix.unitaryGroup (G × G × G × G) ℂ ∧
      Equiv.Perm.permMatrix ℂ (quantumDoubleRenormBoundary (G := G)).symm ∈
        Matrix.unitaryGroup (QuantumDoubleRenormBoundary G) ℂ :=
  ⟨Equiv.Perm.permMatrix_mem_unitaryGroup _, Equiv.Perm.permMatrix_mem_unitaryGroup _⟩

/-- Splitting colors into three differences and one freely chosen color is a
bijection, with the multiplication order preserved. -/
def quantumDoubleRenormColorEquiv : (G × G × G × G) ≃ (G × G × G) × G where
  toFun c := (quantumDoubleRenormReducedSpins c, c.2.2.2)
  invFun z := (z.1.1 * z.1.2.1 * z.1.2.2 * z.2,
    z.1.2.1 * z.1.2.2 * z.2, z.1.2.2 * z.2, z.2)
  left_inv c := by
    rcases c with ⟨p, q, r, s⟩
    simp [quantumDoubleRenormReducedSpins, mul_assoc]
  right_inv z := by
    rcases z with ⟨⟨a, b, c⟩, t⟩
    simp [quantumDoubleRenormReducedSpins, mul_assoc]

/-- The raw local renormalization has squared singular value exactly |G|.
This scalar counts the common-color orbit; the four-T identity itself has scalar one. -/
theorem quantumDoubleRenormReducedTensor_mul_conjTranspose :
    quantumDoubleRenormReducedTensor (G := G) *
        (quantumDoubleRenormReducedTensor (G := G))ᴴ =
      (Fintype.card G : ℂ) • (1 : Matrix (G × G × G) (G × G × G) ℂ) := by
  ext x y
  have hr (z : (G × G × G) × G) :
      quantumDoubleRenormReducedSpins (quantumDoubleRenormColorEquiv.symm z) = z.1 :=
    congrArg Prod.fst (quantumDoubleRenormColorEquiv.apply_symm_apply z)
  rw [Matrix.mul_apply, ← quantumDoubleRenormColorEquiv.symm.sum_comp,
    Fintype.sum_prod_type]
  simp only [quantumDoubleRenormReducedTensor, Matrix.conjTranspose_apply, hr]
  simp [Matrix.one_apply]

omit [Fintype G] in
/-- Reinserting the identity holonomy recovers exactly the existing clockwise
K tensor, with coefficient one and the source's noncommutative order. -/
theorem quantumDoubleRenormReducedTensor_reconstruct (c : G × G × G × G)
    (y : G × G × G × G) :
    (if y.2.2.2 = 1 then (1 : ℂ) else 0) *
        quantumDoubleRenormReducedTensor (y.1, y.2.1, y.2.2.1) c =
      quantumDoubleKTensor G c.1 c.2.1 c.2.2.1 c.2.2.2
        (quantumDoubleRenormReconstruct y) := by
  have he : quantumDoubleRenormReconstruct y = quantumDoubleKSpins c ↔
      (y.1, y.2.1, y.2.2.1) = quantumDoubleRenormReducedSpins c ∧ y.2.2.2 = 1 := by
    constructor
    · intro h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg (fun x : G × G × G × G => x.2.1) h
      have h₃ := congrArg (fun x : G × G × G × G => x.2.2.1) h
      have hh := congrArg quantumDoubleKHolonomy h
      rw [quantumDoubleKHolonomy_spins] at hh
      refine ⟨Prod.ext h₁ (Prod.ext h₂ h₃), ?_⟩
      simpa [quantumDoubleRenormReconstruct, quantumDoubleKHolonomy, mul_assoc] using hh
    · rintro ⟨h, hd⟩
      rcases c with ⟨p, q, r, s⟩
      simp only [quantumDoubleRenormReducedSpins, Prod.mk.injEq] at h
      simp [quantumDoubleRenormReconstruct, quantumDoubleKSpins, h.1, h.2.1,
        h.2.2, hd, mul_assoc]
  simp only [quantumDoubleKTensor, he, quantumDoubleRenormReducedTensor]
  split_ifs <;> simp_all

/-- The exact K form of the four-T physical renormalization, retaining the
four surplus virtual registers and the physical holonomy register. -/
theorem quantumDoubleElementaryBlock_toK (α : QuantumDoubleRenormBoundary G)
    (y : G × G × G × G) :
    quantumDoubleElementaryBlock (quantumDoubleRenormBoundary.symm α)
        (quantumDoubleRenormPhysical.symm y) =
      (if quantumDoubleRenormSurplus α = 1 then (1 : ℂ) else 0) *
      quantumDoubleKTensor G α.1.1 α.2.1.1 α.2.2.1.1 α.2.2.2.1
        (quantumDoubleRenormReconstruct y) := by
  rw [quantumDoubleElementaryBlock_physicalRG, mul_assoc,
    quantumDoubleRenormReducedTensor_reconstruct]
  rfl

/-- The open four-T tensor map with all original physical and virtual labels. -/
def quantumDoubleElementaryBlockMatrix :
    Matrix (G × G × G × G) (QuantumDoubleRenormBoundary G) ℂ :=
  fun x α => quantumDoubleElementaryBlock α x

/-- The product of the retained tensor, a physical identity ket and four
virtual identity covectors. Both sets of surplus factors remain in the matrix. -/
def quantumDoubleRenormFactorMatrix :
    Matrix (G × G × G × G) (QuantumDoubleRenormBoundary G) ℂ :=
  fun y α => (if quantumDoubleRenormSurplus α = 1 then (1 : ℂ) else 0) *
    (if y.2.2.2 = 1 then (1 : ℂ) else 0) *
    quantumDoubleRenormReducedTensor (y.1, y.2.1, y.2.2.1) (quantumDoubleRenormColors α)

/-- A full physical unitary and virtual pair relabelling separate the actual
contracted elementary tensor map, on its entire domain and codomain. The inverse
in the physical permutation matrix is required by the pullback convention. -/
theorem quantumDoubleElementaryBlockMatrix_physicalRG :
    Equiv.Perm.permMatrix ℂ (quantumDoubleRenormPhysical (G := G)).symm *
        quantumDoubleElementaryBlockMatrix *
        Equiv.Perm.permMatrix ℂ (quantumDoubleRenormBoundary (G := G)) =
      quantumDoubleRenormFactorMatrix := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  ext y α
  exact quantumDoubleElementaryBlock_physicalRG α y

/-- The normalized retained tensor has the exact coefficient |G|^(-1/2). -/
noncomputable def quantumDoubleRenormNormalizedTensor :
    Matrix (G × G × G) (G × G × G × G) ℂ :=
  ((Real.sqrt (Fintype.card G) : ℂ)⁻¹) • quantumDoubleRenormReducedTensor

/-- Normalization by |G|^(-1/2) gives a coisometry, derived from the actual
common-color count rather than assumed on the elementary block. -/
theorem quantumDoubleRenormNormalizedTensor_mul_conjTranspose :
    quantumDoubleRenormNormalizedTensor (G := G) *
        (quantumDoubleRenormNormalizedTensor (G := G))ᴴ = 1 := by
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Real.sqrt (Fintype.card G) : ℂ) *
      (Real.sqrt (Fintype.card G) : ℂ) = (Fintype.card G : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hc : star ((Real.sqrt (Fintype.card G) : ℂ)⁻¹) =
      (Real.sqrt (Fintype.card G) : ℂ)⁻¹ := by
    simp
  simp only [quantumDoubleRenormNormalizedTensor, Matrix.conjTranspose_smul,
    hc, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, quantumDoubleRenormReducedTensor_mul_conjTranspose]
  rw [← mul_assoc, ← mul_inv, hs, inv_mul_cancel₀ hn, one_smul]

end TNLean.PEPS
