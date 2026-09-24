/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.MPDO.ActionTensor

/-!
# Matrix product operator symmetries: definitions

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), Sections 2–3,
`Papers/2203.12563/REsubmission.tex` lines 321–361 (matrix product operator algebras and the
fusion rules `O_a O_b = ∑_c N_{ab}^c O_c`), lines 429–460 (matrix product states symmetric under
such an algebra, the action tensors and the multiplicities `M_{a,x}^y`), lines 660–683 (unit,
inverses and the representation `M_{gh,x}^y = ∑_z M_{g,z}^y M_{h,x}^z` in the group case) and
lines 994–997 (the periodic-boundary weakening of both conditions).

**Formalized here.** The periodic-boundary layer of the non-invertible symmetry theory,
parallel to the invertible on-site layer of `TNLean/MPS/Symmetry/`: finite families of matrix
product operators whose periodic operators obey a fusion ring with nonnegative integer structure
constants, the unit and invertible labels of such a ring, matrix product states whose block
vectors are carried by the periodic operators to length-independent combinations of block
vectors, and the fusion characters and nonnegative integer representations these actions
produce.

**Scope restriction (periodic boundary):** the source defines symmetry by invariance of the
arbitrary-boundary subspace `𝒮_A^n` under the arbitrary-boundary algebra `𝒜_T^n` (lines
431–434); this file records only the periodic-boundary consequence, where both boundaries are
identities in each block (the weakening of line 997), which is what the fusion-ring statements
of the source use. Documented in `docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`.

## Main definitions

* `MPOTensor.IsMPOFusionAlgebra`: the fusion rules `O_a O_b = ∑_c N_{ab}^c O_c` of the periodic
  operators at every positive length.
* `MPOTensor.IsFusionUnit`, `MPOTensor.IsInvertibleLabel`: the unit and the invertible labels
  of a fusion ring given by structure constants.
* `MPOTensor.IsMPOSymmetricFamily`: a family of tensors whose periodic vectors are carried by
  every periodic operator of the algebra to length-independent combinations of the family.
* `MPOTensor.IsMPOSymmetric`: the single-block case, the periodic vector being a common
  eigenvector with length-independent eigenvalues.
* `MPOTensor.IsFusionCharacter`: a one-dimensional representation of the fusion ring.
* `MPOTensor.IsNIMRep`: a representation of the fusion ring by matrices of nonnegative integers,
  indexed by block labels.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
-/

open scoped Matrix

namespace MPOTensor

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Matrix product operator fusion algebra.**

Source: arXiv:2203.12563, lines 361–362: the periodic operators `O_a = O_{T_a, 1}` of the blocks
of a matrix product operator algebra satisfy `O_a · O_b = ∑_c N_{ab}^c O_c` for every system
size, with `N_{ab}^c` the nonnegative integer multiplicity of `c` in the product of `a` and `b`.
System sizes are positive. -/
def IsMPOFusionAlgebra {χ : ι → ℕ} (O : ∀ a, MPOTensor d (χ a)) (N : ι → ι → ι → ℕ) : Prop :=
  ∀ a b : ι, ∀ L : ℕ, 0 < L → mpo (O a) L * mpo (O b) L = ∑ c, (N a b c : ℂ) • mpo (O c) L

/-- **Unit label of a fusion ring.**

Source: arXiv:2203.12563, line 660: a trivial block `e` with `O_e O_g = O_g O_e = O_g`, read on
the structure constants as `N_{eb}^c = N_{be}^c = δ_{bc}`. The operator `O_e` need not be the
identity; outside the on-site case it is a projector onto the relevant periodic subspace
(line 660). -/
def IsFusionUnit [DecidableEq ι] (N : ι → ι → ι → ℕ) (e : ι) : Prop :=
  ∀ b c : ι, N e b c = (if c = b then 1 else 0) ∧ N b e c = (if c = b then 1 else 0)

/-- **Invertible label of a fusion ring.**

Source: arXiv:2203.12563, line 660: an inverse `g⁻¹` of `g` with
`O_{g⁻¹} O_g = O_g O_{g⁻¹} = O_e`, read on the structure constants as
`N_{a b}^c = N_{b a}^c = δ_{c e}`. -/
def IsInvertibleLabel [DecidableEq ι] (N : ι → ι → ι → ℕ) (e a : ι) : Prop :=
  ∃ b : ι, ∀ c : ι, N a b c = (if c = e then 1 else 0) ∧ N b a c = (if c = e then 1 else 0)

/-- **A family of matrix product states symmetric under a matrix product operator algebra.**

Source: arXiv:2203.12563, lines 431–460 and line 997. The block vectors `ψ_x` of the family are
carried by every periodic operator `O_a` to a combination `∑_y M_{a,x}^y ψ_y` of block vectors
with coefficients independent of the system size: the periodic-boundary form of the invariance
`𝒜_T · 𝒮_A ⊂ 𝒮_A` (line 431) in which both boundaries are identities in each block (line 997).
The coefficients are a priori complex; that they are the nonnegative integer multiplicities
`M_{a,x}^y` of line 460 is a theorem (`MPOTensor.exists_nat_eq_of_isMPOSymmetricFamily`). -/
def IsMPOSymmetricFamily {χ : ι → ℕ} {D : κ → ℕ} (O : ∀ a, MPOTensor d (χ a))
    (A : ∀ x, MPSTensor d (D x)) (M : ι → κ → κ → ℂ) : Prop :=
  ∀ a x, ∀ L : ℕ, 0 < L →
    mpo (O a) L *ᵥ (fun τ : Fin L → Fin d => MPSTensor.mpv (A x) τ) =
      fun σ : Fin L → Fin d => ∑ y, M a x y * MPSTensor.mpv (A y) σ

/-- **A single matrix product state symmetric under a matrix product operator algebra.**

Source: arXiv:2203.12563, lines 607–613: the single-block case of
`MPOTensor.IsMPOSymmetricFamily`, where the periodic vector is a common eigenvector of the
periodic operators, `O_a ψ = c_a ψ` with `c_a` independent of the system size. -/
def IsMPOSymmetric {χ : ι → ℕ} {D : ℕ} (O : ∀ a, MPOTensor d (χ a)) (A : MPSTensor d D)
    (c : ι → ℂ) : Prop :=
  ∀ a, ∀ L : ℕ, 0 < L →
    mpo (O a) L *ᵥ (fun τ : Fin L → Fin d => MPSTensor.mpv A τ) =
      c a • fun σ : Fin L → Fin d => MPSTensor.mpv A σ

/-- **Fusion character.** A one-dimensional representation of the fusion ring: the unit goes
to `1` and `χ_a χ_b = ∑_c N_{ab}^c χ_c`. A fusion ring with a fusion character in `ℕ` has a ring
homomorphism to `ℤ`; the Fibonacci ring has none (arXiv:2203.12563, line 1993). -/
def IsFusionCharacter {R : Type*} [Semiring R] (N : ι → ι → ι → ℕ) (e : ι) (χ : ι → R) :
    Prop :=
  χ e = 1 ∧ ∀ a b : ι, χ a * χ b = ∑ c, (N a b c : R) * χ c

/-- **Nonnegative integer representation of a fusion ring on block labels.**

Source: arXiv:2203.12563, lines 491–492 and line 683: the multiplicities `M_{a,x}^y` of the
block `y` in the action of `a` on the block `x` satisfy the associativity
`(a × b) · x = a · (b · x)`, that is `∑_c N_{ab}^c M_{c,x}^y = ∑_z M_{b,x}^z M_{a,z}^y`
(for groups, `M_{gh,x}^y = ∑_z M_{g,z}^y M_{h,x}^z`). -/
def IsNIMRep (N : ι → ι → ι → ℕ) (M : ι → κ → κ → ℕ) : Prop :=
  ∀ a b : ι, ∀ x y : κ, ∑ c, N a b c * M c x y = ∑ z, M b x z * M a z y

end MPOTensor
