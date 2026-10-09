import TNLean.MPS.MPU.VirtualUnitaryGauge
import TNLean.MPS.MPU.Simple
import TNLean.MPS.MPDO.BondSimilarity

/-!
# The fundamental theorem of matrix product unitaries at the level of letters

Two matrix product unitary tensors in canonical form II generate the same periodic operators at
every length at least two if and only if they have the same bond dimension and their letters are
unitarily conjugate. The "only if" direction is
`IsMPUCanonicalFormII.exists_unitary_virtual_gauge_of_mpo_eq`;
the "if" direction is the cyclicity of the trace, `MPOTensor.mpo_eq_of_conj`.

This file also records the pulling-through identities of a simple tensor: closing two double-layer
letters by the left witness collapses the first letter to its trace character, and symmetrically on
the right.

Sources: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624--648) and the remark that
$z$ is unitary because both tensors are in canonical form II; Sahinoglu, Shukla, Bi, Chen,
arXiv:1704.01943, Corollary 1 of section III (pulling through).
-/

open scoped Matrix
open Matrix

namespace MPOTensor

/-- Letterwise unitary conjugation across an equality of bond dimensions leaves every periodic
operator unchanged. -/
theorem mpo_eq_of_unitary_conj {d D₁ D₂ : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hdim : D₁ = D₂) (z : Matrix.unitaryGroup (Fin D₂) ℂ)
    (hV : ∀ i j : Fin d,
      V i j = (z : Matrix (Fin D₂) (Fin D₂) ℂ) *
        (cast (congrArg (MPOTensor d) hdim) U) i j *
        (z : Matrix (Fin D₂) (Fin D₂) ℂ)ᴴ) (N : ℕ) :
    mpo U N = mpo V N := by
  subst hdim
  exact mpo_eq_of_conj (M := U) (N := V)
    (G := (z : Matrix (Fin D₁) (Fin D₁) ℂ)) (H := (z : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ)
    (Matrix.mem_unitaryGroup_iff.mp z.2) (Matrix.mem_unitaryGroup_iff'.mp z.2)
    (fun i j => (hV i j).symm) N

/-- **Fundamental theorem of matrix product unitaries, letters.** Two tensors in canonical form II
generate the same periodic operators at every length at least two if and only if they have the
same bond dimension and their letters are related by a unitary conjugation of the bond space.

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624--648) together with the
remark (lines 647--648) that `z` is unitary because both tensors are in canonical form II. The
source prints no letter-level equivalence; this statement is the design choice recorded in the
milestone proposal (MA.tex, Remark on what the source states). -/
theorem IsMPUCanonicalFormII.mpo_eq_iff_exists_unitary_conj
    {d D₁ D₂ : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V) :
    (∀ N : ℕ, 1 < N → mpo U N = mpo V N) ↔
      ∃ hdim : D₁ = D₂, ∃ z : Matrix.unitaryGroup (Fin D₂) ℂ,
        ∀ i j : Fin d,
          V i j = (z : Matrix (Fin D₂) (Fin D₂) ℂ) *
            (cast (congrArg (MPOTensor d) hdim) U) i j *
            (z : Matrix (Fin D₂) (Fin D₂) ℂ)ᴴ := by
  constructor
  · exact fun hEq => hU.exists_unitary_virtual_gauge_of_mpo_eq hV hEq
  · rintro ⟨hdim, z, hz⟩ N _
    exact mpo_eq_of_unitary_conj hdim z hz N

/-- **Pulling through.** For any pair of simplicity witnesses `a, b` of a tensor, closing two
double-layer letters on the left by `a` gives the trace character of the first letter times the
second letter closed by `a`; symmetrically on the right.

Source: Sahinoglu, Shukla, Bi, Chen, arXiv:1704.01943, Corollary 1 (pulling through), from the
separation and isometry equations, which are the simplicity identities of CPSV17. -/
theorem pulling_through_of_simple_witnesses {d D : ℕ} {U : MPOTensor d D}
    {a b : Fin (D * D) → ℂ}
    (h1 : ∀ i j : Fin d, a ⬝ᵥ (doubleLayerTensor U i j *ᵥ b) = if i = j then 1 else 0)
    (h2 : ∀ i j k l : Fin d,
      doubleLayerTensor U i j * doubleLayerTensor U k l =
        doubleLayerTensor U i j * vecMulVec b a * doubleLayerTensor U k l) :
    (∀ i j k l : Fin d,
      a ᵥ* (doubleLayerTensor U i j * doubleLayerTensor U k l) =
        if i = j then a ᵥ* doubleLayerTensor U k l else 0) ∧
    (∀ i j k l : Fin d,
      (doubleLayerTensor U i j * doubleLayerTensor U k l) *ᵥ b =
        if k = l then doubleLayerTensor U i j *ᵥ b else 0) := by
  refine ⟨?_, ?_⟩
  · intro i j k l
    rw [h2 i j k l, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_vecMulVec,
      ← Matrix.dotProduct_mulVec, h1 i j]
    split_ifs <;> simp
  · intro i j k l
    rw [h2 i j k l, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.vecMulVec_mulVec,
      h1 k l]
    split_ifs <;> simp

/-- **Pulling through** for a simple tensor: there are witnesses `a, b` with the normalization
identity and both pulling-through identities (`pulling_through_of_simple_witnesses` applied to
any witnesses of simplicity). -/
theorem IsMPUSimple.exists_pulling_through {d D : ℕ} {U : MPOTensor d D}
    (h : IsMPUSimple U) :
    ∃ a b : Fin (D * D) → ℂ,
      (∀ i j : Fin d, a ⬝ᵥ (doubleLayerTensor U i j *ᵥ b) = if i = j then 1 else 0) ∧
      (∀ i j k l : Fin d,
        a ᵥ* (doubleLayerTensor U i j * doubleLayerTensor U k l) =
          if i = j then a ᵥ* doubleLayerTensor U k l else 0) ∧
      (∀ i j k l : Fin d,
        (doubleLayerTensor U i j * doubleLayerTensor U k l) *ᵥ b =
          if k = l then doubleLayerTensor U i j *ᵥ b else 0) := by
  obtain ⟨a, b, h1, h2⟩ := h
  exact ⟨a, b, h1, (pulling_through_of_simple_witnesses h1 h2).1,
    (pulling_through_of_simple_witnesses h1 h2).2⟩

end MPOTensor
