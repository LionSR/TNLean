/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.AreaLaw
import QICLean.ManyBody.Sites.Relabel

/-!
# Cyclic relocation of actual finite MPO conjugation

The closed virtual trace makes the finite periodic MPO invariant under
simultaneously rotating its bra and ket configurations. Thus both its
forward and adjoint conjugations commute with the actual cyclic site
permutation. Existing finite operator support is transported by that
permutation, including across the periodic seam.

These identities do not assume unitarity or inverse locality. For an MPU
at the source's permitted lengths the adjoint conjugation is its actual
inverse action. They supply the relocation step for inverse propagation
in arXiv:1703.09188, Appendix eq:appendix-1, lines 2300–2306.
-/

open scoped Matrix

namespace MPOTensor

variable {d D N : ℕ}

/-- Actual forward MPO conjugation commutes with a cyclic change of the
finite-chain cut. Source context: arXiv:1703.09188, eq:appendix-1,
lines 2300–2306; periodicity follows from the closed virtual trace. -/
theorem mpo_conjugation_submatrix_rotateConfig
    (U : MPOTensor d D) (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    (mpo U N * A * (mpo U N)ᴴ).submatrix (rotateConfig N d) (rotateConfig N d) =
      mpo U N * A.submatrix (rotateConfig N d) (rotateConfig N d) * (mpo U N)ᴴ := by
  rw [← Matrix.submatrix_mul_equiv (mpo U N * A) (mpo U N)ᴴ
    (rotateConfig N d) (rotateConfig N d) (rotateConfig N d),
    ← Matrix.submatrix_mul_equiv (mpo U N) A
      (rotateConfig N d) (rotateConfig N d) (rotateConfig N d),
    ← Matrix.conjTranspose_submatrix]
  simp only [mpo_submatrix_rotateConfig]

/-- Actual adjoint MPO conjugation commutes with the same cyclic cut
change. No inverse support bound is assumed. Source context:
arXiv:1703.09188, eq:appendix-1, lines 2300–2306. -/
theorem mpo_adjointConjugation_submatrix_rotateConfig
    (U : MPOTensor d D) (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    ((mpo U N)ᴴ * A * mpo U N).submatrix (rotateConfig N d) (rotateConfig N d) =
      (mpo U N)ᴴ * A.submatrix (rotateConfig N d) (rotateConfig N d) * mpo U N := by
  rw [← Matrix.submatrix_mul_equiv ((mpo U N)ᴴ * A) (mpo U N)
    (rotateConfig N d) (rotateConfig N d) (rotateConfig N d),
    ← Matrix.submatrix_mul_equiv (mpo U N)ᴴ A
      (rotateConfig N d) (rotateConfig N d) (rotateConfig N d),
    ← Matrix.conjTranspose_submatrix]
  simp only [mpo_submatrix_rotateConfig]

/-- Relabelling the sites of a configuration by a permutation `p` carries operators supported
on `S` to operators supported on `p '' S`; the case of
`ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators` with the identity on labels. -/
private theorem supportedOperators_submatrix_siteEquiv {d : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : Finset ι} (p : Equiv.Perm ι) {A : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S) :
    A.submatrix (fun σ ↦ σ ∘ p) (fun σ ↦ σ ∘ p) ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
        (S.image p) := by
  have h := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators
    (X := fun _ : ι ↦ Fin d) (X' := fun _ : ι ↦ Fin d) p (fun _ ↦ Equiv.refl _)
    (D := S) (D' := S.image p) (fun v ↦ by simp) hA
  have hsymm : ⇑(ManyBody.siteConfigurationEquiv (X := fun _ : ι ↦ Fin d)
      (X' := fun _ : ι ↦ Fin d) p (fun _ ↦ Equiv.refl _)).symm = fun σ ↦ σ ∘ p := by
    funext σ v
    rw [ManyBody.siteConfigurationEquiv_symm_apply]
    rfl
  rwa [Matrix.reindex_apply, hsymm] at h

/-- A forward finite MPO support bound relocates with the input through
the periodic seam. Source context: arXiv:1703.09188, eq:appendix-1,
lines 2300–2306. -/
theorem mpo_conjugation_mem_supportedOperators_rotate
    (U : MPOTensor d D) {A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {S : Finset (Fin N)}
    (hA : mpo U N * A * (mpo U N)ᴴ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S) :
    mpo U N * A.submatrix (rotateConfig N d) (rotateConfig N d) * (mpo U N)ᴴ ∈
      ManyBody.supportedOperators (fun _ ↦ Fin d) (S.image (finRotate N)) := by
  have h := supportedOperators_submatrix_siteEquiv (finRotate N) hA
  change (mpo U N * A * (mpo U N)ᴴ).submatrix (rotateConfig N d) (rotateConfig N d) ∈
    ManyBody.supportedOperators (fun _ ↦ Fin d) (S.image (finRotate N)) at h
  simpa only [mpo_conjugation_submatrix_rotateConfig] using h

/-- A finite support bound for the actual adjoint conjugation rotates
through the periodic seam with the input observable. This is the cyclic
relocation step toward the boundary-free inverse propagation statement,
not an assumed inverse-family compatibility condition.
Source context: arXiv:1703.09188, eq:appendix-1, lines 2300–2306. -/
theorem mpo_adjointConjugation_mem_supportedOperators_rotate
    (U : MPOTensor d D) {A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {S : Finset (Fin N)}
    (hA : (mpo U N)ᴴ * A * mpo U N ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S) :
    (mpo U N)ᴴ * A.submatrix (rotateConfig N d) (rotateConfig N d) * mpo U N ∈
      ManyBody.supportedOperators (fun _ ↦ Fin d) (S.image (finRotate N)) := by
  have h := supportedOperators_submatrix_siteEquiv (finRotate N) hA
  change ((mpo U N)ᴴ * A * mpo U N).submatrix (rotateConfig N d) (rotateConfig N d) ∈
    ManyBody.supportedOperators (fun _ ↦ Fin d) (S.image (finRotate N)) at h
  simpa only [mpo_adjointConjugation_submatrix_rotateConfig] using h

end MPOTensor
