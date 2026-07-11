/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.SectorEtaContraction

/-!
# Sector-chain coordinates for neighboring operators

The sector decomposition of one physical site has index space
\[
  \coprod_k B_k^L\times B_k^R.
\]
For a chain of length $N$, choosing one sector at each site separates the
physical index space into fibers over the sector configurations.  In these
coordinates, the cyclic tensor product of the neighboring operators
$\eta_{k_n,k_{n+1}}$ is defined by its matrix entries.

No positivity is imposed on the neighboring operators.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1441--1464
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D N : ℕ}
variable {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}

/-- The physical index within a fixed sector configuration of a chain. At each
site it consists of one left and one right sector index.

Source: arXiv:1606.00608, Appendix C.2, lines 1434--1464. -/
abbrev SectorFiber (hη : EtaStructure ρ) (k : Fin N → Fin hη.m) :=
  (n : Fin N) → Fin (hη.dL (k n)) × Fin (hη.dR (k n))

/-- The sector-adapted physical index of a chain: a sector configuration
together with one physical index in its corresponding fiber.

Source: arXiv:1606.00608, Appendix C.2, lines 1434--1464. -/
abbrev SectorChainIndex (hη : EtaStructure ρ) (N : ℕ) :=
  Σ k : Fin N → Fin hη.m, SectorFiber hη k

private def piSigmaEquiv
    {ι : Type*} {α : ι → Type*} {β : (i : ι) → α i → Type*} :
    ((i : ι) → Σ a, β i a) ≃
      Σ a : (i : ι) → α i, (i : ι) → β i (a i) where
  toFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  invFun x i := ⟨x.1 i, x.2 i⟩
  left_inv x := by
    funext i
    exact Sigma.eta (x i)
  right_inv x := by
    obtain ⟨a, b⟩ := x
    rfl

/-- The sitewise Hayashi decomposition identifies physical chain indices with
a sector configuration and an index in the corresponding sector fiber.

Source: arXiv:1606.00608, Appendix C.2, lines 1434--1464. -/
def sectorChainEquiv (hη : EtaStructure ρ) (N : ℕ) :
    (Fin N → Fin d) ≃ SectorChainIndex hη N :=
  (Equiv.piCongrRight fun _ : Fin N => hη.decompB).trans
    piSigmaEquiv

@[simp] lemma sectorChainEquiv_apply_fst (hη : EtaStructure ρ)
    (b : Fin N → Fin d) (n : Fin N) :
    (sectorChainEquiv hη N b).1 n = (hη.decompB (b n)).1 :=
  rfl

@[simp] lemma sectorChainEquiv_apply_snd (hη : EtaStructure ρ)
    (b : Fin N → Fin d) (n : Fin N) :
    (sectorChainEquiv hη N b).2 n = (hη.decompB (b n)).2 :=
  rfl

@[simp] lemma sectorChainEquiv_symm_apply (hη : EtaStructure ρ)
    (x : SectorChainIndex hη N) (n : Fin N) :
    (sectorChainEquiv hη N).symm x n =
      hη.decompB.symm ⟨x.1 n, x.2 n⟩ :=
  rfl

/-- Conjugating both physical indices of every local MPO matrix by the same
matrix changes the physical basis without changing the horizontal bond space.
-/
noncomputable def conjugatePhysical (K : MPOTensor d D)
    (U : Matrix (Fin d) (Fin d) ℂ) : MPOTensor d D :=
  fun i j β α => (U * physicalSlice K β α * Uᴴ) i j

@[simp] lemma conjugatePhysical_apply (K : MPOTensor d D)
    (U : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) (β α : Fin D) :
    conjugatePhysical K U i j β α =
      (U * physicalSlice K β α * Uᴴ) i j :=
  rfl

@[simp] lemma physicalSlice_conjugatePhysical (K : MPOTensor d D)
    (U : Matrix (Fin d) (Fin d) ℂ) (β α : Fin D) :
    physicalSlice (conjugatePhysical K U) β α =
      U * physicalSlice K β α * Uᴴ :=
  rfl

/-- Within one sector, the basis-conjugated local MPO matrix is the product of
the corresponding entries of the left and right sector tensors. -/
theorem conjugatePhysical_sectorFactorization_apply
    (K : MPOTensor d D) (hη : EtaStructure ρ)
    (l : (q : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dL q)) (Fin (hη.dL q)) ℂ)
    (r : (q : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dR q)) (Fin (hη.dR q)) ℂ)
    (hfactor : ∀ β α,
      Matrix.reindex hη.decompB hη.decompB
          ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β α *
            (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
        = Matrix.blockDiagonal' fun q =>
            Matrix.kroneckerMap (· * ·) (l q β) (r q α))
    (q : Fin hη.m) (iL jL : Fin (hη.dL q))
    (iR jR : Fin (hη.dR q)) (β α : Fin D) :
    conjugatePhysical K hη.U_B
        (hη.decompB.symm ⟨q, (iL, iR)⟩)
        (hη.decompB.symm ⟨q, (jL, jR)⟩) β α =
      l q β iL jL * r q α iR jR := by
  rw [conjugatePhysical_apply]
  have h := congrFun (congrFun (hfactor β α)
    ⟨q, (iL, iR)⟩) ⟨q, (jL, jR)⟩
  simpa [Matrix.reindex_apply, Matrix.blockDiagonal'_apply_eq,
    Matrix.kroneckerMap_apply] using h

private theorem mps_evalWord_ofFn_prod {dphys Dbond : ℕ}
    (A : MPSTensor dphys Dbond) {n : ℕ} (σ : Fin n → Fin dphys) :
    MPSTensor.evalWord A (List.ofFn σ) =
      (List.ofFn fun i => A (σ i)).prod := by
  induction n with
  | zero => simp only [List.ofFn_zero, MPSTensor.evalWord_nil, List.prod_nil]
  | succ n ih =>
    simp only [List.ofFn_succ, MPSTensor.evalWord_cons, List.prod_cons]
    congr 1
    exact ih (σ ∘ Fin.succ)

/-- The cyclic tensor product of neighboring operators in the fiber of a fixed
sector configuration. Its entries pair the right index at site $n$ with the
left index at site $n+1$.

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1464. -/
noncomputable def cyclicEtaTensorProduct
    [NeZero N] (hη : EtaStructure ρ) (eta : etaOperators hη)
    (k : Fin N → Fin hη.m) :
    Matrix (SectorFiber hη k) (SectorFiber hη k) ℂ :=
  fun x y => ∏ n : Fin N,
    eta (k n) (k (n + 1))
      ((x n).2, (x (n + 1)).1)
      ((y n).2, (y (n + 1)).1)

@[simp] lemma cyclicEtaTensorProduct_apply
    [NeZero N] (hη : EtaStructure ρ) (eta : etaOperators hη)
    (k : Fin N → Fin hη.m) (x y : SectorFiber hη k) :
    cyclicEtaTensorProduct hη eta k x y =
      ∏ n : Fin N, eta (k n) (k (n + 1))
        ((x n).2, (x (n + 1)).1)
        ((y n).2, (y (n + 1)).1) :=
  rfl

/-- **A fixed sector block is the cyclic tensor product of neighboring
operators.** If every transformed physical slice splits into the sector
tensors $l_q\otimes r_q$, then the compression of the $N$-site operator to a
fixed sector configuration $k_0,\ldots,k_{N-1}$ is the cyclic tensor product
of $\eta_{k_n,k_{n+1}}$.

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1464. -/
theorem mpo_submatrix_sector_eq_cyclicEtaTensorProduct
    (K : MPOTensor d D) (hη : EtaStructure ρ)
    (l : (q : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dL q)) (Fin (hη.dL q)) ℂ)
    (r : (q : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dR q)) (Fin (hη.dR q)) ℂ)
    (hfactor : ∀ β α,
      Matrix.reindex hη.decompB hη.decompB
          ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β α *
            (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
        = Matrix.blockDiagonal' fun q =>
            Matrix.kroneckerMap (· * ·) (l q β) (r q α))
    {N : ℕ} [NeZero N] (k : Fin N → Fin hη.m) :
    Matrix.submatrix (mpo (conjugatePhysical K hη.U_B) N)
        (fun x n => hη.decompB.symm ⟨k n, x n⟩)
        (fun x n => hη.decompB.symm ⟨k n, x n⟩) =
      cyclicEtaTensorProduct hη (etaOfSectorTensors hη l r) k := by
  ext x y
  rw [cyclicEtaTensorProduct_apply]
  simp only [Matrix.submatrix_apply, mpo_apply, mpoMatrixEntry,
    MPOTensor.evalWord_ofFn]
  have hlocal : ∀ n : Fin N,
      conjugatePhysical K hη.U_B
        (hη.decompB.symm ⟨k n, x n⟩)
        (hη.decompB.symm ⟨k n, y n⟩) =
      Matrix.of (fun β α =>
        l (k n) β (x n).1 (y n).1 * r (k n) α (x n).2 (y n).2) := by
    intro n
    ext β α
    exact conjugatePhysical_sectorFactorization_apply
      K hη l r hfactor (k n) (x n).1 (y n).1 (x n).2 (y n).2 β α
  have hlist :
      List.ofFn (fun n : Fin N =>
        conjugatePhysical K hη.U_B
          (hη.decompB.symm ⟨k n, x n⟩)
          (hη.decompB.symm ⟨k n, y n⟩)) =
      List.ofFn (fun n : Fin N => Matrix.of fun β α =>
        l (k n) β (x n).1 (y n).1 * r (k n) α (x n).2 (y n).2) := by
    exact congrArg List.ofFn (funext fun n => hlocal n)
  rw [hlist]
  have h := trace_sector_word_eq_prod_etaOfSectorTensors hη l r k
    (fun n => (x n).1) (fun n => (y n).1)
    (fun n => (x n).2) (fun n => (y n).2)
  rw [mps_evalWord_ofFn_prod] at h
  simpa only [id_eq] using h

end MPOTensor
