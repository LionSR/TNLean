import TNLean.PEPS.RegionBlock.ThreeBlockResonateAB3

/-!
# Residual independence of the cross-tensor transfer kernel from bond locality

This file closes the residual-independence equation `TransferKernelResidualIndependent`
(`TNLean.PEPS.RegionBlock.ThreeBlockResonateAB3`) — the explicit `f`-leg-split form of
the general normal PEPS Fundamental Theorem per-edge gauge (arXiv:1804.04964, Section 3,
Lemma `inj_isomorph`, the step `V=W`) — by reading it off the bond locality of the
cross-tensor transfer kernel.

The witness matrix `witnessMatrix … M` (`TNLean.PEPS.RegionBlock.ThreeBlockResonateAB3`)
is the cross-tensor transfer kernel read off at the reference residual frame. The
incident-matrix kernel `incidentKernel B red f N` of *any* bond matrix `N`, read at the
reference residual, reduces to `N` on the `f`-legs (`incidentKernel_eq_split`,
`TNLean.PEPS.RegionBlock.ResonatePort2`), because the reference residual agrees with
itself. So whenever the transfer kernel of `M` is the incident-matrix kernel of a bond
matrix `N`, the reference read-off `witnessMatrix … M` *is* that `N`, and the
residual-independence equation is exactly the `f`-leg-split criterion
`transferCoeff_eq_incidentKernel_iff_split`
(`TNLean.PEPS.RegionBlock.ResonatePort2`) at `N`.

This reduces the residual-independence content to the single bond-locality fact
`IsBondLocalTransferKernel` (`TNLean.PEPS.RegionBlock.ThreeBlockTransfer`): the
cross-tensor transfer kernel of every inserted matrix is the incident-matrix kernel of
some bond matrix. The explicit witness `witnessMatrix` is then automatically that bond
matrix, with no separate construction needed.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, the step `V=W`, lines 355--486 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The witness matrix is read off any incident kernel

At the reference residual frame, the incident-matrix kernel `incidentKernel B red f N`
reads off `N` on the `f`-legs: the reference residual of the region boundary
configuration with `f`-leg `a` agrees with the reference residual of the complement
configuration of the region boundary configuration with `f`-leg `b`, so the kernel value
is `N a b`. Hence whenever the cross-tensor transfer kernel of `M` is the incident-matrix
kernel of `N`, its reference read-off `witnessMatrix … M` equals `N`. -/

/-- **The incident kernel reads off `N` at the reference frame.** For a bond matrix `N`,
the incident-matrix kernel `incidentKernel B red f N`, evaluated at the region boundary
configuration with `f`-leg `a` and the reference residual against the complement
configuration of the region boundary configuration with `f`-leg `b` and the reference
residual, is `N a b`.

The two reference residuals agree, so the `f`-leg-split form of the incident kernel
(`incidentKernel_eq_split`, `TNLean.PEPS.RegionBlock.ResonatePort2`) selects the
diagonal branch, reading `N` on the `f`-legs `a` and `b`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem incidentKernel_referenceBoundaryConfigAt_eq (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (a b : Fin (B.bondDim f.1)) :
    incidentKernel (G := G) B R f N
        (referenceBoundaryConfigAt (G := G) B R f hposB a)
        (regionComplementBoundaryConfigEquiv (G := G) B R
          (referenceBoundaryConfigAt (G := G) B R f hposB b)) =
      N a b := by
  classical
  rw [incidentKernel_eq_split B R f N]
  rw [Equiv.symm_apply_apply]
  rw [referenceBoundaryConfigAt_residual, referenceBoundaryConfigAt_residual,
    referenceBoundaryConfigAt_fLeg, referenceBoundaryConfigAt_fLeg, if_pos rfl]

/-- **The witness matrix is the bond matrix of a bond-local kernel.** If the cross-tensor
transfer kernel of `M` is the incident-matrix kernel of a bond matrix `N`, then the
reference read-off `witnessMatrix … M` equals `N`.

The witness reads the transfer kernel at the reference residual frame; with the kernel
equal to `incidentKernel B red f N`, this reads off `N` on the `f`-legs
(`incidentKernel_referenceBoundaryConfigAt_eq`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem witnessMatrix_eq_of_eq_incidentKernel (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hMN : transferCoeff (G := G) A B R hRB hCB f M = incidentKernel (G := G) B R f N) :
    witnessMatrix (G := G) A B R hRB hCB f hposB M = N := by
  funext a b
  rw [witnessMatrix, hMN, incidentKernel_referenceBoundaryConfigAt_eq B R f hposB N a b]

/-! ### Residual independence from bond locality

Bond locality of the cross-tensor transfer kernel of `M` — that it is the incident-matrix
kernel of *some* bond matrix `N` — gives residual independence with the explicit witness
`witnessMatrix … M`: the witness reads off that `N` at the reference frame
(`witnessMatrix_eq_of_eq_incidentKernel`), so the transfer kernel is the incident-matrix
kernel of `witnessMatrix … M` itself, which is the residual-independence equation read
through the `f`-leg split. -/

/-- **Residual independence from bond locality.** If the cross-tensor transfer kernel of
`M` is the incident-matrix kernel of a bond matrix `N`, then the kernel is residual
independent (`TransferKernelResidualIndependent`) with the witness the explicit
`witnessMatrix … M`.

The witness equals `N` (`witnessMatrix_eq_of_eq_incidentKernel`), so the kernel is the
incident-matrix kernel of `witnessMatrix … M`; reading this through the `f`-leg-split
criterion `transferCoeff_eq_incidentKernel_iff_split`
(`TNLean.PEPS.RegionBlock.ResonatePort2`) is exactly the residual-independence equation.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem transferKernelResidualIndependent_of_eq_incidentKernel (A B : Tensor G d)
    (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hMN : transferCoeff (G := G) A B R hRB hCB f M = incidentKernel (G := G) B R f N) :
    TransferKernelResidualIndependent (G := G) A B R hRB hCB f hposB M := by
  have hwit : witnessMatrix (G := G) A B R hRB hCB f hposB M = N :=
    witnessMatrix_eq_of_eq_incidentKernel A B R hRB hCB f hposB M N hMN
  intro μ ν'
  have hsplit := (transferCoeff_eq_incidentKernel_iff_split A B R hRB hCB f M N).mp hMN μ ν'
  rw [hsplit, hwit]

/-- **Residual independence from the bond-locality predicate.** If the cross-tensor
transfer kernel is bond-local (`IsBondLocalTransferKernel`,
`TNLean.PEPS.RegionBlock.ThreeBlockTransfer`), then every inserted matrix `M` has a
residual-independent transfer kernel with the explicit witness `witnessMatrix … M`.

For each `M`, bond locality supplies the bond matrix `N` whose incident-matrix kernel is
the transfer kernel; `transferKernelResidualIndependent_of_eq_incidentKernel` reads off
the residual independence at the explicit witness.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem residualIndependent_of_isBondLocalTransferKernel (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (hbond : IsBondLocalTransferKernel (G := G) A B R hRB hCB f) :
    ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      TransferKernelResidualIndependent (G := G) A B R hRB hCB f hposB M := by
  intro M
  obtain ⟨N, hN⟩ := hbond M
  exact transferKernelResidualIndependent_of_eq_incidentKernel A B R hRB hCB f hposB M N hN

end PEPS
end TNLean
