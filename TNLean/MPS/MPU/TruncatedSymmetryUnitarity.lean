/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.StaircaseUnitarity
import TNLean.MPS.MPU.TruncatedSymmetryGrowth

/-!
# Unitarity of truncated symmetries at every bulk length

For a simple MPU in canonical form II, the endpoint contraction in
arXiv:2502.20257, `eq:truncsym` and the sentence immediately following it
(lines 2062–2101), is unitary between its input and output coordinate spaces.
Here `N` counts bulk sites, while the source total length is $L=N+2\geq2$
(`eq:truncsym`, lines 2094–2097; CZX display, lines 4700–4713). The corresponding
source length notation is $U_g^{N+2}$, not $U_g^N$. The zero-bulk base case has
total length two and is the source gate $u$ of arXiv:1703.09188,
`uu` (lines 532–543), whose unitarity follows from the simple-MPU
source-gate equivalence theorem of arXiv:1703.09188 (lines 563–601). Each
additional bulk site is added by the unitary left movement gate of
arXiv:2502.20257, `cor:mpu`(a), using the left-end factorization of
`eq:move_trunc_sym`.

**Scope restriction (endpoint-coordinate unitarity):** the conclusion is
unitary-between the stated rectangularly indexed coordinate spaces. The
two-sided source-factorization growth identity of `eq:move_trunc_sym` is
formalized separately in `TruncatedSymmetryGrowth`. This theorem does not
identify each endpoint source space with a physical site, specialize to a
finite-group operator, prove agreement of the interior action with a global
symmetry, or establish the complementary finite-chain relation following
`eq:move_trunc_sym`. Documented in
`docs/paper-gaps/fbc25_truncated_symmetry_endpoint_unitarity_scope.tex`.
No adjoint-simplicity premise is used.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

/-- Regroup the first bulk letter and its tail without changing either endpoint. -/
private def truncatedConsEquiv (A B : Type*) (d N : ℕ) :
    (A × Fin d × (Fin N → Fin d) × B) ≃ (A × (Fin (N + 1) → Fin d) × B) where
  toFun x := (x.1, Fin.cons x.2.1 x.2.2.1, x.2.2.2)
  invFun x := (x.1, x.2.1 0, Fin.tail x.2.1, x.2.2)
  left_inv x := by simp
  right_inv x := by simp

/-- The truncated symmetry is unitary between its coordinate spaces for every
number `N` of bulk sites, hence every source total length $L=N+2\geq2$.
In source length notation this is $U_g^{N+2}$; the `N = 0` base case is the
two-site endpoint contraction, not a length-zero operator.
Source: arXiv:2502.20257, `eq:truncsym` and its
following unitarity assertion (lines 2062–2101). The assumptions are precisely
canonical form II and simplicity; the source and movement gate unitarities
are derived rather than supplied as hypotheses. -/
theorem IsMPUCanonicalFormII.truncatedSymmetry_isUnitaryBetween
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (N : ℕ) :
    ((sourceFactors U hU.ρ hU.ρ_posDef).truncatedSymmetry N).IsUnitaryBetween := by
  classical
  let S := sourceFactors U hU.ρ hU.ρ_posDef
  change (S.truncatedSymmetry N).IsUnitaryBetween
  have hu : (SourceFactors.sourceU U S).IsUnitaryBetween :=
    (hU.isMPUSimple_tfae.out 0 2).mp hsimple
  have hL : (SourceFactors.sourceWL U S).IsUnitaryBetween :=
    (hU.sourceWL_sourceWR_isUnitaryBetween hsimple).1
  induction N with
  | zero =>
    let e (A B : Type) : (A × B) ≃ (A × (Fin 0 → Fin d) × B) :=
      Equiv.prodCongr (Equiv.refl A) (Equiv.uniqueProd B (Fin 0 → Fin d)).symm
    have heq : S.truncatedSymmetry 0 =
        Matrix.reindex (e (Fin ℓ[U]) (Fin r[U])) (e (Fin d) (Fin d))
          (SourceFactors.sourceU U S) := by
      ext ⟨l, σ, r⟩ ⟨a, τ, b⟩
      simp [e, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [heq]
    exact hu.reindex _ _ _
  | succ N ih =>
    let R := (Fin N → Fin d) × Fin r[U]
    let A := Matrix.reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
      (SourceFactors.sourceWL U S ⊗ₖ (1 : Matrix R R ℂ))
    let B := (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ S.truncatedSymmetry N
    have hId : (1 : Matrix (Fin d) (Fin d) ℂ).IsUnitaryBetween := by
      simp [Matrix.IsUnitaryBetween, Matrix.IsIsometry, Matrix.IsCoisometry]
    have hIR : (1 : Matrix R R ℂ).IsUnitaryBetween := by
      simp [Matrix.IsUnitaryBetween, Matrix.IsIsometry, Matrix.IsCoisometry]
    have hA : A.IsUnitaryBetween :=
      (hL.kronecker _ _ hIR).reindex _ _ _
    have hB : B.IsUnitaryBetween := hId.kronecker _ _ ih
    have heq : S.truncatedSymmetry (N + 1) =
        Matrix.reindex (truncatedConsEquiv (Fin ℓ[U]) (Fin r[U]) d N)
          (truncatedConsEquiv (Fin d) (Fin d) d N) (A * B) := by
      ext ⟨l, σ, r⟩ ⟨a, τ, c⟩
      cases σ using Fin.consCases with
      | cons i σ =>
        cases τ using Fin.consCases with
        | cons b τ =>
          simp [SourceFactors.truncatedSymmetry_cons, A, B, R,
            Matrix.reindex_apply, Matrix.submatrix_apply, truncatedConsEquiv,
            Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
            Matrix.one_apply, mul_ite, ite_mul, Finset.sum_ite_irrel]
    rw [heq]
    exact (hA.mul _ _ hB).reindex _ _ _

end MPOTensor
