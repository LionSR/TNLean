/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.WeakHopfRepresentation
import TNLean.MPS.Symmetry.BoundaryProjectionAverage

/-!
# The weak-Hopf average of the canonical parent term

Garre-Rubio, Lootens and Molnár symmetrize the canonical parent term of an
MPS under an MPO representation of a C*-weak Hopf algebra by
\[
  E(P)=\sum\rho(\Omega_{(1)})\,P\,\rho(T(\Omega_{(2)})),
\]
where \(\rho\) is the represented coproduct, \(\Omega\) the canonical
integral, and \(T\) the linear map of arXiv:2204.05940v1. They assert that
the average of the support projection \(P\) is Hermitian, has trace
\(\operatorname{tr}(\rho(1)P)\), and is again the projection onto the MPS
support; the key identity is
\(\sum\Delta(\Omega_{(1)})\Delta(T(\Omega_{(2)}))=\Delta(1)\).

Here the average is defined from the comultiplication of the integral, with
no choice of Sweedler decomposition, at every positive chain length `n`.
The weak-Hopf data supply the ingredients of the boundary average: adjoint
closure of the boundary range, the normalized boundary family obtained from
\(\Delta(\Omega)\), and unit support. For an MPS compatible with the MPO in
the sense of GLM23 `eq:compatible` and injective after blocking some number
of sites, this gives
\[
  E_n(P_n)=P_n,\qquad E_n(I)=Q_n,\qquad E_n(I-P_n)=Q_n-P_n,
\]
with \(Q_n=\rho_n(1)\). The literal average of the parent term \(I-P_n\) is
therefore \(Q_n-P_n\), while the ambient complement \(I-E_n(P_n)\) is the
original parent term \(I-P_n\); the latter is nonzero when \(d^n>D^2\).

The unit-support step \(Q_nP_n=P_n\) uses \(Q_n=I\) only at length one,
where the physical representation is unital. The boundaries whose vectors
\(Q_m\) fixes at every positive length form a two-sided ideal of the bond
matrix algebra, since
\((I\otimes Q_m)Q_{m+1}=Q_{m+1}=(Q_m\otimes I)Q_{m+1}\) and the words of
the blocking length span all matrices; compatibility with the unit boundary
puts a nonzero element in this ideal unless the MPS vanishes.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `eq:compatible`,
  lines 431--469; Section 5, lines 1276--1320; Appendix B, lines 2463--2466.
* Molnár et al., arXiv:2204.05940v1, Section 4 and Section 6.
-/

open scoped Matrix TensorProduct

noncomputable section

namespace MPOTensor.WeakHopfRepresentation

variable {H : Type*} [Ring H] [Algebra ℂ H] [Coalgebra ℂ H] [StarRing H] [StarModule ℂ H]
variable {d D Dₐ L n : ℕ} (W : WeakHopfRepresentation H d D)

/-- The averaging map of GLM23 Appendix B on `n` sites,
\(E_n(P)=\sum\rho_n(\Omega_{(1)})\,P\,\rho_n(T(\Omega_{(2)}))\),
defined from \(\Delta(\Omega)\) itself. Source: arXiv:2203.12563v3,
lines 2463--2466. -/
def weakHopfAverage (n : ℕ)
    (P : Module.End ℂ (EuclideanSpace ℂ (Fin n → Fin d))) :
    Module.End ℂ (EuclideanSpace ℂ (Fin n → Fin d)) :=
  TensorProduct.lift
    (LinearMap.mk₂ ℂ
      (fun x y ↦ Matrix.toEuclideanLin (W.rep n x) * P *
        Matrix.toEuclideanLin (W.rep n (W.pullThrough y)))
      (fun x x' y ↦ by simp only [map_add, add_mul])
      (fun c x y ↦ by simp only [map_smul, smul_mul_assoc])
      (fun x y y' ↦ by simp only [map_add, mul_add])
      (fun c x y ↦ by simp only [map_smul, mul_smul_comm]))
    (Coalgebra.comul W.integral)

/-- Any Sweedler representation of \(\Delta(\Omega)\) computes the average. -/
theorem weakHopfAverage_eq_sum {ι : Type*} (𝓡 : Coalgebra.Repr ℂ W.integral ι)
    (P : Module.End ℂ (EuclideanSpace ℂ (Fin n → Fin d))) :
    W.weakHopfAverage n P = ∑ i ∈ 𝓡.index,
      Matrix.toEuclideanLin (W.rep n (𝓡.left i)) * P *
        Matrix.toEuclideanLin (W.rep n (W.pullThrough (𝓡.right i))) := by
  rw [weakHopfAverage, ← 𝓡.eq, map_sum]
  rfl

/-- The average of the identity is the represented unit,
\(E_n(I)=\rho_n(1)=Q_n\), as stated in GLM23 Appendix B. -/
theorem weakHopfAverage_one (hn : 0 < n) :
    W.weakHopfAverage n 1 = Matrix.toEuclideanLin (W.rep n 1) := by
  let 𝓡 := Coalgebra.Repr.arbitrary ℂ W.integral
  rw [W.weakHopfAverage_eq_sum 𝓡, ← W.sum_rep_mul_rep_pullThrough 𝓡 hn, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_one]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
  rfl

/-- The average is additive in the averaged operator. -/
theorem weakHopfAverage_sub (P P' : Module.End ℂ (EuclideanSpace ℂ (Fin n → Fin d))) :
    W.weakHopfAverage n (P - P') = W.weakHopfAverage n P - W.weakHopfAverage n P' := by
  let 𝓡 := Coalgebra.Repr.arbitrary ℂ W.integral
  simp only [W.weakHopfAverage_eq_sum 𝓡, ← Finset.sum_sub_distrib, mul_sub, sub_mul]

/-! ### Unit support from the module structure of the boundary space -/

omit [StarRing H] [StarModule ℂ H] in
/-- One more site splits off the last physical coefficient through the
comultiplication; the mirror image of `weakHopfRep_succ_apply`. -/
theorem _root_.MPOTensor.weakHopfRep_succ_apply_last
    (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (x : H) (σ τ : Fin (N + 1) → Fin d) :
    weakHopfRep φ (N + 1) x σ τ =
      LinearMap.mul' ℂ ℂ (TensorProduct.map
        (weakHopfCoeff φ (Fin.init σ) (Fin.init τ)).ofConv
        (dualCoefficient φ (σ (Fin.last N)) (τ (Fin.last N))).ofConv (Coalgebra.comul x)) := by
  simp only [weakHopfRep_apply, weakHopfCoeff, List.ofFn_succ', List.prod_concat]
  rfl

omit [Coalgebra ℂ H] [StarRing H] [StarModule ℂ H] in
/-- A linear combination of functionals in the second tensor factor. -/
private theorem sum_mul_mul'_map_right {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (f : H →ₗ[ℂ] ℂ) (g : ι → H →ₗ[ℂ] ℂ) (p : H ⊗[ℂ] H) :
    ∑ i, c i * LinearMap.mul' ℂ ℂ (TensorProduct.map f (g i) p) =
      LinearMap.mul' ℂ ℂ (TensorProduct.map f (∑ i, c i • g i) p) := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]
  | tmul a b =>
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring

omit [Coalgebra ℂ H] [StarRing H] [StarModule ℂ H] in
/-- A linear combination of functionals in the first tensor factor. -/
private theorem sum_mul_mul'_map_left {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (f : H →ₗ[ℂ] ℂ) (g : ι → H →ₗ[ℂ] ℂ) (p : H ⊗[ℂ] H) :
    ∑ i, c i * LinearMap.mul' ℂ ℂ (TensorProduct.map (g i) f p) =
      LinearMap.mul' ℂ ℂ (TensorProduct.map (∑ i, c i • g i) f p) := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]
  | tmul a b =>
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The represented unit is a left unit for the coefficient functionals:
\(\sum_\tau(Q_n)_{\sigma\tau}f_{\tau\upsilon}=f_{\sigma\upsilon}\), by
multiplicativity of \(\rho_n\) at positive length. -/
private theorem sum_smul_weakHopfCoeff (hn : 0 < n) (σ υ : Fin n → Fin d) :
    ∑ τ, weakHopfRep W.phys.toLinearMap n 1 σ τ •
        (weakHopfCoeff W.phys.toLinearMap τ υ).ofConv =
      (weakHopfCoeff W.phys.toLinearMap σ υ).ofConv := by
  ext y
  have hy := congrArg (fun M ↦ M σ υ) (W.rep_mul hn 1 y)
  simp only [one_mul, Matrix.mul_apply, rep, weakHopfRep_apply] at hy
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, weakHopfRep_apply]
  exact hy.symm

/-- A vector fixed by \(Q_{n+1}\) restricts to a vector fixed by \(Q_n\) when
the first site is set to `j`: in the represented algebra
\((I\otimes Q_n)Q_{n+1}=Q_{n+1}\). -/
theorem rep_one_mulVec_cons (hn : 0 < n) {v : (Fin (n + 1) → Fin d) → ℂ}
    (hv : W.rep (n + 1) 1 *ᵥ v = v) (j : Fin d) :
    W.rep n 1 *ᵥ (fun σ ↦ v (Fin.cons j σ)) = fun σ ↦ v (Fin.cons j σ) := by
  have key : ∀ (σ : Fin n → Fin d) (υ : Fin (n + 1) → Fin d),
      ∑ τ, W.rep n 1 σ τ * W.rep (n + 1) 1 (Fin.cons j τ) υ =
        W.rep (n + 1) 1 (Fin.cons j σ) υ := by
    intro σ υ
    simp only [rep, weakHopfRep_succ_apply, Fin.cons_zero, Fin.tail_cons]
    rw [sum_mul_mul'_map_right, W.sum_smul_weakHopfCoeff hn]
  have hv' : ∀ τ, ∑ υ, W.rep (n + 1) 1 τ υ * v υ = v τ := fun τ ↦ congrFun hv τ
  funext σ
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ τ, W.rep n 1 σ τ * v (Fin.cons j τ)
      = ∑ τ, W.rep n 1 σ τ * ∑ υ, W.rep (n + 1) 1 (Fin.cons j τ) υ * v υ := by
        simp only [hv']
    _ = ∑ υ, (∑ τ, W.rep n 1 σ τ * W.rep (n + 1) 1 (Fin.cons j τ) υ) * v υ := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ = v (Fin.cons j σ) := by simp only [key, hv']

/-- A vector fixed by \(Q_{n+1}\) restricts to a vector fixed by \(Q_n\) when
the last site is set to `j`: in the represented algebra
\((Q_n\otimes I)Q_{n+1}=Q_{n+1}\). -/
theorem rep_one_mulVec_snoc (hn : 0 < n) {v : (Fin (n + 1) → Fin d) → ℂ}
    (hv : W.rep (n + 1) 1 *ᵥ v = v) (j : Fin d) :
    W.rep n 1 *ᵥ (fun σ ↦ v (Fin.snoc (α := fun _ ↦ Fin d) σ j)) =
      fun σ ↦ v (Fin.snoc (α := fun _ ↦ Fin d) σ j) := by
  have key : ∀ (σ : Fin n → Fin d) (υ : Fin (n + 1) → Fin d),
      ∑ τ, W.rep n 1 σ τ * W.rep (n + 1) 1 (Fin.snoc (α := fun _ ↦ Fin d) τ j) υ =
        W.rep (n + 1) 1 (Fin.snoc (α := fun _ ↦ Fin d) σ j) υ := by
    intro σ υ
    simp only [rep, weakHopfRep_succ_apply_last, Fin.init_snoc, Fin.snoc_last]
    rw [sum_mul_mul'_map_left, W.sum_smul_weakHopfCoeff hn]
  have hv' : ∀ τ, ∑ υ, W.rep (n + 1) 1 τ υ * v υ = v τ := fun τ ↦ congrFun hv τ
  funext σ
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ τ, W.rep n 1 σ τ * v (Fin.snoc (α := fun _ ↦ Fin d) τ j)
      = ∑ τ, W.rep n 1 σ τ *
          ∑ υ, W.rep (n + 1) 1 (Fin.snoc (α := fun _ ↦ Fin d) τ j) υ * v υ := by
        simp only [hv']
    _ = ∑ υ, (∑ τ, W.rep n 1 σ τ *
          W.rep (n + 1) 1 (Fin.snoc (α := fun _ ↦ Fin d) τ j) υ) * v υ := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ = v (Fin.snoc (α := fun _ ↦ Fin d) σ j) := by simp only [key, hv']

/-- Setting the first site to `j` moves the letter \(A^j\) to the right of
the boundary: \(\Gamma_{n+1}(Z)(j\sigma)=\Gamma_n(ZA^j)(\sigma)\). -/
private theorem groundSpaceMap_cons (A : MPSTensor d Dₐ) (Z : Matrix (Fin Dₐ) (Fin Dₐ) ℂ)
    (j : Fin d) (σ : Fin n → Fin d) :
    MPSTensor.groundSpaceMap A (n + 1) Z (Fin.cons j σ) =
      MPSTensor.groundSpaceMap A n (Z * A j) σ := by
  simp only [MPSTensor.groundSpaceMap_apply, List.ofFn_cons, Kraus.evalWord_cons]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- Setting the last site to `j` moves the letter \(A^j\) to the left of
the boundary: \(\Gamma_{n+1}(Z)(\sigma j)=\Gamma_n(A^jZ)(\sigma)\). -/
private theorem groundSpaceMap_snoc (A : MPSTensor d Dₐ) (Z : Matrix (Fin Dₐ) (Fin Dₐ) ℂ)
    (j : Fin d) (σ : Fin n → Fin d) :
    MPSTensor.groundSpaceMap A (n + 1) Z (Fin.snoc (α := fun _ ↦ Fin d) σ j) =
      MPSTensor.groundSpaceMap A n (A j * Z) σ := by
  simp only [MPSTensor.groundSpaceMap_apply, List.ofFn_succ', Fin.snoc_castSucc,
    Fin.snoc_last, List.concat_eq_append, Kraus.evalWord_append, Kraus.evalWord_cons,
    Kraus.evalWord_nil, Matrix.mul_one, Matrix.mul_assoc]

/-- The represented unit fixes every boundary vector of a compatible state
tensor that is injective after blocking: \(Q_n\psi^n_{A,X}=\psi^n_{A,X}\) at
every positive length, with \(Q_n=\rho_n(1)\).

The boundaries `Z` with \(Q_m\Gamma_m(Z)=\Gamma_m(Z)\) for all \(m>0\) form
a subspace. Because \((I\otimes Q_m)Q_{m+1}=Q_{m+1}=(Q_m\otimes I)Q_{m+1}\),
it is stable under multiplication by every letter on either side, hence,
by block injectivity, a two-sided ideal of the full matrix algebra.
Compatibility with the unit boundary and idempotence of \(Q_m\) put in it,
for each `X`, a boundary agreeing with `X` at one site, where \(Q_1=I\).
So the ideal is everything, unless every one-site vector vanishes, in which
case every boundary vector vanishes. This is the unit-support step of the
projection claim of GLM23 Appendix B, lines 2463--2466, for an MPS
compatible with the MPO as in `eq:compatible`. -/
theorem rep_one_mulVec_mpvWithBoundary {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsNBlkInjective A L)
    (X : Matrix (Fin Dₐ) (Fin Dₐ) ℂ) (hn : 0 < n) :
    W.rep n 1 *ᵥ MPSTensor.mpvWithBoundary A X =
      (MPSTensor.mpvWithBoundary A X : (Fin n → Fin d) → ℂ) := by
  let F : Submodule ℂ (Matrix (Fin Dₐ) (Fin Dₐ) ℂ) :=
    { carrier := {Z | ∀ m, 0 < m →
        W.rep m 1 *ᵥ MPSTensor.groundSpaceMap A m Z = MPSTensor.groundSpaceMap A m Z}
      add_mem' := fun {Z Z'} hZ hZ' m hm ↦ by
        rw [map_add, Matrix.mulVec_add, hZ m hm, hZ' m hm]
      zero_mem' := fun m _ ↦ by rw [map_zero, Matrix.mulVec_zero]
      smul_mem' := fun c Z hZ m hm ↦ by
        rw [map_smul, Matrix.mulVec_smul, hZ m hm] }
  have hright : ∀ Z ∈ F, ∀ j, Z * A j ∈ F := by
    intro Z hZ j m hm
    have := W.rep_one_mulVec_cons hm (hZ (m + 1) m.succ_pos) j
    simpa only [groundSpaceMap_cons] using this
  have hleft : ∀ Z ∈ F, ∀ j, A j * Z ∈ F := by
    intro Z hZ j m hm
    have := W.rep_one_mulVec_snoc hm (hZ (m + 1) m.succ_pos) j
    simpa only [groundSpaceMap_snoc] using this
  have hwordR : ∀ (w : List (Fin d)) (Z : Matrix (Fin Dₐ) (Fin Dₐ) ℂ), Z ∈ F →
      Z * Kraus.evalWord A w ∈ F := by
    intro w
    induction w with
    | nil => intro Z hZ; simpa using hZ
    | cons i w ih =>
      intro Z hZ
      rw [Kraus.evalWord_cons, ← Matrix.mul_assoc]
      exact ih _ (hright Z hZ i)
  have hwordL : ∀ (w : List (Fin d)) (Z : Matrix (Fin Dₐ) (Fin Dₐ) ℂ), Z ∈ F →
      Kraus.evalWord A w * Z ∈ F := by
    intro w
    induction w with
    | nil => intro Z hZ; simpa using hZ
    | cons i w ih =>
      intro Z hZ
      rw [Kraus.evalWord_cons, Matrix.mul_assoc]
      exact hleft _ (ih Z hZ) i
  have hspan : ∀ M : Matrix (Fin Dₐ) (Fin Dₐ) ℂ, M ∈ Submodule.span ℂ
      (Set.range fun σ : Fin L → Fin d ↦ Kraus.evalWord A (List.ofFn σ)) := by
    intro M
    rw [hInj.span_eq_top]
    exact Submodule.mem_top
  have hmul : ∀ M N Z : Matrix (Fin Dₐ) (Fin Dₐ) ℂ, Z ∈ F → M * Z * N ∈ F := by
    intro M N Z hZ
    have hMZ : M * Z ∈ F := by
      induction hspan M using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨σ, rfl⟩ := hx
        exact hwordL _ Z hZ
      | zero => simp
      | add x y _ _ hx hy => simpa [Matrix.add_mul] using F.add_mem hx hy
      | smul c x _ hx => simpa [Matrix.smul_mul] using F.smul_mem c hx
    induction hspan N using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨σ, rfl⟩ := hx
      exact hwordR _ _ hMZ
    | zero => simp
    | add x y _ _ hx hy => simpa [Matrix.mul_add] using F.add_mem hx hy
    | smul c x _ hx => simpa [Matrix.mul_smul] using F.smul_mem c hx
  have hcompat : ∀ Y, ∃ Z ∈ F,
      MPSTensor.groundSpaceMap A 1 Z = MPSTensor.groundSpaceMap A 1 Y := by
    intro Y
    obtain ⟨Z, hZ⟩ := h (W.boundary 1) Y
    simp only [mpoWithBoundary_boundary, MPSTensor.mpvWithBoundary_eq_groundSpaceMap] at hZ
    refine ⟨Z, fun m hm ↦ ?_, ?_⟩
    · rw [← hZ m hm, Matrix.mulVec_mulVec, ← W.rep_mul hm, one_mul]
    · rw [← hZ 1 Nat.one_pos, W.rep_one_length_one, Matrix.one_mulVec]
  rw [MPSTensor.mpvWithBoundary_eq_groundSpaceMap]
  suffices hX : X ∈ F from hX n hn
  by_cases hF : ∃ Z ∈ F, Z ≠ 0
  · obtain ⟨Z, hZ, hZ0⟩ := hF
    obtain ⟨c, e, hce⟩ : ∃ c e, Z c e ≠ 0 := by
      by_contra hc
      exact hZ0 (Matrix.ext fun c e ↦ not_not.mp fun hce ↦ hc ⟨c, e, hce⟩)
    rw [Matrix.matrix_eq_sum_single X]
    refine Submodule.sum_mem _ fun a _ ↦ Submodule.sum_mem _ fun b _ ↦ ?_
    have hab : Matrix.single a b (X a b) =
        Matrix.single a c (X a b / Z c e) * Z * Matrix.single e b 1 := by
      rw [Matrix.single_mul_mul_single, mul_one, div_mul_cancel₀ _ hce]
    rw [hab]
    exact hmul _ _ _ hZ
  · replace hF : ∀ Z ∈ F, Z = 0 := fun Z hZ ↦ not_not.mp fun hZ0 ↦ hF ⟨Z, hZ, hZ0⟩
    have h1 : ∀ Y, MPSTensor.groundSpaceMap A 1 Y = 0 := by
      intro Y
      obtain ⟨Z, hZ, hZY⟩ := hcompat Y
      rw [← hZY, hF Z hZ, map_zero]
    have hall : ∀ (m : ℕ) (Y : Matrix (Fin Dₐ) (Fin Dₐ) ℂ),
        MPSTensor.groundSpaceMap A (m + 1) Y = 0 := by
      intro m
      induction m with
      | zero => exact h1
      | succ m ih =>
        intro Y
        funext τ
        rw [← Fin.cons_self_tail τ, groundSpaceMap_cons, ih]
        rfl
    intro m hm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    rw [hall, Matrix.mulVec_zero]

attribute [local instance] MPSTensor.groundSpaceES_hasOrthogonalProjection

/-- The represented unit fixes the MPS support, \(Q_nP_n=P_n\), for a
compatible state tensor injective after blocking. -/
theorem toEuclideanLin_rep_one_comp_starProjection {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsNBlkInjective A L) (hn : 0 < n) :
    Matrix.toEuclideanLin (W.rep n 1) ∘ₗ
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap =
      (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
  apply LinearMap.ext
  intro ψ
  apply (WithLp.linearEquiv 2 ℂ (MPSTensor.NSiteSpace d n)).injective
  change W.rep n 1 *ᵥ
      ((WithLp.linearEquiv 2 ℂ (MPSTensor.NSiteSpace d n))
        ((MPSTensor.groundSpaceES A n).starProjection ψ)) =
      (WithLp.linearEquiv 2 ℂ (MPSTensor.NSiteSpace d n))
        ((MPSTensor.groundSpaceES A n).starProjection ψ)
  obtain ⟨X, hX⟩ := (MPSTensor.mem_groundSpaceES_iff A n _).mp
    (Submodule.starProjection_apply_mem (MPSTensor.groundSpaceES A n) ψ)
  rw [← hX]
  simpa only [MPSTensor.mpvWithBoundary_eq_groundSpaceMap] using
    W.rep_one_mulVec_mpvWithBoundary h hInj X hn

/-- The weak-Hopf average fixes the MPS support projection of a compatible
MPS injective after blocking: \(E_n(P_n)=P_n\) at every positive length.

Adjoint closure of the boundary range, the normalized boundary family, and
the unit support \(Q_nP_n=P_n\) are all derived from the weak-Hopf data.
This is the projection claim of GLM23 Appendix B, lines 2463--2466, for an
MPS compatible with the MPO as in `eq:compatible`; the consequences
Hermiticity and \(\operatorname{tr}E_n(P_n)=\operatorname{tr}(Q_nP_n)\)
follow below. -/
theorem weakHopfAverage_starProjection {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsNBlkInjective A L) (hn : 0 < n) :
    W.weakHopfAverage n (MPSTensor.groundSpaceES A n).starProjection.toLinearMap =
      (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
  let 𝓡 := Coalgebra.Repr.arbitrary ℂ W.integral
  have hstar : ∀ Z : Matrix (Fin D) (Fin D) ℂ, ∃ Z' : Matrix (Fin D) (Fin D) ℂ,
      (mpoWithBoundary W.tensor Z n)ᴴ = mpoWithBoundary W.tensor Z' n := by
    intro Z
    obtain ⟨Z', hZ'⟩ := W.exists_conjTranspose_mpoWithBoundary_eq Z
    exact ⟨Z', hZ' n⟩
  calc W.weakHopfAverage n (MPSTensor.groundSpaceES A n).starProjection.toLinearMap
      = (∑ i ∈ 𝓡.index, Matrix.toEuclideanLin (W.rep n (𝓡.left i)) *
          Matrix.toEuclideanLin (W.rep n (W.pullThrough (𝓡.right i)))) *
          (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
        rw [W.weakHopfAverage_eq_sum 𝓡, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hc := h.groundSpaceES_starProjection_commute_mpoWithBoundary hn hstar
          (W.boundary (W.pullThrough (𝓡.right i)))
        rw [mpoWithBoundary_boundary] at hc
        rw [mul_assoc, hc.eq, ← mul_assoc]
    _ = W.weakHopfAverage n 1 *
          (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
        rw [W.weakHopfAverage_eq_sum 𝓡]
        simp only [mul_one]
    _ = (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
        rw [W.weakHopfAverage_one hn]
        exact W.toEuclideanLin_rep_one_comp_starProjection h hInj hn

/-- The averaged support projection is Hermitian and has trace
\(\operatorname{tr}(Q_nP_n)\), as asserted in GLM23 Appendix B,
lines 2463--2466. -/
theorem isSymmetricProjection_weakHopfAverage_starProjection {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsNBlkInjective A L) (hn : 0 < n) :
    (W.weakHopfAverage n
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap).IsSymmetricProjection ∧
      LinearMap.trace ℂ _ (W.weakHopfAverage n
          (MPSTensor.groundSpaceES A n).starProjection.toLinearMap) =
        LinearMap.trace ℂ _ (Matrix.toEuclideanLin (W.rep n 1) ∘ₗ
          (MPSTensor.groundSpaceES A n).starProjection.toLinearMap) := by
  rw [W.weakHopfAverage_starProjection h hInj hn,
    W.toEuclideanLin_rep_one_comp_starProjection h hInj hn]
  exact ⟨Submodule.isSymmetricProjection_starProjection _, rfl⟩

/-- The literal average of the canonical parent term is
\(E_n(I-P_n)=Q_n-P_n\), which may vanish. Source: arXiv:2203.12563v3,
lines 2463--2466; the distinction from the ambient complement is recorded
in `docs/paper-gaps/glm23_wha_parent_completion.tex`. -/
theorem weakHopfAverage_parentInteractionES {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsNBlkInjective A L) (hn : 0 < n) :
    W.weakHopfAverage n (MPSTensor.parentInteractionES A n) =
      Matrix.toEuclideanLin (W.rep n 1) -
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
  rw [MPSTensor.parentInteractionES, Submodule.starProjection_orthogonal']
  change W.weakHopfAverage n
      (1 - (MPSTensor.groundSpaceES A n).starProjection.toLinearMap) = _
  rw [W.weakHopfAverage_sub, W.weakHopfAverage_one hn,
    W.weakHopfAverage_starProjection h hInj hn]

/-- The ambient complement of the averaged support is the canonical parent
term: \(I-E_n(P_n)=I-P_n\). This is the parent term chosen in GLM23
Appendix B, lines 2463--2466. -/
theorem one_sub_weakHopfAverage_starProjection {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsNBlkInjective A L) (hn : 0 < n) :
    1 - W.weakHopfAverage n (MPSTensor.groundSpaceES A n).starProjection.toLinearMap =
      MPSTensor.parentInteractionES A n := by
  rw [W.weakHopfAverage_starProjection h hInj hn, MPSTensor.parentInteractionES,
    Submodule.starProjection_orthogonal']
  rfl

/-- The symmetrized parent term \(I-E_n(P_n)\) is nonzero when
\(d^n>D^2\), the nonvanishing claim of GLM23 Appendix B, lines 2453--2466,
for the ambient complement. -/
theorem one_sub_weakHopfAverage_starProjection_ne_zero {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsNBlkInjective A L) (hn : 0 < n)
    (hDim : d ^ n > Dₐ ^ 2) :
    1 - W.weakHopfAverage n (MPSTensor.groundSpaceES A n).starProjection.toLinearMap ≠ 0 := by
  rw [W.one_sub_weakHopfAverage_starProjection h hInj hn]
  exact MPSTensor.parentInteractionES_ne_zero A n hDim

/-- The symmetrized parent term commutes with every boundary operator of the
representation, at every positive length. -/
theorem commute_one_sub_weakHopfAverage_mpoWithBoundary {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsNBlkInjective A L) (hn : 0 < n)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Commute (1 - W.weakHopfAverage n (MPSTensor.groundSpaceES A n).starProjection.toLinearMap)
      (Matrix.toEuclideanLin (mpoWithBoundary W.tensor X n)) := by
  rw [W.one_sub_weakHopfAverage_starProjection h hInj hn]
  apply h.parentInteractionES_commute_mpoWithBoundary hn ?_ X
  intro Z
  obtain ⟨Z', hZ'⟩ := W.exists_conjTranspose_mpoWithBoundary_eq Z
  exact ⟨Z', hZ' n⟩

end MPOTensor.WeakHopfRepresentation
