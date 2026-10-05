/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryZipperUniqueness
import TNLean.MPS.FundamentalTheorem.Reduction.MPOProduct
import TNLean.MPS.Symmetry.MPOSymmetry.NIMRep

/-!
# Fusion and action multiplicities from arbitrary-boundary tensors

Tracing the exact biorthogonal decompositions gives the periodic fusion and
action expansions with their actual natural-number multiplicities. A common
simultaneous word span gives linear independence of the periodic target
blocks at that length. Physical operator associativity then gives fusion
associativity, and the existing periodic-action comparison gives the NIM
relation for those same multiplicities.

No unit, duality, commutativity, or fusion-category structure is asserted.
All coefficient identities concern the original unblocked tensors.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `algcond`,
  `fusiontensors`, `eq:compatible`, `fusiontensors2`, Appendix A,
  and the multiplicity equations at lines 564--568.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Exact biorthogonal synthesis gives the periodic vector expansion with
its actual integer multiplicities. Source: GLM23 Appendix A and lines 567--568. -/
theorem IsBiorthogonalDecomposition.mpv_eq_sum_multiplicity
    {ι : Type*} [Fintype ι] {d DB : ℕ} {D N : ι → ℕ}
    {B : MPSTensor d DB} {A : ∀ c, MPSTensor d (D c)}
    {V : ∀ c, Fin (N c) → Matrix (Fin (D c)) (Fin DB) ℂ}
    {W : ∀ c, Fin (N c) → Matrix (Fin DB) (Fin (D c)) ℂ}
    (h : IsBiorthogonalDecomposition B
      (fun q : (c : ι) × Fin (N c) ↦ A q.1)
      (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2))
    {L : ℕ} (hL : 0 < L) (w : Fin L → Fin d) :
    mpv B w = ∑ c, (N c : ℂ) * mpv (A c) w := by
  exact h.trace_evalWord_eq_sum_multiplicity (List.ofFn w)
    (by rw [Ne, List.ofFn_eq_nil_iff]; omega)

/-- Positive-dimensional blocks with simultaneous word spanning have
linearly independent periodic vectors at that same length. -/
theorem WordTupleSpanTop.linearIndependent_mpv
    {d g : ℕ} {D : Fin g → ℕ} {A : ∀ c, MPSTensor d (D c)}
    {L : ℕ} (hSpan : WordTupleSpanTop A L) (hD : ∀ c, 0 < D c) :
    LinearIndependent ℂ (fun c ↦ fun w : Fin L → Fin d ↦ mpv (A c) w) := by
  apply Fintype.linearIndependent_iff.2
  intro z hz c
  have hzero := block_matrices_eq_zero_of_wordTupleSpanTop_trace A hSpan
    (fun c ↦ z c • (1 : Matrix (Fin (D c)) (Fin (D c)) ℂ)) (fun w ↦ by
      have hw := congrFun hz w
      simpa [Finset.sum_apply, mpv, coeff, Matrix.smul_mul, Matrix.trace_smul,
        smul_eq_mul] using hw)
  have hc := congrArg (fun X ↦ X ⟨0, hD c⟩ ⟨0, hD c⟩) (hzero c)
  simpa using hc

end MPSTensor

namespace MPOTensor

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {O : ∀ a, MPOTensor d (χ a)} {A : ∀ x, MPSTensor d (D x)}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

/-- Tracing exact pairwise fusion decompositions gives the existing periodic
fusion-algebra predicate with the same natural-number multiplicities.
Source: GLM23 `fusiontensors` and the ensuing periodic fusion equation. -/
theorem isMPOFusionAlgebra_of_biorthogonalDecompositions
    (V : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
    (W : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
    (h : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ V a b q.1 q.2) (fun q ↦ W a b q.1 q.2)) :
    IsMPOFusionAlgebra O N := by
  intro a b L hL
  rw [← mpo_mulTensor]
  ext σ τ
  have hh := (h a b).mpv_eq_sum_multiplicity hL
    (fun n ↦ finProdFinEquiv (σ n, τ n))
  simpa [mpv_toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul] using hh

/-- Tracing exact action decompositions gives the existing periodic symmetry
predicate with the same natural-number multiplicities. Source: GLM23
`fusiontensors2` and lines 567--568. -/
theorem isMPOSymmetricFamily_of_biorthogonalDecompositions
    (V : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
    (W : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
    (h : ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
        (fun q ↦ V a x q.1 q.2) (fun q ↦ W a x q.1 q.2)) :
    IsMPOSymmetricFamily O A (fun a x y ↦ (M a x y : ℂ)) := by
  intro a x L hL
  rw [mpo_mulVec_mpv]
  funext w
  exact (h a x).mpv_eq_sum_multiplicity hL w

/-- State-block separation turns the periodic fusion and action expansions
into the NIM relation for the specified natural coefficients. The positive
independent length is derived from the source block assumptions. -/
theorem isNIMRep_of_periodic_expansions_of_isInjective
    (hfus : IsMPOFusionAlgebra O N)
    (hact : IsMPOSymmetricFamily O A (fun a x y ↦ (M a x y : ℂ)))
    (hInj : ∀ x, Kraus.IsInjective (A x)) (hD : ∀ x, 0 < D x)
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv A) : IsNIMRep N M := by
  obtain ⟨L, hL, hSpan⟩ :=
    MPSTensor.exists_positive_wordTupleSpanTop_of_isInjective hInj hD hne
  intro a b x y
  have he := sum_fusion_mul_eq_sum_mul_of_isMPOSymmetricFamily hfus hact hL
    (hSpan.linearIndependent_mpv hD) a b x y
  exact_mod_cast he

/-- A simultaneous span on the doubled physical alphabet gives linear
independence of the periodic block operators. -/
theorem linearIndependent_mpo_of_wordTupleSpanTop
    {L : ℕ} (hSpan : MPSTensor.WordTupleSpanTop (fun a ↦ (O a).toMPSTensor) L)
    (hχ : ∀ a, 0 < χ a) : LinearIndependent ℂ (fun a ↦ mpo (O a) L) := by
  apply Fintype.linearIndependent_iff.2
  intro z hz
  apply Fintype.linearIndependent_iff.1 (hSpan.linearIndependent_mpv hχ) z
  funext w
  have hw := congrArg
    (fun X ↦ X (fun n ↦ (w n).divNat) (fun n ↦ (w n).modNat)) hz
  simpa [mpv_toMPSTensor, Finset.sum_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul] using hw

/-- Associativity of physical operators implies associativity of their
fusion coefficients at any positive length where the operators are linearly
independent. This assertion imposes no unit or duality structure. -/
theorem IsMPOFusionAlgebra.associative_of_linearIndependent
    (hfus : IsMPOFusionAlgebra O N) {L : ℕ} (hL : 0 < L)
    (hli : LinearIndependent ℂ (fun a ↦ mpo (O a) L)) (a b c q : Fin r) :
    ∑ e, N a b e * N e c q = ∑ f, N b c f * N a f q := by
  have hleft : (mpo (O a) L * mpo (O b) L) * mpo (O c) L =
      ∑ q, (∑ e, (N a b e : ℂ) * (N e c q : ℂ)) • mpo (O q) L := by
    rw [hfus a b L hL, Matrix.sum_mul]
    simp_rw [Matrix.smul_mul, hfus _ c L hL, Finset.smul_sum, smul_smul,
      Finset.sum_smul]
    exact Finset.sum_comm
  have hright : mpo (O a) L * (mpo (O b) L * mpo (O c) L) =
      ∑ q, (∑ f, (N b c f : ℂ) * (N a f q : ℂ)) • mpo (O q) L := by
    rw [hfus b c L hL, Matrix.mul_sum]
    simp_rw [Matrix.mul_smul, hfus a _ L hL, Finset.smul_sum, smul_smul,
      Finset.sum_smul]
    exact Finset.sum_comm
  have he := Fintype.linearIndependent_iffₛ.1 hli _ _
    (hleft.symm.trans ((Matrix.mul_assoc _ _ _).trans hright)) q
  exact_mod_cast he

/-- The source block assumptions derive the separating positive length used
to read fusion associativity from physical matrix associativity. -/
theorem IsMPOFusionAlgebra.associative_of_isInjective
    (hfus : IsMPOFusionAlgebra O N)
    (hInj : ∀ a, Kraus.IsInjective (O a).toMPSTensor) (hχ : ∀ a, 0 < χ a)
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor))
    (a b c q : Fin r) :
    ∑ e, N a b e * N e c q = ∑ f, N b c f * N a f q := by
  obtain ⟨L, hL, hSpan⟩ :=
    MPSTensor.exists_positive_wordTupleSpanTop_of_isInjective hInj hχ hne
  exact hfus.associative_of_linearIndependent hL
    (linearIndependent_mpo_of_wordTupleSpanTop hSpan hχ) a b c q

/-- Arbitrary-boundary closedness and compatibility give periodic fusion
and action expansions with natural multiplicities satisfying both fusion
associativity and the NIM relation. All separating lengths and exact tensors
are derived from the source's individual block assumptions.
Source: GLM23 `algcond`, `eq:compatible`, Appendix A, and lines 564--568. -/
theorem IsBoundaryClosed.exists_isNIMRep_of_isBoundaryCompatible
    {T : MPOTensor d (∑ a : Fin r, χ a)}
    {B : MPSTensor d (∑ x : Fin s, D x)} (hT : IsBoundaryClosed T)
    (hB : IsBoundaryCompatible T B)
    (O : ∀ a, MPOTensor d (χ a)) (A : ∀ x, MPSTensor d (D x))
    (hOp : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1)
      (fun a ↦ (O a).toMPSTensor))
    (hState : B = MPSTensor.toTensorFromBlocks (fun _ ↦ 1) A)
    (hInjOp : ∀ a, Kraus.IsInjective (O a).toMPSTensor) (hχ : ∀ a, 0 < χ a)
    (hneOp : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor))
    (hInjState : ∀ x, Kraus.IsInjective (A x)) (hD : ∀ x, 0 < D x)
    (hneState : MPSTensor.BlocksNotGaugePhaseEquiv A) :
    ∃ (N : Fin r → Fin r → Fin r → ℕ) (M : Fin r → Fin s → Fin s → ℕ),
      IsMPOFusionAlgebra O N ∧
      IsMPOSymmetricFamily O A (fun a x y ↦ (M a x y : ℂ)) ∧ IsNIMRep N M ∧
      ∀ a b c q, ∑ e, N a b e * N e c q = ∑ f, N b c f * N a f q := by
  classical
  choose N VF WF hF using
    fun a b ↦ hT.exists_blockFusionDecomposition_of_isInjective
      O hOp hInjOp hχ hneOp a b
  choose M VA WA hA using
    fun a x ↦ hB.exists_blockActionDecomposition_of_isInjective
      O A hOp hState hInjState hD hneState a x
  have hfus := isMPOFusionAlgebra_of_biorthogonalDecompositions VF WF hF
  have hact := isMPOSymmetricFamily_of_biorthogonalDecompositions VA WA hA
  exact ⟨N, M, hfus, hact,
    isNIMRep_of_periodic_expansions_of_isInjective hfus hact hInjState hD hneState,
    hfus.associative_of_isInjective hInjOp hχ hneOp⟩

end MPOTensor
