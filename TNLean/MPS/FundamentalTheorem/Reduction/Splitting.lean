/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.LinearAlgebra.DirectSum.Finite
import TNLean.Algebra.BlockDiagonalGauge
import TNLean.MPS.FundamentalTheorem.Reduction.ProjectorWeightedSum
import TNLean.MPS.FundamentalTheorem.Reduction.StarSemisimple

/-!
# The splitting criterion for multi-block compressions

The multi-block asymmetric compression theorem
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7)
produces a block *upper triangular* gauge, hence relations between words of the source tensor and
words of the blocks, but no relation site by site. The exact algebraic criterion for the extension
to split, so that the compression pair becomes a pair of sitewise intertwiners
(`Notes/OpenProblemsTN/strategies/final_resolution/p5_local_zipper_hypotheses.tex`): a fixed
occurrence splits exactly when the corresponding step of the invariant flag is an invariant direct
summand, and semisimplicity of the source module is sufficient for that.

For matrix product operator symmetries with star-closed virtual algebras the resulting sitewise
intertwiners are the fusion tensors of Garre-Rubio, Lootens and Molnar (arXiv:2203.12563).
Anomalous symmetries are exactly the non-split ones: Example D of the P5 note has no nonzero
sitewise intertwiner at all, so its virtual algebra cannot be star-closed.

## Main results

* `MPSTensor.FlagData.exists_invariant_complement`: one step of the flag of a semisimple module
  has an invariant complement inside the next.
* `MPSTensor.FlagData.exists_isInternal_blockCoordinates`: the flag of a semisimple module
  splits as an internal direct sum of invariant subspaces carrying the prescribed blocks.
* `MPSTensor.exists_multiBlockCompression_remainder_eq_zero_of_isSemisimpleModule`: a semisimple
  source admits a multi-block compression with vanishing remainder.
* `MPSTensor.exists_multiBlockCompression_remainder_eq_zero_of_star`: the splitting criterion in
  terms of star closure of the virtual algebra.
* `MPSTensor.exists_fusionTensors_of_star`: the sitewise intertwiners of a split compression.
-/

open scoped Matrix DirectSum

namespace MPSTensor

open WordAlgebra

variable {d DB : ℕ} {ι : Type*} {D : ι → ℕ} [DecidableEq ι]

section Splitting

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
  [IsScalarTower ℂ (WordAlgebra d) M] [FiniteDimensional ℂ M] {S : Finset ι}
  {C : ∀ s, MPSTensor d (D s)}

omit [DecidableEq ι] [FiniteDimensional ℂ M] in
/-- **Splitting one step of the flag**. Over a semisimple module, the step `k` of a labelled
invariant flag has an invariant complement inside the next member of the flag, and that
complement carries the subquotient of the step. -/
theorem FlagData.exists_invariant_complement [IsSemisimpleModule (WordAlgebra d) M]
    (F : FlagData M S C) (k : Fin F.r) :
    ∃ W : Submodule (WordAlgebra d) M,
      F.cflag k.castSucc ⊔ W.restrictScalars ℂ = F.cflag k.succ ∧
      Nonempty (↥(W.restrictScalars ℂ) ≃ₗ[WordAlgebra d] F.step k) := by
  obtain ⟨V, hV⟩ := exists_isCompl ((F.H k.castSucc).comap (F.H k.succ).subtype)
  refine ⟨V.map (F.H k.succ).subtype, le_antisymm (sup_le ?_ ?_) ?_, ⟨?_⟩⟩
  · exact F.cflag_mono k.castSucc_le_succ
  · exact fun x hx => Submodule.map_subtype_le (F.H k.succ) V hx
  · intro x hx
    have hmem : (⟨x, hx⟩ : ↥(F.H k.succ)) ∈
        ((F.H k.castSucc).comap (F.H k.succ).subtype) ⊔ V := by
      rw [codisjoint_iff.1 hV.codisjoint]
      trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
    exact Submodule.mem_sup.2 ⟨(a : M), ha, (b : M), ⟨b, hb, rfl⟩, congrArg Subtype.val hab⟩
  · exact (Submodule.restrictScalarsEquiv ℂ (WordAlgebra d) M _).trans
      ((Submodule.equivMapOfInjective _ (F.H k.succ).injective_subtype V).symm.trans
        (Submodule.quotientEquivOfIsCompl _ V hV).symm)

omit [DecidableEq ι] in
/-- **The split flag of a semisimple module**. The steps of a labelled invariant flag of a
semisimple module are carried by invariant subspaces whose internal direct sum is the whole
module, in coordinates turning every one-letter action into the prescribed diagonal block. -/
theorem FlagData.exists_isInternal_blockCoordinates [IsSemisimpleModule (WordAlgebra d) M]
    (F : FlagData M S C) :
    ∃ (W : Fin F.r → Submodule ℂ M)
      (hmaps : ∀ (i : Fin d) (k : Fin F.r), Set.MapsTo (actAlgHom M (ofWord [i])) (W k) (W k))
      (ψ : ∀ k, ↥(W k) ≃ₗ[ℂ] (Fin (slotSize D (F.label k)) → ℂ)),
      DirectSum.IsInternal W ∧ ∀ (i : Fin d) (k : Fin F.r),
        LinearMap.toMatrix' ((ψ k).conj ((actAlgHom M (ofWord [i])).restrict (hmaps i k))) =
          blockOf D C i (F.label k) := by
  classical
  choose V hVsup hViso using F.exists_invariant_complement
  set W : Fin F.r → Submodule ℂ M := fun k => (V k).restrictScalars ℂ with hWdef
  have hmaps : ∀ (i : Fin d) (k : Fin F.r),
      Set.MapsTo (actAlgHom M (ofWord [i])) (W k) (W k) :=
    fun _ k _ hx => (V k).smul_mem _ hx
  have hcoord : ∀ k : Fin F.r, ∃ ψ : ↥(W k) ≃ₗ[ℂ] (Fin (slotSize D (F.label k)) → ℂ),
      ∀ i : Fin d, LinearMap.toMatrix' (ψ.conj (actAlgHom (↥(W k)) (ofWord [i]))) =
        blockOf D C i (F.label k) :=
    fun k => F.exists_blockCoordinates_of_equiv k (hViso k).some
  choose ψ hψ using hcoord
  -- The flag is exhausted by the complements, so they span the module.
  have hiSup : ⨆ k, W k = ⊤ := by
    have key : ∀ l : Fin (F.r + 1), F.cflag l ≤ ⨆ k, W k := by
      intro l
      induction l using Fin.induction with
      | zero => rw [F.cflag_zero]; exact bot_le
      | succ k ih => rw [← hVsup k]; exact sup_le ih (le_iSup W k)
    have := key (Fin.last F.r)
    rwa [F.cflag_last, top_le_iff] at this
  -- The dimensions of the complements add up to the dimension of the module.
  choose ψ₀ _hψ₀ using F.exists_blockCoordinates
  have hfin : ∀ k, Module.finrank ℂ ↥(W k) = slotSize D (F.label k) := by
    intro k
    rw [(ψ k).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hdim : Module.finrank ℂ (⨁ k, ↥(W k)) = Module.finrank ℂ M := by
    rw [Module.finrank_directSum, finrank_eq_sum_of_flag F.cflag F.cflag_zero F.cflag_last
      F.cflag_mono (fun k => slotSize D (F.label k)) ψ₀]
    exact Finset.sum_congr rfl fun k _ => hfin k
  have hsurj : Function.Surjective (DirectSum.coeLinearMap W) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, hiSup]
  have hrestrict : ∀ (i : Fin d) (k : Fin F.r),
      (actAlgHom M (ofWord [i])).restrict (hmaps i k) = actAlgHom (↥(W k)) (ofWord [i]) :=
    fun _ _ => LinearMap.ext fun _ => rfl
  refine ⟨W, hmaps, ψ,
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj, hsurj⟩,
    fun i k => ?_⟩
  rw [hrestrict i k]
  exact hψ k i

end Splitting

section Compression

open WordAlgebra in
/-- **The splitting criterion, semisimple form**. A tensor whose positive-length word traces are
the sums of the word traces of a finite family of normal blocks of positive bond dimension, and
whose word module is semisimple, admits a multi-block compression whose remainder vanishes: the
gauged one-site matrices are block *diagonal* (P5 note, Theorem 7.7 together with
`Notes/OpenProblemsTN/strategies/final_resolution/p5_local_zipper_hypotheses.tex`,
`thm:p5-local-semisimple-sufficient`). -/
theorem exists_multiBlockCompression_remainder_eq_zero_of_isSemisimpleModule (S : Finset ι)
    (C : ∀ s, MPSTensor d (D s)) (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (B : MPSTensor d DB)
    (htr : ∀ w : List (Fin d), w ≠ [] →
      Matrix.trace (Kraus.evalWord B w) = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w))
    [IsSemisimpleModule (WordAlgebra d) B.WordModule] :
    ∃ P : MultiBlockCompression B S C, P.remainder = 0 := by
  classical
  obtain ⟨F⟩ := exists_flagData C hC hD B.WordModule
    fun w hw => by rw [traceWord_wordModule]; exact htr w hw
  set lab : Fin F.r ≃ BlockIndex S F.z := Equiv.ofBijective F.label F.label_bijective with hlab
  have hr : F.r = S.card + F.z := by
    simpa [Fintype.card_sum] using Fintype.card_congr lab
  set ord : BlockIndex S F.z ≃ Fin (S.card + F.z) := lab.symm.trans (finCongr hr) with hord
  obtain ⟨W, hmaps, ψ, hinternal, hblocks⟩ := F.exists_isInternal_blockCoordinates
  obtain ⟨e, he⟩ := exists_linearEquiv_blockDiagonal_of_isInternal hinternal
    (fun k => slotSize D (F.label k)) ψ (fun i => actAlgHom B.WordModule (ofWord [i])) hmaps
  set σ : ((k : Fin F.r) × Fin (slotSize D (F.label k))) ≃ BlockSpace D S F.z :=
    Equiv.sigmaCongrLeft (β := fun b : BlockIndex S F.z => Fin (slotSize D b)) lab with hσ
  set gauge : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S F.z → ℂ) :=
    (B.wordRep.asModuleEquiv.symm.trans e).trans (LinearEquiv.funCongrLeft ℂ ℂ σ.symm) with hgauge
  -- In the split coordinates every one-site matrix is block diagonal with the prescribed blocks.
  have hall : ∀ i, conjMatrix gauge (B i) =
      (Matrix.blockDiagonal' fun k => blockOf D C i (F.label k)).submatrix σ.symm σ.symm := by
    intro i
    have hfi : B.wordRep.asModuleEquiv.symm.conj (Matrix.toLin' (B i)) =
        actAlgHom B.WordModule (ofWord [i]) := by
      rw [MPSTensor.actAlgHom_wordModule_ofWord B [i]]
      simp [Kraus.evalWord]
    rw [conjMatrix_apply, hgauge,
      show ((B.wordRep.asModuleEquiv.symm.trans e).trans
          (LinearEquiv.funCongrLeft ℂ ℂ σ.symm)).conj (Matrix.toLin' (B i)) =
        (LinearEquiv.funCongrLeft ℂ ℂ σ.symm).conj
          (e.conj (B.wordRep.asModuleEquiv.symm.conj (Matrix.toLin' (B i)))) from rfl,
      hfi, toMatrix'_conj_funCongrLeft, he i]
    exact congrArg (fun T => Matrix.submatrix T σ.symm σ.symm)
      (congrArg Matrix.blockDiagonal' (funext fun k => hblocks i k))
  have hfst : ∀ b : BlockSpace D S F.z, (σ.symm b).1 = lab.symm b.1 := fun _ => rfl
  have hoff : ∀ (i : Fin d) (x y : BlockSpace D S F.z), x.1 ≠ y.1 →
      conjMatrix gauge (B i) x y = 0 := by
    intro i x y hne
    rw [hall i, Matrix.submatrix_apply, Matrix.blockDiagonal'_apply]
    refine dite_eq_right fun h => hne ?_
    rw [hfst x, hfst y] at h
    exact lab.symm.injective h
  have htriangular : ∀ i, (conjMatrix gauge (B i)).BlockTriangular fun x => ord x.1 := by
    intro i x y hlt
    refine hoff i x y fun h => absurd hlt ?_
    change ¬ ord y.1 < ord x.1
    rw [h]
    exact lt_irrefl _
  have hblockdiag : ∀ (i : Fin d) (b : BlockIndex S F.z),
      (conjMatrix gauge (B i)).blockDiag' b = blockOf D C i b := by
    intro i b
    obtain ⟨k, rfl⟩ := F.label_bijective.2 b
    have hx : ∀ p : Fin (slotSize D (F.label k)),
        σ.symm ⟨F.label k, p⟩ = (⟨k, p⟩ : (k : Fin F.r) × Fin (slotSize D (F.label k))) :=
      fun p => σ.symm_apply_apply ⟨k, p⟩
    ext p q
    rw [Matrix.blockDiag'_apply, hall i, Matrix.submatrix_apply, hx p, hx q,
      Matrix.blockDiagonal'_apply_eq]
  let P : MultiBlockCompression B S C :=
    { z := F.z
      ord := ord
      gauge := gauge
      triangular := htriangular
      matched := fun i s => hblockdiag i (Sum.inl s)
      unmatched := fun i t => hblockdiag i (Sum.inr t) }
  refine ⟨P, ?_⟩
  funext i
  change P.remainder i = 0
  refine conjMatrix_injective gauge ?_
  have hrem : conjMatrix gauge (P.remainder i) = conjMatrix gauge (B i) -
      Matrix.blockDiagonal' (conjMatrix gauge (B i)).blockDiag' := P.conjMatrix_remainder i
  rw [hrem, conjMatrix_zero, sub_eq_zero]
  ext x y
  rcases eq_or_ne x.1 y.1 with hxy | hxy
  · obtain ⟨bx, px⟩ := x
    obtain ⟨by', py⟩ := y
    cases hxy
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiag'_apply]
  · obtain ⟨bx, px⟩ := x
    obtain ⟨by', py⟩ := y
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hxy, hoff i _ _ hxy]

/-- **The splitting criterion, star-closed form**. If the conjugate transpose of every one-site
matrix of the source lies in the algebra generated by the one-site matrices, the multi-block
compression of Theorem 7.7 can be chosen with vanishing remainder, so that the source is the
direct sum of the blocks and the zero slots
(`Notes/OpenProblemsTN/strategies/final_resolution/p5_local_zipper_hypotheses.tex`,
`thm:p5-local-adjoint-closure`). The hypothesis here asks only that the conjugate transpose of
every generator lie in the generated algebra, which is equivalent to the closure of the whole
generated algebra under conjugate transposition used in the source. -/
theorem exists_multiBlockCompression_remainder_eq_zero_of_star (S : Finset ι)
    (C : ∀ s, MPSTensor d (D s)) (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (B : MPSTensor d DB)
    (htr : ∀ w : List (Fin d), w ≠ [] →
      Matrix.trace (Kraus.evalWord B w) = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w))
    (hstar : ∀ i, (B i)ᴴ ∈ Algebra.adjoin ℂ (Set.range B)) :
    ∃ P : MultiBlockCompression B S C, P.remainder = 0 := by
  have := B.isSemisimpleModule_wordModule_of_conjTranspose_mem_adjoin hstar
  exact exists_multiBlockCompression_remainder_eq_zero_of_isSemisimpleModule S C hC hD B htr

omit [DecidableEq ι] in
/-- **Sitewise fusion tensors from star closure**. When the virtual algebra of the source is
closed under conjugate transposition, the word-level compression pairs of Theorem 7.7 become
sitewise intertwiners: `B^i V_s = V_s C_s^i` and `W_s B^i = C_s^i W_s`, with `W_s V_s = 1` and
`W_s V_t = 0` for `s` distinct from `t`. For a matrix product operator symmetry these are the
fusion tensors of Garre-Rubio, Lootens and Molnar (arXiv:2203.12563); the biorthogonal zipper
family is the conclusion of
`Notes/OpenProblemsTN/strategies/final_resolution/p5_local_zipper_hypotheses.tex`,
`thm:p5-local-adjoint-closure`. -/
theorem exists_fusionTensors_of_star (S : Finset ι) (C : ∀ s, MPSTensor d (D s))
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s) (B : MPSTensor d DB)
    (htr : ∀ w : List (Fin d), w ≠ [] →
      Matrix.trace (Kraus.evalWord B w) = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w))
    (hstar : ∀ i, (B i)ᴴ ∈ Algebra.adjoin ℂ (Set.range B)) :
    ∃ (left : ∀ s : {s // s ∈ S}, Matrix (Fin (D s.1)) (Fin DB) ℂ)
      (right : ∀ s : {s // s ∈ S}, Matrix (Fin DB) (Fin (D s.1)) ℂ),
      (∀ s, MPSTensor.IsReduction B (C s.1) (left s) (right s)) ∧
      (∀ (i : Fin d) (s : {s // s ∈ S}), B i * right s = right s * C s.1 i) ∧
      (∀ (i : Fin d) (s : {s // s ∈ S}), left s * B i = C s.1 i * left s) ∧
      (∀ s t : {s // s ∈ S}, s ≠ t → left s * right t = 0) := by
  classical
  obtain ⟨P, hP⟩ :=
    exists_multiBlockCompression_remainder_eq_zero_of_star S C hC hD B htr hstar
  exact ⟨P.left, P.right, P.isReduction, fun i s => P.mul_right_eq_right_mul hP i s,
    fun i s => P.left_mul_eq_mul_left hP i s, fun _ _ h => P.left_mul_right_of_ne h⟩

omit [DecidableEq ι] in
/-- **The anomaly converse**. If one of the blocks admits no nonzero sitewise right intertwiner
with the source, then the virtual algebra of the source is not closed under conjugate
transposition. This is the algebraic trace of an anomalous symmetry: the compression exists at
the level of words but never site by site (P5 note, the remark "Exact algebraic zipper
criterion" of `Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`). -/
theorem not_forall_conjTranspose_mem_adjoin_of_forall_right_intertwiner_eq_zero (S : Finset ι)
    (C : ∀ s, MPSTensor d (D s)) (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (B : MPSTensor d DB)
    (htr : ∀ w : List (Fin d), w ≠ [] →
      Matrix.trace (Kraus.evalWord B w) = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w))
    (s : {s // s ∈ S})
    (hno : ∀ X : Matrix (Fin DB) (Fin (D s.1)) ℂ, (∀ i, B i * X = X * C s.1 i) → X = 0) :
    ¬ ∀ i, (B i)ᴴ ∈ Algebra.adjoin ℂ (Set.range B) := by
  classical
  intro hstar
  obtain ⟨P, hP⟩ :=
    exists_multiBlockCompression_remainder_eq_zero_of_star S C hC hD B htr hstar
  have hzero := hno (P.right s) fun i => P.mul_right_eq_right_mul hP i s
  have hone : P.left s * P.right s = 1 := P.left_mul_right_self s
  rw [hzero, Matrix.mul_zero] at hone
  have : Nonempty (Fin (D s.1)) := ⟨⟨0, hD s.1 s.2⟩⟩
  exact zero_ne_one hone

end Compression

end MPSTensor
