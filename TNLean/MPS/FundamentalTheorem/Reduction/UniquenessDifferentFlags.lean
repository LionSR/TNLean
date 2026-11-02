/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.IrreducibleTensor

/-!
# Two reductions with different flags

Let `P` and `Q` be two multi-block compressions of the same tensor `B`, onto normal blocks of
positive bond dimension, with flags `M_k` and `M'_{k'}`, reading maps `W_b`, `W'_{b'}` and
injections `V_b`, `V'_{b'}`. Fix a position `k` of `P` carrying the slot `b`, and let the matched
position `k'` of `Q` carry the slot `b'`. With
$$U = M_k ∩ M'_{k'},\qquad N = M_{k-1} + M'_{k'-1},$$
there is a unique intertwiner `X`, `X C_b^i = C'_{b'}^i X`, with `W'_{b'} x = X W_b x` for every
`x ∈ U`; it is invertible, and with `Y = X⁻¹` the difference `V'_{b'} - V_b Y` takes values in `N`.
On a pair of zero slots, and on a pair of block slots with the same label of the same family, `X` is
a nonzero scalar `λ`: `W'_{b'} = λ W_b` on `U`, and `V'_{b'} ≡ λ⁻¹ V_b` modulo `N` (blueprint
`thm:asym_uniq_different_flags`, *Two compressions with different flags*).

The proof compares two linear maps on `U` with the same kernel: `W_b` and `W'_{b'}` both map `U`
onto the coordinates of their slots, because `M_{k-1} + U = M_k` and `M'_{k'-1} + U = M'_{k'}`, and
both have kernel `K = U ∩ M_{k-1} = U ∩ M'_{k'-1}` (blueprint `prop:asym_uniq_matching`, *The
matching*).

## Main results

* `MPSTensor.MultiBlockCompression.exists_intertwiner_of_matching`: *Two compressions with different
  flags*, existence of the invertible intertwiner, the comparison of the reading maps on `U`, and of
  the injections modulo `N`.
* `MPSTensor.MultiBlockCompression.existsUnique_intertwiner_of_matching`: *Two compressions with
  different flags*, uniqueness of the intertwiner.
* `MPSTensor.MultiBlockCompression.exists_smul_of_matching_inl`,
  `MPSTensor.MultiBlockCompression.exists_smul_of_matching_inr`: *Two compressions with different
  flags*, the scalar clause for block slots with the same label and for zero slots.
* `MPSTensor.MultiBlockCompression.exists_ne_zero_eq_smul_of_slotTensor_eq`: the scalar clause for
  equal blocks at any two slots of two families (*The asymmetric fundamental theorem of matrix
  product states*, Theorem 2.2(c)).
* `MPSTensor.MultiBlockCompression.matching_eq_of_flag_eq`,
  `MPSTensor.MultiBlockCompression.inf_eq_and_sup_eq_of_flag_eq`: *Two compressions with different
  flags* for coinciding flags, where `U = M_k` and `N = M_{k-1}`.

## References

Blueprint chapter *The Multi-Block Asymmetric Fundamental Theorem* (`ch:asymmetric_ft`):
`thm:asym_uniq_different_flags`, *Two compressions with different flags*; *The asymmetric
fundamental theorem of matrix product states*, Theorem 2.2(c).
-/

open scoped Matrix

namespace Matrix

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {m n : Type*} [Fintype m]

/-- A linear map onto a coordinate space on a subspace `U` factors, on `U`, every linear map
whose kernel on `U` contains its own: if `f` maps `U` onto `ℂ^m` and `g` vanishes on
`U ∩ ker f`, then `g = X f` on `U` for a matrix `X`. -/
theorem exists_mulVec_eq_of_surjOn (U : Submodule ℂ V) (f : V →ₗ[ℂ] m → ℂ)
    (g : V →ₗ[ℂ] n → ℂ) (hf : Set.SurjOn f U Set.univ) (hfg : ∀ x ∈ U, f x = 0 → g x = 0) :
    ∃ X : Matrix n m ℂ, ∀ x ∈ U, X *ᵥ f x = g x := by
  classical
  have hsurj : LinearMap.range (f.domRestrict U) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun v => ?_
    obtain ⟨x, hx, rfl⟩ := hf (Set.mem_univ v)
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨r, hr⟩ := (f.domRestrict U).exists_rightInverse_of_surjective hsurj
  refine ⟨LinearMap.toMatrix' (g.domRestrict U ∘ₗ r), fun x hx => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  have h1 : f ((r (f x) : V) - x) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact LinearMap.congr_fun hr (f x)
  have h2 := hfg _ (U.sub_mem (r (f x)).2 hx) h1
  rw [map_sub, sub_eq_zero] at h2
  simpa using h2

/-- A matrix over a one-point index type is a scalar. -/
theorem exists_eq_smul_one_of_subsingleton [DecidableEq n] [Subsingleton n] [Nonempty n]
    (X : Matrix n n ℂ) : ∃ c : ℂ, X = c • 1 := by
  obtain ⟨j₀⟩ := ‹Nonempty n›
  refine ⟨X j₀ j₀, Matrix.ext fun i j => ?_⟩
  rw [Subsingleton.elim i j₀, Subsingleton.elim j j₀]
  simp

/-- If a scalar matrix `c • 1` on a nonempty index type has a right inverse `Y`, then `c ≠ 0`
and `Y = c⁻¹ • 1`. -/
theorem ne_zero_and_eq_inv_smul_one_of_smul_one_mul_eq_one [Fintype n] [DecidableEq n] [Nonempty n]
    {Y : Matrix n n ℂ} {c : ℂ} (h : (c • 1 : Matrix n n ℂ) * Y = 1) : c ≠ 0 ∧ Y = c⁻¹ • 1 := by
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, Matrix.zero_mul] at h
    exact zero_ne_one h
  refine ⟨hc, ?_⟩
  rw [Matrix.smul_mul, Matrix.one_mul] at h
  rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Matrix

namespace MPSTensor

open WordAlgebra

namespace MultiBlockCompression

variable {d DB : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {D : ι → ℕ} {D' : κ → ℕ}
  {B : MPSTensor d DB} {S : Finset ι} {S' : Finset κ} {C : ∀ s, MPSTensor d (D s)}
  {C' : ∀ t, MPSTensor d (D' t)}

section OneCompression

variable (P : MultiBlockCompression B S C)

/-- The reading map of a slot at position `k` maps a subspace `U` with `M_{k-1} + U = M_k` onto the
coordinates of the slot (proof of blueprint `thm:asym_uniq_different_flags`, *Two compressions with
different flags*: `W_b(U) = W_b(M_{k-1} + U) = W_b(M_k)`). -/
theorem leftRow_surjOn_of_sup_eq {b : BlockIndex S P.z}
    {U : Submodule (WordAlgebra d) B.WordModule}
    (hU : P.flag (P.ord b).castSucc ⊔ U = P.flag (P.ord b).succ) :
    Set.SurjOn (fun x : B.WordModule => P.leftRow b *ᵥ WordModule.toVec B x) U Set.univ := by
  intro v _
  obtain ⟨x, hx, rfl⟩ := P.leftRow_surjOn b (Set.mem_univ v)
  rw [SetLike.mem_coe, ← hU] at hx
  obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.1 hx
  refine ⟨u, hu, ?_⟩
  simp only [map_add, Matrix.mulVec_add, P.leftRow_mulVec_eq_zero_of_mem hy, zero_add]

/-- The kernel of the reading map of a slot at position `k` on `M_k` is `M_{k-1}` (blueprint
`lem:asym_uniq_maps`, *The compression maps in terms of the flag*, the assertions on `W_b`). -/
theorem mem_flag_of_leftRow_mulVec_eq_zero {b : BlockIndex S P.z} {x : B.WordModule}
    (hx : x ∈ P.flag (P.ord b).succ) (h : P.leftRow b *ᵥ WordModule.toVec B x = 0) :
    x ∈ P.flag (P.ord b).castSucc := by
  have hker : (⟨x, hx⟩ : P.flag (P.ord b).succ) ∈ LinearMap.ker (P.readStep b) := by
    rw [LinearMap.mem_ker, ← (WordModule.toVec (slotTensor C b)).map_eq_zero_iff,
      toVec_readStep]
    exact h
  rw [P.ker_readStep] at hker
  exact hker

/-- The reading map of a slot at position `k` intertwines the action of a letter on `M_k` with the
diagonal block of the slot (blueprint `lem:asym_uniq_maps`, *The compression maps in terms of the
flag*, the assertions on `W_b`), written with the action of the word algebra. -/
theorem leftRow_mulVec_ofWord_smul {b : BlockIndex S P.z} (i : Fin d) {x : B.WordModule}
    (hx : x ∈ P.flag (P.ord b).succ) :
    P.leftRow b *ᵥ WordModule.toVec B ((ofWord [i] : WordAlgebra d) • x) =
      slotTensor C b i *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x) := by
  rw [asModuleEquiv_letter_smul]
  exact P.leftRow_mulVec_mulVec_of_mem i hx

end OneCompression

section TwoCompressions

variable (P : MultiBlockCompression B S C) (Q : MultiBlockCompression B S' C')
  (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
  (hC' : ∀ t ∈ S', Kraus.IsNormal (C' t)) (hD' : ∀ t ∈ S', 0 < D' t)

/-- **Two compressions with different flags** (blueprint `thm:asym_uniq_different_flags`, *Two
compressions with different flags*). Let the position `k` of `P` carry the slot `b`, and the matched
position `k'` of `Q` the slot `b'`; put `U = M_k ∩ M'_{k'}` and `N = M_{k-1} + M'_{k'-1}`. There are
mutually inverse matrices `X`, `Y` such that `X` intertwines the diagonal blocks,
`X C_b^i = C'_{b'}^i X`, the reading maps satisfy `W'_{b'} x = X W_b x` for `x ∈ U`, and the
injections satisfy `V'_{b'} v - V_b Y v ∈ N` for every `v`. -/
theorem exists_intertwiner_of_matching (k : Fin (S.card + P.z)) {b : BlockIndex S P.z}
    (hb : P.ord b = k) {b' : BlockIndex S' Q.z}
    (hb' : Q.ord b' = P.matching Q hC hD hC' hD' k) :
    ∃ (X : Matrix (Fin (slotSize D' b')) (Fin (slotSize D b)) ℂ)
      (Y : Matrix (Fin (slotSize D b)) (Fin (slotSize D' b')) ℂ),
      X * Y = 1 ∧ Y * X = 1 ∧ (∀ i, X * slotTensor C b i = slotTensor C' b' i * X) ∧
      (∀ x ∈ P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ,
        Q.leftRow b' *ᵥ WordModule.toVec B x = X *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x)) ∧
      ∀ v, (WordModule.toVec B).symm (Q.rightCol b' *ᵥ v - P.rightCol b *ᵥ (Y *ᵥ v)) ∈
        P.flag k.castSucc ⊔ Q.flag (P.matching Q hC hD hC' hD' k).castSucc := by
  subst hb
  have hPU := P.flag_sup_inf_eq Q hC hD hC' hD' (P.ord b)
  have hQU := P.flag_sup_inf_eq' Q hC hD hC' hD' (P.ord b)
  have hK := (P.flag_inf_inf_eq Q hC hD hC' hD' (P.ord b)).trans
    (P.flag_inf_inf_eq' Q hC hD hC' hD' (P.ord b)).symm
  rw [← hb'] at hPU hQU hK ⊢
  set U := P.flag (P.ord b).succ ⊓ Q.flag (Q.ord b').succ with hU
  have hUP : U ≤ P.flag (P.ord b).succ := inf_le_left
  have hUQ : U ≤ Q.flag (Q.ord b').succ := inf_le_right
  have hsP := P.leftRow_surjOn_of_sup_eq hPU
  have hsQ := Q.leftRow_surjOn_of_sup_eq hQU
  -- The two reading maps have the same kernel `K` on `U`.
  have hkerP : ∀ x ∈ U, P.leftRow b *ᵥ WordModule.toVec B x = 0 →
      x ∈ Q.flag (Q.ord b').castSucc := fun x hx h =>
    (hK.le ⟨hx, P.mem_flag_of_leftRow_mulVec_eq_zero (hUP hx) h⟩).2
  have hkerQ : ∀ x ∈ U, Q.leftRow b' *ᵥ WordModule.toVec B x = 0 →
      x ∈ P.flag (P.ord b).castSucc := fun x hx h =>
    (hK.ge ⟨hx, Q.mem_flag_of_leftRow_mulVec_eq_zero (hUQ hx) h⟩).2
  obtain ⟨X, hX⟩ := Matrix.exists_mulVec_eq_of_surjOn (U.restrictScalars ℂ)
    ((P.leftRow b).mulVecLin ∘ₗ (WordModule.toVec B).toLinearMap)
    ((Q.leftRow b').mulVecLin ∘ₗ (WordModule.toVec B).toLinearMap) hsP
    fun x hx h => Q.leftRow_mulVec_eq_zero_of_mem (hkerP x hx h)
  obtain ⟨Y, hY⟩ := Matrix.exists_mulVec_eq_of_surjOn (U.restrictScalars ℂ)
    ((Q.leftRow b').mulVecLin ∘ₗ (WordModule.toVec B).toLinearMap)
    ((P.leftRow b).mulVecLin ∘ₗ (WordModule.toVec B).toLinearMap) hsQ
    fun x hx h => P.leftRow_mulVec_eq_zero_of_mem (hkerQ x hx h)
  simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply,
    LinearEquiv.coe_coe, Submodule.restrictScalars_mem] at hX hY
  refine ⟨X, Y, ?_, ?_, fun i => ?_, fun x hx => (hX x hx).symm, fun v => ?_⟩
  · refine Matrix.ext_iff_mulVec.2 fun v => ?_
    obtain ⟨x, hx, rfl⟩ := hsQ (Set.mem_univ v)
    rw [← Matrix.mulVec_mulVec, hY x hx, hX x hx, Matrix.one_mulVec]
  · refine Matrix.ext_iff_mulVec.2 fun v => ?_
    obtain ⟨x, hx, rfl⟩ := hsP (Set.mem_univ v)
    rw [← Matrix.mulVec_mulVec, hX x hx, hY x hx, Matrix.one_mulVec]
  · -- Intertwining: `X C_b^i W_b u = X W_b (B^i u) = W'_{b'} (B^i u) = C'_{b'}^i X W_b u`.
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    obtain ⟨x, hx, rfl⟩ := hsP (Set.mem_univ v)
    have hix : (ofWord [i] : WordAlgebra d) • x ∈ U := U.smul_mem _ hx
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← P.leftRow_mulVec_ofWord_smul i (hUP hx),
      hX _ hix, hX x hx, Q.leftRow_mulVec_ofWord_smul i (hUQ hx)]
  · -- Injections: decompose `V'_{b'} v = y + u` and `V_b Y v = y' + u'` along `N`.
    have hq := Q.rightCol_mulVec_mem_flag b' v
    rw [← hQU] at hq
    obtain ⟨y, hy, u, hu, hyu⟩ := Submodule.mem_sup.1 hq
    have hp := P.rightCol_mulVec_mem_flag b (Y *ᵥ v)
    rw [← hPU] at hp
    obtain ⟨y', hy', u', hu', hyu'⟩ := Submodule.mem_sup.1 hp
    have h1 : Q.leftRow b' *ᵥ WordModule.toVec B u = v := by
      have h := congrArg (fun w => Q.leftRow b' *ᵥ WordModule.toVec B w) hyu
      simp only [map_add, Matrix.mulVec_add, Q.leftRow_mulVec_eq_zero_of_mem hy, zero_add,
        LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, leftRow_mul_rightCol_self,
        Matrix.one_mulVec] at h
      exact h
    have h2 : P.leftRow b *ᵥ WordModule.toVec B u' = Y *ᵥ v := by
      have h := congrArg (fun w => P.leftRow b *ᵥ WordModule.toVec B w) hyu'
      simp only [map_add, Matrix.mulVec_add, P.leftRow_mulVec_eq_zero_of_mem hy', zero_add,
        LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
        leftRow_mul_rightCol_self, Matrix.one_mul] at h
      exact h
    have h3 : P.leftRow b *ᵥ WordModule.toVec B (u - u') = 0 := by
      rw [map_sub, Matrix.mulVec_sub, h2, ← hY u hu, h1, sub_self]
    have h4 : u - u' ∈ P.flag (P.ord b).castSucc :=
      P.mem_flag_of_leftRow_mulVec_eq_zero (hUP (U.sub_mem hu hu')) h3
    rw [map_sub, ← hyu, ← hyu']
    exact Submodule.mem_sup.2 ⟨u - u' - y', sub_mem h4 hy', y, hy, by abel⟩

/-- **Two compressions with different flags, uniqueness of the intertwiner** (blueprint
`thm:asym_uniq_different_flags`, *Two compressions with different flags*): the intertwiner `X` with
`W'_{b'} x = X W_b x` for `x ∈ U = M_k ∩ M'_{k'}` is unique, because `W_b` maps `U` onto the
coordinates of `b`. -/
theorem existsUnique_intertwiner_of_matching (k : Fin (S.card + P.z)) {b : BlockIndex S P.z}
    (hb : P.ord b = k) {b' : BlockIndex S' Q.z}
    (hb' : Q.ord b' = P.matching Q hC hD hC' hD' k) :
    ∃! X : Matrix (Fin (slotSize D' b')) (Fin (slotSize D b)) ℂ,
      (∀ i, X * slotTensor C b i = slotTensor C' b' i * X) ∧
      ∀ x ∈ P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ,
        Q.leftRow b' *ᵥ WordModule.toVec B x = X *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x) := by
  obtain ⟨X, -, -, -, hint, hX, -⟩ := P.exists_intertwiner_of_matching Q hC hD hC' hD' k hb hb'
  refine ⟨X, ⟨hint, hX⟩, fun X' hX' => ?_⟩
  subst hb
  have hs := P.leftRow_surjOn_of_sup_eq (P.flag_sup_inf_eq Q hC hD hC' hD' (P.ord b))
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  obtain ⟨x, hx, rfl⟩ := hs (Set.mem_univ v)
  rw [← hX'.2 x hx, hX x hx]

/-- **Two compressions with different flags, on a pair of zero slots** (blueprint
`thm:asym_uniq_different_flags`, *Two compressions with different flags*): when the position `k` of
`P` and the matched position `k'` of `Q` carry zero slots, there is a nonzero scalar `λ` with
`W'_{b'} = λ W_b` on `U = M_k ∩ M'_{k'}` and `V'_{b'} ≡ λ⁻¹ V_b` modulo `N = M_{k-1} + M'_{k'-1}`.
-/
theorem exists_smul_of_matching_inr (k : Fin (S.card + P.z)) {t : Fin P.z}
    (hk : P.ord (Sum.inr t) = k) {t' : Fin Q.z}
    (hk' : Q.ord (Sum.inr t') = P.matching Q hC hD hC' hD' k) :
    ∃ c : ℂ, c ≠ 0 ∧
      (∀ x ∈ P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ,
        Q.leftRow (Sum.inr t') *ᵥ WordModule.toVec B x =
          c • (P.leftRow (Sum.inr t) *ᵥ WordModule.toVec B x)) ∧
      ∀ v, (WordModule.toVec B).symm
          (Q.rightCol (Sum.inr t') *ᵥ v - c⁻¹ • (P.rightCol (Sum.inr t) *ᵥ v)) ∈
        P.flag k.castSucc ⊔ Q.flag (P.matching Q hC hD hC' hD' k).castSucc := by
  obtain ⟨X, Y, hXY, -, -, hX, hV⟩ :=
    P.exists_intertwiner_of_matching Q hC hD hC' hD' k hk hk'
  obtain ⟨c, rfl⟩ := Matrix.exists_eq_smul_one_of_subsingleton (n := Fin 1) X
  obtain ⟨hc, rfl⟩ := Matrix.ne_zero_and_eq_inv_smul_one_of_smul_one_mul_eq_one (n := Fin 1) hXY
  refine ⟨c, hc, fun x hx => ?_, fun v => ?_⟩
  · rw [hX x hx, Matrix.smul_mulVec, Matrix.one_mulVec]
  · have h := hV v
    rwa [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul] at h

/-- **Matched positions of coinciding flags** (blueprint `thm:asym_uniq_different_flags`, *Two
compressions with different flags*, the case of coinciding flags): if the position `j` of `Q` has
the same two members `M'_{j-1} = M_{k-1}`, `M'_j = M_k` as the position `k` of `P`, then `j` is
matched with `k`. -/
theorem matching_eq_of_flag_eq (k : Fin (S.card + P.z)) {j : Fin (S'.card + Q.z)}
    (h0 : Q.flag j.castSucc = P.flag k.castSucc) (h1 : Q.flag j.succ = P.flag k.succ) :
    P.matching Q hC hD hC' hD' k = j := by
  rw [matching_apply]
  refine (CoveringMatching.CoveringChain.jump_unique _ _ k ?_).symm
  change P.flag k.castSucc ⊔ (P.flag k.succ ⊓ Q.flag j.castSucc) <
    P.flag k.castSucc ⊔ (P.flag k.succ ⊓ Q.flag j.succ)
  rw [h0, h1, inf_idem, sup_eq_left.2 inf_le_right,
    sup_eq_right.2 (P.flag_mono (Fin.castSucc_le_succ k))]
  exact (P.flag_covBy hC hD k).lt

/-- **Two compressions with different flags, for coinciding flags** (blueprint
`thm:asym_uniq_different_flags`, *Two compressions with different flags*): when the position `j` of
`Q` has the same two members `M'_{j-1} = M_{k-1}`, `M'_j = M_k` as the position `k` of `P`, the
subspaces of *Two compressions with different flags* are `U = M_k` and `N = M_{k-1}`. -/
theorem inf_eq_and_sup_eq_of_flag_eq (k : Fin (S.card + P.z)) {j : Fin (S'.card + Q.z)}
    (h0 : Q.flag j.castSucc = P.flag k.castSucc) (h1 : Q.flag j.succ = P.flag k.succ) :
    P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ = P.flag k.succ ∧
      P.flag k.castSucc ⊔ Q.flag (P.matching Q hC hD hC' hD' k).castSucc =
        P.flag k.castSucc := by
  rw [P.matching_eq_of_flag_eq Q hC hD hC' hD' k h0 h1, h0, h1]
  exact ⟨inf_idem _, sup_idem _⟩

end TwoCompressions

section SameFamily

variable (P Q : MultiBlockCompression B S C) (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
  (hD : ∀ s ∈ S, 0 < D s)

/-- **Two compressions with different flags, on a pair of block slots with the same label**
(blueprint `thm:asym_uniq_different_flags`, *Two compressions with different flags*): for two
compressions onto the same family, when the position `k` of `P` and the matched position `k'` of `Q`
both carry the block `C_s`, the intertwiner of *Two compressions with different flags* commutes with
`C_s` and is a nonzero scalar `λ` by Schur's lemma; so `W'_s = λ W_s` on `U = M_k ∩ M'_{k'}` and
`V'_s ≡ λ⁻¹ V_s` modulo `N = M_{k-1} + M'_{k'-1}`. -/
theorem exists_smul_of_matching_inl (k : Fin (S.card + P.z)) (s : {s // s ∈ S})
    (hk : P.ord (Sum.inl s) = k) (hk' : Q.ord (Sum.inl s) = P.matching Q hC hD hC hD k) :
    ∃ c : ℂ, c ≠ 0 ∧
      (∀ x ∈ P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC hD k).succ,
        Q.leftRow (Sum.inl s) *ᵥ WordModule.toVec B x =
          c • (P.leftRow (Sum.inl s) *ᵥ WordModule.toVec B x)) ∧
      ∀ v, (WordModule.toVec B).symm
          (Q.rightCol (Sum.inl s) *ᵥ v - c⁻¹ • (P.rightCol (Sum.inl s) *ᵥ v)) ∈
        P.flag k.castSucc ⊔ Q.flag (P.matching Q hC hD hC hD k).castSucc := by
  obtain ⟨X, Y, hXY, -, hint, hX, hV⟩ :=
    P.exists_intertwiner_of_matching Q hC hD hC hD k hk hk'
  have : Nonempty (Fin (D s.1)) := ⟨⟨0, hD s.1 s.2⟩⟩
  obtain ⟨c, rfl⟩ := (hC s.1 s.2).eq_smul_one_of_commute (S := X) hint
  obtain ⟨hc, rfl⟩ :=
    Matrix.ne_zero_and_eq_inv_smul_one_of_smul_one_mul_eq_one (n := Fin (D s.1)) hXY
  refine ⟨c, hc, fun x hx => ?_, fun v => ?_⟩
  · rw [hX x hx, Matrix.smul_mulVec, Matrix.one_mulVec]
  · have h := hV v
    rwa [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul] at h

end SameFamily

section EqualBlocks

variable (P : MultiBlockCompression B S C) (Q : MultiBlockCompression B S' C')

/-- **Equal blocks give a scalar** (*The asymmetric fundamental theorem of matrix product states*,
Theorem 2.2(c)), for two families: if the diagonal blocks at the slot `b` of `P` and the slot `b'`
of `Q` are equal tensors (equal sizes, letters equal after the size identification; two zero slots
count as equal), then every invertible intertwiner `X` from the first to the second, in particular
the intertwiner of *Two compressions with different flags* for matched slots, is a nonzero multiple
of the identification. This covers equal blocks at different labels of one family and blocks of two
families. The statement holds for any two slots, matched or not, and uses only `X Y = 1`. -/
theorem exists_ne_zero_eq_smul_of_slotTensor_eq (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) {b : BlockIndex S P.z} {b' : BlockIndex S' Q.z}
    (hdim : slotSize D b = slotSize D' b')
    (heq : ∀ i, Matrix.reindex (finCongr hdim) (finCongr hdim) (slotTensor C b i) =
      slotTensor C' b' i)
    {X : Matrix (Fin (slotSize D' b')) (Fin (slotSize D b)) ℂ}
    {Y : Matrix (Fin (slotSize D b)) (Fin (slotSize D' b')) ℂ} (hXY : X * Y = 1)
    (hint : ∀ i, X * slotTensor C b i = slotTensor C' b' i * X) :
    ∃ c : ℂ, c ≠ 0 ∧
      X = c • Matrix.reindex (finCongr hdim) (Equiv.refl _)
        (1 : Matrix (Fin (slotSize D b)) (Fin (slotSize D b)) ℂ) :=
  have := isSimpleModule_slotTensor hC hD b
  exists_ne_zero_eq_smul_reindex_one_of_intertwines hdim
    ((isIrreducibleAction_and_pos_iff_isSimpleModule _).2 this).1 heq hXY hint

end EqualBlocks

end MultiBlockCompression

end MPSTensor
