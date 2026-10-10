/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.GroupCocycleMPO
import TNLean.MPS.Symmetry.MPOSymmetry.Associator

/-!
# Group matrix product operators from a three-cocycle: fusion tensors and the inverse cocycle

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), Section
"Examples of explicit MPSs and MPO representations", `Papers/2203.12563/REsubmission.tex`
lines 2025–2044: the fusion tensors of the tensors built from a three-cocycle `ω` have nonzero
elements `ω(g,h,k)⁻¹`, at the bond labels `hk` of `g` and `k` of `h` fused into the label `k`
of `gh` (equation `ftexam`), and "these fusion tensors satisfy Eq. (3cocygroup) with the
3-cocycle `ω(g,h,k)⁻¹`". Lines 2224–2225: the periodic tensors `T̂_g` of lines 2204–2222
"satisfy Eq. (fusiontensorG2) with fusion tensors defined in Eq. (ftexam)". The three-cocycle
of equation `3cocygroup` (lines 664–679) compares the tree fusing `g` with `h` first to the
tree fusing `h` with `k` first, as the three-cochain of arXiv:2502.20257 (display preceding
`eq:3-cocycle`) does.

**Formalized here.** For every three-cocycle `ω` of a group `G`, the fusion tensors of
equation `ftexam`, read on the periodic tensors `T̂_g`, reduce the stacked product of `T̂_g` and
`T̂_h` onto `T̂_{gh}` (the reduction `fusiontensorG2`, at every word length and including the
empty word), and the three-cochain they define is `ω⁻¹`: the two fusion trees of a triple
product differ by exactly `ω(g,h,k)⁻¹`. So the representation built from `ω` carries the
inverse cocycle, as the source states at line 2044.

The identity member `T̂_e` has bond dimension `|G|` and is not normal once `G` is nontrivial
(`not_isNormal_tensor_one`): every product of its letters has equal rows. Hence the family is
not a `MPOTensor.GroupFamily.IsNormalRepresentation`, and the class-independence results for
normal representations do not apply to it; the three-cochain computed here is the one of the
source's fusion tensors.

## Main definitions

* `MPOTensor.GroupCocycle.fusionV`, `MPOTensor.GroupCocycle.fusionW`: the fusion tensors of
  equation `ftexam`.
* `MPOTensor.GroupCocycle.fusionData`: the corresponding choice of fusion tensors.

## Main results

* `MPOTensor.GroupCocycle.isReduction_fusion`: the reduction `fusiontensorG2`.
* `MPOTensor.GroupCocycle.fusionData_leftV`: the two fusion trees differ by `ω(g,h,k)⁻¹`.
* `MPOTensor.GroupCocycle.fusionData_omega`: the three-cochain of the fusion tensors is `ω⁻¹`.
* `MPOTensor.GroupCocycle.not_isNormal_tensor_one`: `T̂_e` is not normal for `|G| ≥ 2`.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- Garre-Rubio, Lootens, Molnár,
  *Classifying phases protected by matrix product operator symmetries using matrix product
  states*
- [arXiv:2502.20257](https://arxiv.org/abs/2502.20257) -- the anomaly three-cochain of a
  group of matrix product operators
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace MPOTensor.GroupCocycle

variable {G : Type*} [Group G] {n : ℕ} (e : G ≃ Fin n)

/-- The pair of bond labels `(h l, l)` of the stacked product of `T̂_g` and `T̂_h` that sits
over the bond label `l` of `T̂_{gh}`: the label of `T̂_h` is `l`, that of `T̂_g` is `h l`. -/
def pairLabel (h : G) (l : Fin n) : Fin (n * n) :=
  finProdFinEquiv (siteShift e h l, l)

theorem pairLabel_injective (h : G) : Function.Injective (pairLabel e h) := by
  intro l l' hl
  simpa [pairLabel] using congrArg Prod.snd (finProdFinEquiv.injective hl)

end MPOTensor.GroupCocycle

namespace MPOTensor.GroupCocycle

open TNLean.Algebra MPOTensor.GroupFamily

variable {G : Type} [Group G] {n : ℕ} (e : G ≃ Fin n)

/-- The left fusion tensor `F^<_{g,h}` of equation `ftexam`: it sends the pair label
`(h l, l)` to the label `l` with the factor `ω(g, h, l)⁻¹`.

Source: arXiv:2203.12563, lines 2025–2043 (equation `ftexam`) and 2224–2225. -/
def fusionV (ω : ScalarThreeCochain G) (g h : G) : Matrix (Fin n) (Fin (n * n)) ℂ :=
  Matrix.of fun l p ↦ if p = pairLabel e h l then ((ω g h (e.symm l))⁻¹ : ℂˣ) else 0

/-- The right fusion tensor `F^>_{g,h}`, the inverse of `fusionV` on its range: it sends the
label `r` to the pair label `(h r, r)` with the factor `ω(g, h, r)`. The source prints only
the left fusion tensor; this one is fixed by `F^< F^> = 1` (arXiv:2203.12563, line 1026, the
case `n = 0` of `fusiontensorG2`). -/
def fusionW (ω : ScalarThreeCochain G) (g h : G) : Matrix (Fin (n * n)) (Fin n) ℂ :=
  Matrix.of fun p r ↦ if p = pairLabel e h r then (ω g h (e.symm r) : ℂ) else 0

variable {e}

theorem fusionV_mul_apply {m : ℕ} (ω : ScalarThreeCochain G) (g h : G)
    (M : Matrix (Fin (n * n)) (Fin m) ℂ) (l : Fin n) (q : Fin m) :
    (fusionV e ω g h * M) l q = ((ω g h (e.symm l))⁻¹ : ℂˣ) * M (pairLabel e h l) q := by
  simp [fusionV, Matrix.mul_apply, ite_mul, zero_mul, Finset.sum_ite_eq']

theorem mul_fusionV_apply {m : ℕ} (ω : ScalarThreeCochain G) (g h : G)
    (M : Matrix (Fin m) (Fin n) ℂ) (q : Fin m) (p : Fin n × Fin n) :
    (M * fusionV e ω g h) q (finProdFinEquiv p) =
      if p.1 = siteShift e h p.2 then M q p.2 * ((ω g h (e.symm p.2))⁻¹ : ℂˣ) else 0 := by
  obtain ⟨a, b⟩ := p
  simp only [Matrix.mul_apply, fusionV, Matrix.of_apply, mul_ite, mul_zero, pairLabel,
    EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hab : a = siteShift e h b
  · simp [hab]
  · simp only [hab, ↓reduceIte]
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    simp only [ite_eq_right_iff, and_imp]
    rintro h1 rfl
    exact absurd h1 hab

variable (e) in
/-- **The fusion tensors intertwine every letter**: `F^<_{g,h} (T̂_g T̂_h)^{ij} =
T̂_{gh}^{ij} F^<_{g,h}`. The bondwise identity is the three-cocycle equation in the form
`phase_site`.

Source: arXiv:2203.12563, lines 2224–2225 (the tensors `T̂_g` satisfy `fusiontensorG2` with
the fusion tensors of `ftexam`). -/
theorem fusionV_mul_mulTensor {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω)
    (g h : G) (i j : Fin n) :
    fusionV e ω g h * mulTensor (tensor e ω g) (tensor e ω h) i j =
      tensor e ω (g * h) i j * fusionV e ω g h := by
  ext l p
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective p
  rw [fusionV_mul_apply, mul_fusionV_apply]
  simp only [mulTensor_apply, pairLabel, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.sum_apply, Matrix.kroneckerMap_apply, tensor_apply]
  obtain ⟨a, b⟩ := p
  rw [Finset.sum_eq_single a (fun c _ hc ↦ by simp [Ne.symm hc]) (by simp)]
  by_cases hb : b = j
  · subst hb
    by_cases ha : a = siteShift e h b
    · subst ha
      have key := congrArg Units.val (phase_site hω g h (e.symm b) (e.symm l))
      simp only [Units.val_mul] at key
      by_cases hi : i = siteShift e (g * h) b
      · subst hi
        simp only [siteShift_apply, Equiv.symm_apply_apply, mul_assoc, and_self, ↓reduceIte]
        rw [key, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
        have := Units.ne_zero (ω g h (e.symm l))
        field_simp
      · simp only [siteShift_apply, mul_assoc] at hi ⊢
        simp [hi]
    · rw [siteShift_apply] at ha
      simp [ha]
  · simp [hb]

theorem fusionV_mul_fusionW (ω : ScalarThreeCochain G) (g h : G) :
    fusionV e ω g h * fusionW e ω g h = 1 := by
  ext l r
  rw [fusionV_mul_apply]
  simp only [fusionW, Matrix.of_apply, (pairLabel_injective e h).eq_iff, Matrix.one_apply]
  split_ifs with hlr
  · subst hlr
    simp
  · simp

variable (e) in
/-- **The fusion tensors reduce the stacked product onto `T̂_{gh}`** (the reduction
`fusiontensorG2` of arXiv:2203.12563, lines 1002–1026): `F^<_{g,h} F^>_{g,h} = 1` and
`F^<_{g,h} (T̂_g T̂_h)^w F^>_{g,h} = T̂_{gh}^w` for every word `w`, including the empty word.

Source: arXiv:2203.12563, lines 2224–2225, with the fusion tensors of `ftexam`
(lines 2025–2043). Here the remainder of the stacked product vanishes on the range of the
fusion tensors, so the identity holds at every length. -/
theorem isReduction_fusion {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω)
    (g h : G) :
    MPSTensor.IsReduction (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor
      (tensor e ω (g * h)).toMPSTensor (fusionV e ω g h) (fusionW e ω g h) := by
  refine ⟨fusionV_mul_fusionW ω g h, fun w ↦ ?_⟩
  have hw := Kraus.evalWord_intertwine (tensor e ω (g * h)).toMPSTensor
    (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor (fusionV e ω g h)
    (fun ij ↦ (fusionV_mul_mulTensor e hω g h ij.divNat ij.modNat).symm) w
  rw [← hw, Matrix.mul_assoc, fusionV_mul_fusionW, Matrix.mul_one]

variable (e) in
/-- **The fusion tensors of arXiv:2203.12563, equation `ftexam`**, as a choice of fusion tensors
of the periodic representation built from `ω`.

Source: arXiv:2203.12563, lines 2025–2043 and 2224–2225. -/
def fusionData {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω) :
    (family e ω).FusionData where
  V := fusionV e ω
  W := fusionW e ω
  isReduction := isReduction_fusion e hω

theorem fusionV_mul_kronId {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω)
    (g h k : G) :
    fusionV e ω (g * h) k * kronId (fusionV e ω g h) n =
      ((ω g h k)⁻¹ : ℂˣ) •
        (fusionV e ω g (h * k) * idKron n (fusionV e ω h k) * mulTensorAssocInvMatrix n n n) := by
  rw [mulTensorAssocInvMatrix, PEquiv.mul_toMatrix_toPEquiv]
  ext x p
  obtain ⟨⟨q, c⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective q
  simp only [Matrix.smul_apply, Matrix.submatrix_apply, id, fusionV_mul_apply]
  simp only [kronId, idKron, pairLabel, mulTensorAssocEquiv, fusionV]
  simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.symm_apply_apply, Matrix.one_apply, Equiv.symm_symm, Equiv.trans_apply,
    Equiv.prodCongr_apply, Prod.map, Equiv.prodAssoc_apply, Equiv.refl_apply,
    EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, siteShift_apply, Equiv.symm_apply_apply,
    mul_assoc]
  by_cases hx : x = c
  · subst hx
    by_cases hb : b = e (k * e.symm x)
    · subst hb
      by_cases ha : a = e (h * (k * e.symm x))
      · subst ha
        simp only [and_self, ↓reduceIte, mul_one, one_mul, Units.smul_def, smul_eq_mul,
          ← Units.val_mul, ← mul_inv]
        rw [hω g h k (e.symm x), mul_assoc]
      · simp [ha, Ne.symm ha]
    · simp [hb]
  · simp [hx, Ne.symm hx]

variable (e) in
/-- The bond identifications of the family are trivial: every member has bond dimension `|G|`. -/
theorem castMat_family_mul (ω : ScalarThreeCochain G) {a b : G} (p : a = b) {m : ℕ}
    (M : Matrix (Fin ((family e ω).bondDim a)) (Fin m) ℂ) :
    (family e ω).castMat p * M = M := by
  subst p
  simp

variable (e) in
/-- **The two fusion trees differ by `ω(g,h,k)⁻¹`**: for the fusion tensors of `ftexam`, the
tree fusing `g` with `h` first is `ω(g,h,k)⁻¹` times the tree fusing `h` with `k` first,
exactly and not only against long words.

Source: arXiv:2203.12563, line 2044 ("these fusion tensors satisfy Eq. (3cocygroup) with the
3-cocycle `ω(g,h,k)⁻¹`"), for the periodic tensors of lines 2224–2225. -/
theorem fusionData_leftV {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω)
    (g h k : G) :
    (fusionData e hω).leftV g h k = ((ω g h k)⁻¹ : ℂˣ) • (fusionData e hω).rightV g h k := by
  rw [FusionData.leftV, FusionData.rightV, castMat_family_mul]
  exact fusionV_mul_kronId hω g h k

variable (e) in
/-- The two fusion trees satisfy the characterizing identity of the anomaly three-cochain with
the scalar `ω(g,h,k)⁻¹`.

Source: arXiv:2203.12563, line 2044, read on the periodic tensors of lines 2224–2225. -/
theorem fusionData_isAssociator {ω : ScalarThreeCochain G}
    (hω : ScalarThreeCochain.IsCocycle ω) (g h k : G) :
    (fusionData e hω).IsAssociator g h k ((ω g h k)⁻¹ : ℂˣ) :=
  ⟨0, fun w _ ↦ by rw [fusionData_leftV, Matrix.smul_mul, Units.smul_def]⟩

variable (e) in
/-- Every tensor `T̂_g` has nonvanishing words of every length: the periodic operator is a
shift with phases of modulus one. -/
theorem exists_evalWord_tensor_ne_zero (ω : ScalarThreeCochain G) (g : G) (N : ℕ) :
    ∃ w : List (Fin (n * n)), N ≤ w.length ∧
      Kraus.evalWord (tensor e ω g).toMPSTensor w ≠ 0 := by
  let t : Fin (N + 1) → Fin n := fun _ ↦ e 1
  let ρ : Fin (N + 1) → Fin (n * n) := fun k ↦ finProdFinEquiv (shift e g (N + 1) t k, t k)
  refine ⟨List.ofFn ρ, by simp, fun h0 ↦ ?_⟩
  have hmpv := mpv_toMPSTensor (tensor e ω g) ρ
  have hdiv : (fun k ↦ (ρ k).divNat) = shift e g (N + 1) t := by
    funext k
    simp [ρ]
  have hmod : (fun k ↦ (ρ k).modNat) = t := by
    funext k
    simp [ρ]
  rw [hdiv, hmod, mpo_tensor_apply] at hmpv
  simp only [↓reduceIte, MPSTensor.mpv, MPSTensor.coeff, h0, Matrix.trace_zero] at hmpv
  exact (Units.ne_zero (∏ i, ω g (e.symm (t (i + 1))) ((e.symm (t (i + 1)))⁻¹ * e.symm (t i))))
    (by rw [Units.coe_prod]; exact hmpv.symm)

variable (e) in
/-- **The representation built from `ω` carries `ω⁻¹`**: the anomaly three-cochain of the
fusion tensors of `ftexam` is the inverse of the cocycle the tensors are built from.

Source: arXiv:2203.12563, line 2044 ("these fusion tensors satisfy Eq. (3cocygroup) with the
3-cocycle `ω(g,h,k)⁻¹`") and lines 2224–2225 (the periodic tensors satisfy `fusiontensorG2`
with the same fusion tensors). The cochain is that of arXiv:2502.20257, display preceding
`eq:3-cocycle`, whose orientation agrees with `3cocygroup` (lines 664–679). -/
theorem fusionData_omega {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω) :
    (fusionData e hω).omega = ω⁻¹ := by
  funext g h k
  have hz := fusionData_isAssociator e hω g h k
  have hex : ∃ z : ℂ, z ≠ 0 ∧ (fusionData e hω).IsAssociator g h k z :=
    ⟨_, Units.ne_zero _, hz⟩
  have hdp := MPSTensor.isDressedProportional_dressedScalar hex
  apply Units.ext
  simp only [Pi.inv_apply]
  refine hdp.eq_of_forall_exists_ne_zero hz fun N ↦ ?_
  obtain ⟨w, hw, hne⟩ := exists_evalWord_tensor_ne_zero e ω (g * h * k) N
  refine ⟨w, hw, fun h0 ↦ hne ?_⟩
  have hred := ((fusionData e hω).isReduction_left g h k).evalWord w
  rw [h0, Matrix.zero_mul] at hred
  exact hred.symm

/-! ### The identity member is not normal -/

variable (e) in
/-- For a normalized cochain, every entry of a letter of `T̂_e` is independent of its row. -/
theorem tensor_one_apply_row {ω : ScalarThreeCochain G} (hn : ScalarThreeCochain.IsNormalized ω)
    (ij : Fin (n * n)) (l l' r : Fin n) :
    (tensor e ω 1).toMPSTensor ij l r = (tensor e ω 1).toMPSTensor ij l' r := by
  simp [MPOTensor.toMPSTensor, tensor_apply, hn.1]

variable (e) in
/-- Every nonempty product of letters of `T̂_e` has equal rows. -/
theorem evalWord_tensor_one_apply_row {ω : ScalarThreeCochain G}
    (hn : ScalarThreeCochain.IsNormalized ω) {w : List (Fin (n * n))} (hw : w ≠ [])
    (l l' r : Fin n) :
    Kraus.evalWord (tensor e ω 1).toMPSTensor w l r =
      Kraus.evalWord (tensor e ω 1).toMPSTensor w l' r := by
  obtain ⟨i, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp only [Kraus.evalWord_cons, Matrix.mul_apply, tensor_one_apply_row e hn i l l']

variable (e) in
/-- **The identity member `T̂_e` is not normal** once `G` is nontrivial: its bond dimension is
`|G|`, but every nonempty product of its letters has equal rows, so no word length spans the
full matrix algebra. Hence the family built from `ω` is not a representation with normal
tensors (`not_isNormalRepresentation`).

Project result: arXiv:2203.12563, lines 2204–2222, prints `T̂_g` for every `g`, including `e`,
with bond dimension `|G|`, and states `U_e = 1` (line 2204); the failure of normality at `e`
is not discussed there. -/
theorem not_isNormal_tensor_one [Nontrivial G] {ω : ScalarThreeCochain G}
    (hn : ScalarThreeCochain.IsNormalized ω) :
    ¬ Kraus.IsNormal (tensor e ω 1).toMPSTensor := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne G
  rintro ⟨N, hN, hinj⟩
  let φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    Matrix.entryLinearMap ℂ ℂ (e a) (e a) - Matrix.entryLinearMap ℂ ℂ (e b) (e a)
  have hle : Kraus.wordSpan (tensor e ω 1).toMPSTensor N ≤ LinearMap.ker φ := by
    rw [Kraus.wordSpan, Submodule.span_le]
    rintro _ ⟨σ, rfl⟩
    have hw : List.ofFn σ ≠ [] := by
      simpa [List.ofFn_eq_nil_iff] using Nat.pos_iff_ne_zero.mp hN
    simp [φ, evalWord_tensor_one_apply_row e hn hw (e a) (e b) (e a)]
  have hmem := hle (hinj ▸ Submodule.mem_top (x := Matrix.single (e a) (e a) (1 : ℂ)))
  simp [φ, e.injective.ne hab] at hmem

variable (e) in
/-- The family built from a normalized `ω` on a nontrivial group is not a representation with
normal tensors, so the class-independence results for such representations do not apply to
it; its three-cochain is taken with the fusion tensors of the source (`fusionData_omega`). -/
theorem not_isNormalRepresentation [Nontrivial G] {ω : ScalarThreeCochain G}
    (hn : ScalarThreeCochain.IsNormalized ω) : ¬ (family e ω).IsNormalRepresentation :=
  fun h ↦ not_isNormal_tensor_one e hn (h.isNormal 1)

end MPOTensor.GroupCocycle
