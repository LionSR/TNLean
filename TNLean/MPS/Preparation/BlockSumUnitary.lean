/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockUnitary
import TNLean.MPS.Preparation.OrthogonalBlockSum
import TNLean.MPS.Preparation.PolarUniqueness
import TNLean.MPS.Preparation.SequentialFactorization

/-!
# One block unitary for several blocks with orthogonal states

For a tensor that is not normal, arXiv:2307.01696 (paragraph "Long-range MPS using
measurements") applies on every block of `q` sites the isometry `V` of the polar decomposition
of the blocked tensor, "following the same steps as in the tree-RG circuit". For a direct sum of
blocks `A_j` whose `q`-site states are orthogonal, `B_jᴴ B_{j'} = 0`, the isometry acts on the
bond pairs `(l, r)` of each block `j` as the isometry `V_j` of that block. This file builds one
unitary on `q` sites, a product of `O(q)` gates on neighbouring sites, that implements all the
`V_j` at once (`MPSPreparation.exists_blockSumUnitary`): placing the bond indices of the blocks
side by side in `Fin (∑ⱼ Dⱼ)`, it sends the input `|l, 0 ⋯ 0, r⟩` of a pair of block `j` to
`V_j |l, r⟩`.

The map `(j, l, r) ↦ V_j |l, r⟩` is an isometry, because the ranges of the `V_j` are orthogonal
(`Matrix.conjTranspose_polarIso_mul_polarIso_eq_zero`), and it is the matrix product map of the
direct sum with the inverse positive parts of the blocks absorbed on the right. The sequential
factorization of arXiv:2307.01696, eqs. (13)–(15), applies to such a map
(`MPSPreparation.exists_isometric_chain_of_eq_mul_of_le`), and the staircase of
`MPSPreparation.exists_blockUnitary_of_equiv` implements the factorized map.

**Scope restriction (orthogonal blocks):** `MPSPreparation.exists_blockSumUnitary` takes the
orthogonality `B_jᴴ B_{j'} = 0` of the `q`-site states of distinct blocks, which the source does
not assume; without it the isometry of the blocked direct sum is not the sum of the isometries
`V_j` of the blocks. Documented in `docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSPreparation.flatCoord` — the place of the bond index `a` of block `j` in `Fin (∑ⱼ Dⱼ)`.
* `MPSPreparation.exists_blockSumUnitary` — the block unitary.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, eqs. (11), (13)–(15), and the paragraph "Long-range MPS using
  measurements".
-/

open Matrix MPSTensor
open scoped BigOperators
open QuantumCircuit

namespace MPSPreparation

open MPSChainTensor (eval)

variable {d b : ℕ} {Dj : Fin b → ℕ}

/-- The place of the bond index `a` of block `j` among the bond indices of all blocks placed side
by side, `Fin (∑ⱼ Dⱼ)`. -/
def flatCoord (Dj : Fin b → ℕ) (j : Fin b) (a : Fin (Dj j)) : Fin (∑ j, Dj j) :=
  finSigmaFinEquiv ⟨j, a⟩

theorem flatCoord_injective (j : Fin b) : Function.Injective (flatCoord Dj j) := fun _ _ h =>
  eq_of_heq (Sigma.mk.inj (finSigmaFinEquiv.injective h)).2

theorem flatCoord_ne {j j' : Fin b} (h : j ≠ j') (a : Fin (Dj j)) (a' : Fin (Dj j')) :
    flatCoord Dj j a ≠ flatCoord Dj j' a' := fun e =>
  h (Sigma.mk.inj (finSigmaFinEquiv.injective e)).1

/-- An entry of a nonempty word of the direct sum of blocks placed along `flatCoord`, between two
bond indices of block `j`, is the entry of the word of block `j`. -/
theorem evalWord_blockSum_flatCoord (A : (j : Fin b) → MPSTensor d (Dj j)) {w : List (Fin d)}
    (hw : w ≠ []) (j : Fin b) (α β : Fin (Dj j)) :
    Kraus.evalWord (blockSum A (flatCoord Dj) fun _ => 1) w (flatCoord Dj j α)
      (flatCoord Dj j β) = Kraus.evalWord (A j) w α β := by
  classical
  rw [evalWord_blockSum (fun j => flatCoord_injective j)
    (fun _ _ h a a' => flatCoord_ne h a a') _ w hw, Matrix.sum_apply,
    Finset.sum_eq_single j]
  · simp [mul_apply, coordEmbedding, conjTranspose_apply, (flatCoord_injective j).eq_iff]
  · intro j' _ hj'
    have h : ∀ c, flatCoord Dj j β ≠ flatCoord Dj j' c := fun c => flatCoord_ne (Ne.symm hj') β c
    simp [mul_apply, coordEmbedding, conjTranspose_apply, h]
  · simp

/-- The isometries of injective blocked tensors with orthogonal physical matrices have
orthonormal columns jointly: for two bond pairs `(j, l, r)` and `(j', l', r')`,
`⟨V_j|l, r⟩, V_{j'}|l', r'⟩⟩ = δ`. -/
theorem sum_star_polarIsoMatrix_mul (A : (j : Fin b) → MPSTensor d (Dj j)) {q : ℕ}
    (hinj : ∀ j, Kraus.IsInjective (blockTensor (A j) q))
    (horth : ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (A j) q))ᴴ *
      physicalMatrix (blockTensor (A j') q) = 0)
    (p p' : (j : Fin b) × (Fin (Dj j) × Fin (Dj j))) :
    ∑ σ : Fin q → Fin d,
      star (polarIsoMatrix (blockTensor (A p.1) q) ((decodeBlockEquiv d q).symm σ)
        (finProdFinEquiv p.2)) *
      polarIsoMatrix (blockTensor (A p'.1) q) ((decodeBlockEquiv d q).symm σ)
        (finProdFinEquiv p'.2) = if p = p' then 1 else 0 := by
  classical
  rw [(decodeBlockEquiv d q).symm.sum_comp (fun t =>
    star (polarIsoMatrix (blockTensor (A p.1) q) t (finProdFinEquiv p.2)) *
      polarIsoMatrix (blockTensor (A p'.1) q) t (finProdFinEquiv p'.2))]
  obtain ⟨j, lr⟩ := p
  obtain ⟨j', lr'⟩ := p'
  by_cases hj : j = j'
  · subst hj
    have h := congrFun (congrFun (isIsometry_polarIsoMatrix_of_isInjective (hinj j))
      (finProdFinEquiv lr)) (finProdFinEquiv lr')
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [conjTranspose_apply] at h
    rw [h]
    refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
    · rw [finProdFinEquiv.injective h]
    · rw [eq_of_heq (Sigma.mk.inj h).2]
  · have h := congrFun (congrFun (Matrix.conjTranspose_polarIso_mul_polarIso_eq_zero
      (horth j j' hj)) lr) lr'
    rw [Matrix.mul_apply] at h
    simp only [conjTranspose_apply, Matrix.zero_apply] at h
    rw [ite_eq_right fun h' => hj (Sigma.mk.inj h').1]
    simpa [polarIsoMatrix, virtualPairEquiv] using h

/-- **Counting the bond pairs.** If the blocked tensors of the `A_j` on `q` sites are injective
and the physical matrices of distinct blocks are orthogonal, the isometries `V_j` have jointly
orthonormal columns, so `∑ⱼ Dⱼ² ≤ d^q`. -/
theorem sum_mul_self_le_pow (A : (j : Fin b) → MPSTensor d (Dj j)) {q : ℕ}
    (hinj : ∀ j, Kraus.IsInjective (blockTensor (A j) q))
    (horth : ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (A j) q))ᴴ *
      physicalMatrix (blockTensor (A j') q) = 0) :
    ∑ j, Dj j * Dj j ≤ d ^ q := by
  classical
  let κ := (j : Fin b) × (Fin (Dj j) × Fin (Dj j))
  let V : Matrix (Fin (blockPhysDim d q)) κ ℂ := Matrix.of fun t p =>
    polarIsoMatrix (blockTensor (A p.1) q) t (finProdFinEquiv p.2)
  have hV : Vᴴ * V = 1 := by
    ext p p'
    rw [Matrix.mul_apply, Matrix.one_apply, ← sum_star_polarIsoMatrix_mul A hinj horth p p',
      ← (decodeBlockEquiv d q).symm.sum_comp]
    rfl
  have hcard : Fintype.card κ = ∑ j, Dj j * Dj j := by simp [κ]
  have h := Matrix.rank_mul_le_right Vᴴ V
  rw [hV, Matrix.rank_one] at h
  have h' := Matrix.rank_le_card_height V
  have h'' : Fintype.card (Fin (blockPhysDim d q)) = d ^ q := by
    rw [Fintype.card_fin, blockPhysDim_eq_pow]
  omega

/-- **One block unitary for several blocks with orthogonal states.** Let the bond indices of all
blocks, `Fin (∑ⱼ Dⱼ)`, be encoded in `r₁ ≥ 1` sites by an injective `dig`. There is `C` such
that for all tensors `A_j` and every block length `q ≥ 3 r₁` at which every blocked tensor is
injective and the physical matrices of distinct blocks are orthogonal, some unitary `U` on `q`
sites, a product of at most `C q` gates on neighbouring sites, sends the input
`|l, 0 ⋯ 0, r⟩` of a bond pair `(l, r)` of block `j` to `V_j |l, r⟩`, with `V_j` the isometry
of the polar decomposition of the blocked tensor of `A_j`.

arXiv:2307.01696, paragraph "Long-range MPS using measurements" (the isometry of the blocked
tensor of a tensor that is not normal, implemented "following the same steps" as for normal
tensors) and eqs. (13)–(15). The blocks enter only through `V_j`: the isometry of the direct
sum, `V = ∑ⱼ V_j K_jᴴ` (`MPSTensor.polarIso_blockTensor_blockSum`), agrees with `U` on these
inputs. -/
theorem exists_blockSumUnitary (hd : 0 < d) {r₁ : ℕ} (hr₁ : 1 ≤ r₁)
    {dig : Fin (∑ j, Dj j) → Cfg d r₁} (hdig : Function.Injective dig) (hD : 0 < ∑ j, Dj j) :
    ∃ C : ℕ, ∀ (A : (j : Fin b) → MPSTensor d (Dj j)) (q : ℕ), 3 * r₁ ≤ q →
      (∀ j, Kraus.IsInjective (blockTensor (A j) q)) →
      (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (A j) q))ᴴ *
        physicalMatrix (blockTensor (A j') q) = 0) →
      ∃ U : Matrix (Cfg d q) (Cfg d q) ℂ, IsPairProduct d q (C * q) U ∧
        ∀ j l r τ, U τ (blockInputCfg hd q dig (flatCoord Dj j l) (flatCoord Dj j r)) =
          polarIsoMatrix (blockTensor (A j) q) ((decodeBlockEquiv d q).symm τ)
            (finProdFinEquiv (l, r)) := by
  classical
  let κ := (j : Fin b) × (Fin (Dj j) × Fin (Dj j))
  let pairOf : κ → Fin (∑ j, Dj j) × Fin (∑ j, Dj j) := fun p =>
    (flatCoord Dj p.1 p.2.1, flatCoord Dj p.1 p.2.2)
  have hpairOf : Function.Injective pairOf := by
    rintro ⟨j, l, r⟩ ⟨j', l', r'⟩ h
    simp only [pairOf, Prod.mk.injEq] at h
    have hj : j = j' := by
      by_contra hj
      exact flatCoord_ne hj l l' h.1
    subst hj
    rw [flatCoord_injective j h.1, flatCoord_injective j h.2]
  set r := Fintype.card κ
  let eκ : κ ≃ Fin r := Fintype.equivFin κ
  have hr : r ≤ (∑ j, Dj j) * (∑ j, Dj j) := by
    have := Fintype.card_le_of_injective pairOf hpairOf
    simpa using this
  -- Extend the injection `pairOf ∘ eκ.symm` on the first `r` inputs to a bijection.
  obtain ⟨π, hπ⟩ : ∃ π : Fin ((∑ j, Dj j) * (∑ j, Dj j)) ≃ Fin (∑ j, Dj j) × Fin (∑ j, Dj j),
      ∀ x, π (Fin.castLE hr x) = (pairOf ∘ eκ.symm) x := by
    set f := Function.extend (Fin.castLE hr) (pairOf ∘ eκ.symm) finProdFinEquiv.symm
    have hf : ∀ x, f (Fin.castLE hr x) = (pairOf ∘ eκ.symm) x :=
      (Fin.castLE_injective hr).extend_apply _ _
    have hinj : Set.InjOn f (Set.range (Fin.castLE hr)) := by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
      rw [hf, hf] at h
      rw [(hpairOf.comp eκ.symm.injective) h]
    obtain ⟨π, hπ⟩ := Set.MapsTo.exists_equiv_extend_of_card_eq (t := Finset.univ)
      (by simp) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
    exact ⟨π.trans (Equiv.subtypeUnivEquiv Finset.mem_univ), fun x => by
      rw [Equiv.trans_apply, Equiv.subtypeUnivEquiv_apply, hπ _ ⟨x, rfl⟩, hf]⟩
  obtain ⟨C, hC⟩ := exists_blockUnitary_of_equiv hd hr₁ hdig hD π
  refine ⟨C, fun A q hq hinj horth => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  -- The isometry `(j, l, r) ↦ V_j |l, r⟩` on the first `r` inputs.
  let Vp : κ → (Fin (n + 1) → Fin d) → ℂ := fun p σ =>
    polarIsoMatrix (blockTensor (A p.1) (n + 1)) ((decodeBlockEquiv d (n + 1)).symm σ)
      (finProdFinEquiv p.2)
  let V : (Fin (n + 1) → Fin d) → Fin ((∑ j, Dj j) * (∑ j, Dj j)) → ℂ := fun σ x =>
    if h : x.val < r then Vp (eκ.symm ⟨x, h⟩) σ else 0
  let Pinv : (j : Fin b) → Matrix (Fin (Dj j * Dj j)) (Fin (Dj j * Dj j)) ℂ := fun j =>
    (Matrix.polarPos (physicalMatrix (blockTensor (A j) (n + 1))))⁻¹.submatrix
      (virtualPairEquiv (Dj j)) (virtualPairEquiv (Dj j))
  let G : Matrix (Fin ((∑ j, Dj j) * (∑ j, Dj j))) (Fin ((∑ j, Dj j) * (∑ j, Dj j))) ℂ :=
    Matrix.of fun a x =>
      if h : x.val < r then
        ∑ c : Fin (Dj (eκ.symm ⟨x, h⟩).1 * Dj (eκ.symm ⟨x, h⟩).1),
          (if virtualPairEquiv (∑ j, Dj j) a =
              (flatCoord Dj (eκ.symm ⟨x, h⟩).1 (virtualPairEquiv _ c).1,
                flatCoord Dj (eκ.symm ⟨x, h⟩).1 (virtualPairEquiv _ c).2) then 1 else 0) *
          Pinv (eκ.symm ⟨x, h⟩).1 c (finProdFinEquiv (eκ.symm ⟨x, h⟩).2)
      else 0
  have hw : ∀ σ : Fin (n + 1) → Fin d, List.ofFn σ ≠ [] := fun σ => by simp
  have hV : ∀ σ x, x.val < r → V σ x = ∑ a, Kraus.evalWord (blockSum A (flatCoord Dj)
      fun _ => 1) (List.ofFn σ) (virtualPairEquiv (∑ j, Dj j) a).1
        (virtualPairEquiv (∑ j, Dj j) a).2 * G a x := by
    intro σ x hx
    simp only [V, G, dite_eq_left hx, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [Vp]
    rw [polarIsoMatrix_blockTensor_eq_sum _ (hinj _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single ((virtualPairEquiv (∑ j, Dj j)).symm
      (flatCoord Dj _ (virtualPairEquiv _ c).1, flatCoord Dj _ (virtualPairEquiv _ c).2))]
    · rw [Equiv.apply_symm_apply, ite_eq_left rfl, one_mul, evalWord_blockSum_flatCoord A (hw σ)]
    · intro a _ ha
      rw [ite_eq_right fun h => ha (by rw [← h, Equiv.symm_apply_apply]), zero_mul, mul_zero]
    · simp
  have hiso : ∀ x y, x.val < r → y.val < r →
      ∑ σ, star (V σ x) * V σ y = if x = y then 1 else 0 := fun x y hx hy => by
    simp only [V, dite_eq_left hx, dite_eq_left hy]
    rw [sum_star_polarIsoMatrix_mul A hinj horth]
    refine if_congr ⟨fun h => ?_, fun h => by subst h; rfl⟩ rfl rfl
    have := congrArg Fin.val (eκ.symm.injective h)
    exact Fin.ext this
  obtain ⟨bb, Q, hb0, hbl, -, hrow, -, hisoQ, hVQ⟩ :=
    exists_isometric_chain_of_eq_mul_of_le (fun _ => blockSum A (flatCoord Dj) fun _ => 1) hr G V
      (fun σ x hx => by rw [MPSChainTensor.eval_const]; exact hV σ x hx) hiso
  obtain ⟨U, hUpp, hUQ⟩ := hC (n + 1) hq bb Q hb0 hrow hisoQ
  refine ⟨U, hUpp, fun j l r' τ => ?_⟩
  set x : Fin ((∑ j, Dj j) * (∑ j, Dj j)) := Fin.castLE hr (eκ ⟨j, (l, r')⟩) with hxdef
  have hx : x.val < r := (eκ ⟨j, (l, r')⟩).isLt
  have hπx : π x = (flatCoord Dj j l, flatCoord Dj j r') := by
    rw [hxdef, hπ, Function.comp_apply, Equiv.symm_apply_apply]
  have hU := hUQ x (by rw [hbl]; exact hx) τ
  rw [hπx] at hU
  rw [hU, ← hVQ τ x hx]
  have hsymm : ∀ h : x.val < r, eκ.symm ⟨x.val, h⟩ = ⟨j, (l, r')⟩ := fun h => by
    rw [Equiv.symm_apply_eq]; exact Fin.ext rfl
  change (if h : x.val < r then Vp (eκ.symm ⟨x.val, h⟩) τ else 0) = Vp ⟨j, (l, r')⟩ τ
  rw [dite_eq_left hx, hsymm hx]

end MPSPreparation
