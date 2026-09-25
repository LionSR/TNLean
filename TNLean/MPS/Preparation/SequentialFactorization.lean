/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockedPolar
import TNLean.MPS.Preparation.IsometricChain

/-!
# Sequential factorization of the isometry of a blocked tensor

For an injective `q`-site blocked tensor `B` with polar decomposition `B = V P`, the
isometry `V : ℂ^{D²} → (ℂ^d)^{⊗q}` is `B P⁻¹`. Read site by site, `B P⁻¹` is an
open-boundary matrix product map with bond space `ℂ^D ⊗ ℂ^D`: the site matrices are
`1_D ⊗ A^i`, the left end joins the two bond factors, and `P⁻¹` is absorbed into the
right end, where the input `|α, β⟩` enters. Successive decompositions from the left
make every site map an isometry, and the remainder left at the right end is an
isometry because `V` is. This is arXiv:2307.01696, eqs. (13)–(15).

The chain is stored as in `TNLean.MPS.Preparation.IsometricChain`: square
`D² × D²` site matrices `Q_p(i)` together with bond dimensions `b₀, …, b_q`, where
`Q_p(i)` vanishes outside the upper-left `b_p × b_{p+1}` block and the site map
`|β⟩ ↦ ∑_{α,i} Q_p(i)_{αβ} |α⟩|i⟩` is isometric on the first `b_{p+1}` levels. The
factorization reads `⟨σ| V |x⟩ = (Q₀(σ₀) ⋯ Q_{q-1}(σ_{q-1}))_{0x}`, with `b₀ = 1` (the
output end), `b_q = D²` (the input), and every bond at most `D²`. In the notation
of the source, `Q_p` is the isometry `V_{q-p}` of eq. (14) and `b_p = D'_{q+1-p}`.

## Main results

* `MPSPreparation.exists_isometric_chain_of_eq_mul` — the factorization for any
  isometry of the form `⟨σ|V|x⟩ = ∑_{α,β} (A^{σ₁} ⋯ A^{σ_q})_{αβ} G_{(α,β),x}`.
* `MPSPreparation.exists_isometric_chain_polarIsoMatrix` — the isometric factor of
  the polar decomposition of an injective blocked tensor factors into `q`
  isometries with bonds at most `D²`, arXiv:2307.01696, eqs. (13)–(15).

## References

* Malz, Styliaris, Wei, Cirac, *Preparation of matrix product states with log-depth
  quantum circuits*, arXiv:2307.01696, eqs. (13), (14), (15) and the paragraph
  between them.
-/

open scoped BigOperators Matrix Kronecker ComplexOrder

namespace MPSPreparation

open MPSChainTensor (eval eval_succ eval_succ')
open MPSTensor (blockTensor decodeBlockEquiv virtualPairEquiv)

variable {d D : ℕ}

/-- The embedding `X ↦ 1_D ⊗ X` of `D × D` matrices into matrices on the pair space
`ℂ^D ⊗ ℂ^D ≅ ℂ^{D²}`, as a monoid homomorphism. Its values on the letters of a tensor
are the site matrices `A'^i` of arXiv:2307.01696, eq. (13) (there written
`A^i ⊗ 1_D`; the order of the two bond factors is immaterial). Its underlying matrix
is that of `MPOTensor.idKron D X` in `TNLean.MPS.Core.ReductionComposition`, which is not
imported here because that module pulls in the matrix-product-operator layer; this
version adds the monoid-homomorphism packaging used by `eval_pairEmbed`. -/
noncomputable def pairEmbed (D : ℕ) :
    Matrix (Fin D) (Fin D) ℂ →* Matrix (Fin (D * D)) (Fin (D * D)) ℂ where
  toFun X := ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ X).submatrix (virtualPairEquiv D)
    (virtualPairEquiv D)
  map_one' := by simp [Matrix.submatrix_one_equiv]
  map_mul' X Y := by
    rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- The ordered product of the embedded letters along a word is the embedding of the
ordered product of the letters. -/
theorem eval_pairEmbed (A : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∀ {n : ℕ} (σ : Fin n → Fin d),
      eval (fun _ i => pairEmbed D (A i)) σ = pairEmbed D (Kraus.evalWord A (List.ofFn σ))
  | 0, σ => by simp
  | n + 1, σ => by
    rw [eval_succ, eval_pairEmbed A (fun k => σ k.succ), List.ofFn_succ,
      Kraus.evalWord_cons, map_mul]

/-- The vector `∑_γ |γ⟩ ⊗ |γ⟩` of the pair space, which joins the two bond factors at
the left end of the matrix product map of arXiv:2307.01696, eq. (13). -/
def pairJoin (D : ℕ) : Fin (D * D) → ℂ :=
  fun a => if (virtualPairEquiv D a).1 = (virtualPairEquiv D a).2 then 1 else 0

/-- Joining the two bond factors of `1_D ⊗ X` on the left reads off the entries of
`X`: `∑_a j_a (1 ⊗ X)_{a,(α,β)} = X_{αβ}`. -/
theorem sum_pairJoin_mul_pairEmbed (X : Matrix (Fin D) (Fin D) ℂ) (b : Fin (D * D)) :
    ∑ a, pairJoin D a * pairEmbed D X a b =
      X (virtualPairEquiv D b).1 (virtualPairEquiv D b).2 := by
  classical
  obtain ⟨⟨β₁, β₂⟩, rfl⟩ := (virtualPairEquiv D).symm.surjective b
  rw [← (virtualPairEquiv D).symm.sum_comp, Fintype.sum_prod_type]
  simp [pairJoin, pairEmbed, Matrix.one_apply, ite_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- Two vectors supported on the first coordinate pair through that coordinate. -/
private theorem star_dotProduct_of_isSupportedBelow_one {D' : ℕ} (hD : 0 < D')
    {u v : Fin D' → ℂ} (hu : IsSupportedBelow 1 u) :
    star u ⬝ᵥ v = star (u ⟨0, hD⟩) * v ⟨0, hD⟩ := by
  rw [dotProduct, Finset.sum_eq_single ⟨0, hD⟩]
  · rfl
  · intro α _ hα
    have : 1 ≤ α.val := Nat.one_le_iff_ne_zero.mpr fun h => hα (Fin.ext h)
    simp [hu α this]
  · simp

/-- **Sequential factorization of an isometry given by a matrix product.** Let `V`
be an isometry from `ℂ^{D²}` to `(ℂ^d)^{⊗(n+1)}` whose matrix elements are
`⟨σ|V|x⟩ = ∑_{α,β} (A^{σ₀} ⋯ A^{σ_n})_{αβ} G_{(α,β),x}`. Then there are bond
dimensions `b₀ = 1`, `b_{n+1} = D²`, all at most `D²`, and site matrices `Q_p`
vanishing outside the `b_p × b_{p+1}` block and isometric on it, with
`⟨σ|V|x⟩ = (Q₀(σ₀) ⋯ Q_n(σ_n))_{0x}`.

arXiv:2307.01696, eqs. (13)–(15): the map is the open-boundary product of the site
matrices `1_D ⊗ A^i` with the two bond factors joined on the left and `G` absorbed on
the right (eq. (13)); successive decompositions from the left make every site
isometric (eq. (14)); and the remainder is an isometry because `V` is, so absorbing
it into the last site keeps that site isometric (eq. (15)). Here `G` plays the role
of `P⁻¹`. -/
theorem exists_isometric_chain_of_eq_mul (A : Fin d → Matrix (Fin D) (Fin D) ℂ) (n : ℕ)
    (G : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) (V : (Fin (n + 1) → Fin d) → Fin (D * D) → ℂ)
    (hV : ∀ σ x, V σ x = ∑ a, Kraus.evalWord A (List.ofFn σ) (virtualPairEquiv D a).1
      (virtualPairEquiv D a).2 * G a x)
    (hiso : ∀ x y, ∑ σ, star (V σ x) * V σ y = if x = y then 1 else 0) :
    ∃ (b : Fin (n + 2) → ℕ) (Q : MPSChainTensor d (D * D) (n + 1)),
      b 0 = 1 ∧ b (Fin.last (n + 1)) = D * D ∧ (∀ p : Fin (n + 1), b p.succ ≤ D * D) ∧
      (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) ∧
      (∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0) ∧
      (∀ p, IsIsometryOn (b p.succ) (Q p)) ∧
      ∀ σ x, V σ x = eval Q σ ⟨0, x.pos⟩ x := by
  classical
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · refine ⟨fun k => if k = 0 then 1 else 0, fun _ _ => 0, by simp, by simp [Fin.ext_iff],
      fun p => by simp [Fin.succ_ne_zero], fun _ _ α => absurd α.pos (by simp),
      fun _ _ α => absurd α.pos (by simp), fun _ β => absurd β.pos (by simp),
      fun _ x => absurd x.pos (by simp)⟩
  have hDD : 0 < D * D := Nat.mul_pos hD hD
  -- The open-boundary product of eq. (13), swept from the left (eq. (14)).
  obtain ⟨b, Q, R, hb0, hbD, -, hrow, hcol, hisoQ, hR, hprod⟩ :=
    exists_isometric_chain_mul (n + 1) 1 hDD (rowMat (pairJoin D))
      (isRowSupportedBelow_rowMat _) fun _ i => pairEmbed D (A i)
  set C := R * G with hCdef
  have hC : IsRowSupportedBelow (b (Fin.last (n + 1))) C := hR.mul G
  have hjoin : ∀ (σ : Fin (n + 1) → Fin d) a,
      (rowMat (pairJoin D) * eval (fun _ i => pairEmbed D (A i)) σ) ⟨0, hDD⟩ a =
      Kraus.evalWord A (List.ofFn σ) (virtualPairEquiv D a).1 (virtualPairEquiv D a).2 :=
    fun σ a => by
      rw [eval_pairEmbed, Matrix.mul_apply]
      exact (Finset.sum_congr rfl fun j _ => by simp [rowMat]).trans
        (sum_pairJoin_mul_pairEmbed _ a)
  have hVC : ∀ σ x, V σ x = (eval Q σ * C) ⟨0, hDD⟩ x := fun σ x => by
    rw [hCdef, ← Matrix.mul_assoc, ← hprod σ, hV σ x, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [hjoin]
  -- The columns of the remainder are orthonormal because `V` is an isometry (eq. (15)).
  let col : Fin (D * D) → Fin (D * D) → ℂ := fun x β => C β x
  have hcol_supp : ∀ x, IsSupportedBelow (b (Fin.last (n + 1))) (col x) :=
    fun x β hβ => hC β x hβ
  have hCiso : ∀ x y, star (col x) ⬝ᵥ col y = if x = y then 1 else 0 := fun x y => by
    rw [← sum_star_eval_mulVec_dotProduct b Q hrow hisoQ _ _ (hcol_supp x) (hcol_supp y),
      ← hiso x y]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hsupp := isSupportedBelow_eval_mulVec b Q hrow _ (hcol_supp x) σ
    rw [hb0] at hsupp
    rw [star_dotProduct_of_isSupportedBelow_one hDD hsupp, hVC, hVC]
    simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  -- Absorb the remainder into the last site.
  let b' : Fin (n + 2) → ℕ := fun k => if k = Fin.last (n + 1) then D * D else b k
  let Q' : MPSChainTensor d (D * D) (n + 1) := fun p i =>
    if p = Fin.last n then Q p i * C else Q p i
  have hcs : ∀ p : Fin (n + 1), b' p.castSucc = b p.castSucc := fun p => by
    simp [b', Fin.castSucc_ne_last]
  have hsc : ∀ p : Fin (n + 1), p ≠ Fin.last n → b' p.succ = b p.succ := fun p hp => by
    have : p.succ ≠ Fin.last (n + 1) := by
      rw [← Fin.succ_last]; exact fun h => hp (Fin.succ_injective _ h)
    simp [b', this]
  refine ⟨b', Q', ?_, by simp [b'], fun p => ?_, fun p i => ?_, fun p i α β hβ => ?_,
    fun p => ?_, fun σ x => ?_⟩
  · have : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by simp [Fin.ext_iff]
    simp [b', this, hb0]
  · by_cases hp : p = Fin.last n
    · subst hp; simp [b']
    · rw [hsc p hp]; exact hbD _
  · rw [hcs]; simp only [Q']; split_ifs
    · exact (hrow p i).mul _
    · exact hrow p i
  · by_cases hp : p = Fin.last n
    · subst hp
      simp only [b', Fin.succ_last, ite_true] at hβ
      exact absurd β.isLt (not_lt.mpr hβ)
    · rw [hsc p hp] at hβ
      simp only [Q', hp, ite_false]
      exact hcol p i α β hβ
  · by_cases hp : p = Fin.last n
    · subst hp
      intro x y _ _
      have h := sum_star_mulVec_dotProduct_of_isometryOn (hisoQ (Fin.last n))
        (v := col x) (w := col y) (by rw [Fin.succ_last]; exact hcol_supp x)
        (by rw [Fin.succ_last]; exact hcol_supp y)
      rw [hCiso] at h
      rw [← h]
      simp [Q', col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    · rw [hsc p hp]
      simpa [Q', hp] using hisoQ p
  · rw [hVC]
    have hQ' : (fun p : Fin n => Q' p.castSucc) = fun p => Q p.castSucc := by
      funext p i; simp [Q', Fin.castSucc_ne_last]
    rw [eval_succ' Q', hQ', eval_succ' Q]
    simp only [Q', ite_true, Matrix.mul_assoc]

/-- **Sequential factorization of the isometry** of the polar decomposition of an
injective blocked tensor. Let `A` be a tensor with bond dimension `D`, let `q ≥ 1`,
and suppose the `q`-site blocked tensor `B` is injective, so that its polar
decomposition `B = V P` has an isometry `V : ℂ^{D²} → (ℂ^d)^{⊗q}`. Then there are
bond dimensions `b₀ = 1`, `b_q = D²`, and `b_p ≤ D²`, and site matrices `Q_p`,
vanishing outside the `b_p × b_{p+1}` block, whose site maps
`ℂ^{b_{p+1}} → ℂ^{b_p} ⊗ ℂ^d` are isometries, such that
`⟨σ₁ ⋯ σ_q| V |x⟩ = (Q₀(σ₁) ⋯ Q_{q-1}(σ_q))_{0x}` for every configuration and every
input `x` of `ℂ^{D²}`. Equivalently, `V` is the ordered composition of the `q`
isometries, each acting on one site and the bond to its left.

arXiv:2307.01696, eqs. (13)–(15): `V = V_q ⋯ V_1` with isometries
`V_i : ℂ^{D'_i} → ℂ^{d D'_{i+1}}`, `D'_i ≤ D²`, `D'_{q+1} = 1`, where the last factor
`C̃ = V_1`, carrying the input `ℂ^{D²}`, is an isometry by eq. (15). In the notation
here `Q_p = V_{q-p}` and `b_p = D'_{q+1-p}`. The block length `q ≥ 1` is implicit in
the source, which draws at least one site. -/
theorem exists_isometric_chain_polarIsoMatrix (A : MPSTensor d D) {q : ℕ} (hq : 0 < q)
    (hB : Kraus.IsInjective (blockTensor A q)) :
    ∃ (b : Fin (q + 1) → ℕ) (Q : MPSChainTensor d (D * D) q),
      b 0 = 1 ∧ b (Fin.last q) = D * D ∧ (∀ p : Fin q, b p.succ ≤ D * D) ∧
      (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) ∧
      (∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0) ∧
      (∀ p, IsIsometryOn (b p.succ) (Q p)) ∧
      ∀ (σ : Fin q → Fin d) (x : Fin (D * D)),
        MPSTensor.polarIsoMatrix (blockTensor A q) ((decodeBlockEquiv d q).symm σ) x =
          eval Q σ ⟨0, x.pos⟩ x := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  set B := blockTensor A (n + 1) with hBdef
  set M := MPSTensor.physicalMatrix B
  let e := virtualPairEquiv D
  have hinj := MPSTensor.injective_physicalMatrix_mulVec_of_isInjective hB
  have hdet : IsUnit (Matrix.polarPos M).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.posDef_polarPos_of_injective M hinj).isUnit
  have hVM : Matrix.polarIso M = M * (Matrix.polarPos M)⁻¹ := by
    calc Matrix.polarIso M
        = Matrix.polarIso M * Matrix.polarPos M * (Matrix.polarPos M)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = M * (Matrix.polarPos M)⁻¹ := by rw [Matrix.polarIso_mul_polarPos]
  let V : (Fin (n + 1) → Fin d) → Fin (D * D) → ℂ := fun σ x =>
    MPSTensor.polarIsoMatrix B ((decodeBlockEquiv d (n + 1)).symm σ) x
  have hBσ : ∀ σ, B ((decodeBlockEquiv d (n + 1)).symm σ) =
      Kraus.evalWord A (List.ofFn σ) := fun σ => by
    simp only [hBdef, blockTensor, decodeBlockEquiv, Kraus.blockTensor, Kraus.wordOfBlock,
      Kraus.decodeBlock_decodeBlockEquiv_symm]
  have hV : ∀ σ x, V σ x = ∑ a, Kraus.evalWord A (List.ofFn σ) (e a).1 (e a).2 *
      ((Matrix.polarPos M)⁻¹.submatrix e e) a x := fun σ x => by
    change (Matrix.polarIso M) _ (e x) = _
    rw [hVM, Matrix.mul_apply, ← e.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [M, MPSTensor.physicalMatrix, hBσ, e]
  have hiso : ∀ x y, ∑ σ, star (V σ x) * V σ y = if x = y then 1 else 0 := fun x y => by
    have h := congrFun (congrFun
      (MPSTensor.isIsometry_polarIsoMatrix_of_isInjective hB) x) y
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h, ← (decodeBlockEquiv d (n + 1)).symm.sum_comp]
    rfl
  exact exists_isometric_chain_of_eq_mul A n _ V hV hiso

end MPSPreparation
