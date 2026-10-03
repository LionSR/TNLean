/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.BlockTensor
import TNLean.MPS.Preparation.BlockedPolar
import TNLean.MPS.Preparation.IsometricChain
import TNLean.MPS.Preparation.SupportedPolar

/-!
# Sequential factorization of the isometry of a blocked tensor

For an injective `q`-site blocked tensor `B` with polar decomposition `B = V P`, the
isometry `V : ℂ^{D²} → (ℂ^d)^{⊗q}` is `B P⁻¹`. Read site by site, `B P⁻¹` is an
open-boundary matrix product map with bond space `ℂ^D ⊗ ℂ^D`: the site matrices are
`1_D ⊗ A_p^i`, where the tensors `A_p` may depend on the site `p`, the left end joins the two
bond factors, and `P⁻¹` is absorbed into the right end, where the input `|α, β⟩` enters.
Successive decompositions from the left make every site map an isometry, and the remainder left
at the right end is an isometry because `V` is. This is arXiv:2307.01696, eqs. (13)–(15).

The chain is stored as in `TNLean.MPS.Preparation.IsometricChain`: square
`D² × D²` site matrices `Q_p(i)` together with bond dimensions `b₀, …, b_q`, where
`Q_p(i)` vanishes outside the upper-left `b_p × b_{p+1}` block and the site map
`|β⟩ ↦ ∑_{α,i} Q_p(i)_{αβ} |α⟩|i⟩` is isometric on the first `b_{p+1}` levels. The
factorization reads `⟨σ| V |x⟩ = (Q₀(σ₀) ⋯ Q_{q-1}(σ_{q-1}))_{0x}`, with `b₀ = 1` (the
output end), `b_q = D²` (the input), and `b₁, …, b_q ≤ D²`. In the notation
of the source, `Q_p` is the isometry `V_{q-p}` of eq. (14) and `b_p = D'_{q+1-p}`.

## Main results

* `MPSPreparation.exists_isometric_chain_of_eq_mul` — the factorization for any
  isometry of the form `⟨σ|V|x⟩ = ∑_{α,β} (A_1^{σ₁} ⋯ A_q^{σ_q})_{αβ} G_{(α,β),x}`.
* `MPSPreparation.exists_isometric_chain_polarIsoMatrix_of_isInjectiveOn` — the factorization
  of the isometric factor of a blocked tensor injective on a set of bond pairs, on the inputs of
  that set.
* `MPSPreparation.exists_isometric_chain_polarIsoMatrix_mul_unitary` — the factorization of the
  partial isometry of any blocked tensor, with no injectivity, after a unitary `T` that puts the
  range of the support projector on the first `r` inputs (the footnote to "The sequential-RG
  circuit", with `P⁻¹` the pseudo-inverse).
* `MPSPreparation.exists_isometric_chain_polarIsoMatrix` — the isometric factor of
  the polar decomposition of an injective blocked tensor of a chain of site-dependent
  tensors factors into `q` isometries with bonds `b₁, …, b_q` at most `D²`,
  arXiv:2307.01696, eqs. (13)–(15), and the paragraph "Inhomogeneous short-range
  correlated MPS" for tensors that depend on the site.

For the source's inhomogeneous states with "bond dimension at most `D`" varying along the
ring, the chain is padded with zeros (`VaryingBondChain.zeroPad`); its blocked
tensors are then injective only on the rectangle of their bonds, and
`MPSPreparation.exists_isometric_chain_polarIsoMatrix_of_isInjectiveOn` factorizes the isometric
factor on those inputs.

**Scope restriction (positive block length):** the hypothesis `0 < q` of
`MPSPreparation.exists_isometric_chain_polarIsoMatrix`,
`MPSPreparation.exists_isometric_chain_polarIsoMatrix_of_isInjectiveOn` and
`MPSPreparation.exists_isometric_chain_polarIsoMatrix_mul_unitary` is absent from
arXiv:2307.01696, eqs. (13)–(15) and the footnote to "The sequential-RG circuit", which state
no lower bound on the block length. The empty block `q = 0` is injective, or injective on a set
`S` of bond pairs, only for `D ≤ 1`; the conclusion holds trivially at `D = 1` and fails at
`D = 0`, where `b₀ = 1` and `b₀ = D²`, or `b₀ = |S| = 0`, name the same bond. Without
injectivity, the conclusion fails at `q = 0` for every `D`: `r = 0` contradicts `b₀ = 1` when
`D = 0`, and for `D ≥ 1` it asks the unit-modulus scalar `V T |0⟩` to equal `1`, which a sign
on the first column of `T` breaks. Documented in
`docs/paper-gaps/mswc24_sequential_factorization_positive_block_length.tex`.

## References

* Malz, Styliaris, Wei, Cirac, *Preparation of matrix product states with log-depth
  quantum circuits*, arXiv:2307.01696, eqs. (13), (14), (15) and the paragraph
  between them, the paragraph "Inhomogeneous short-range correlated MPS", and Supplemental
  Material, "Proof of Lemma 1 and extension to non-normal tensors".
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

/-- The ordered product of the embedded letters along a chain is the embedding of the
ordered product of the letters. -/
theorem eval_pairEmbed :
    ∀ {n : ℕ} (A : MPSChainTensor d D n) (σ : Fin n → Fin d),
      eval (fun p i => pairEmbed D (A p i)) σ = pairEmbed D (eval A σ)
  | 0, A, σ => by simp
  | n + 1, A, σ => by
    rw [eval_succ, eval_pairEmbed (fun p => A p.succ) (fun k => σ k.succ), eval_succ A,
      map_mul]

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

/-- **Sequential factorization of a matrix product map isometric on its first inputs.** Let
`V : ℂ^{D²} → (ℂ^d)^{⊗(n+1)}` have matrix elements
`⟨σ|V|x⟩ = ∑_{α,β} (A_0^{σ₀} ⋯ A_n^{σ_n})_{αβ} G_{(α,β),x}` for the inputs `x < r`, for tensors
`A_0, …, A_n` which may depend on the site, and let these
`r ≤ D²` columns be orthonormal. Then there are bond dimensions `b₀ = 1`, `b_{n+1} = r` and
`b₁, …, b_{n+1} ≤ D²`, and site matrices `Q_p` vanishing outside the `b_p × b_{p+1}` block and
isometric on it, with `⟨σ|V|x⟩ = (Q₀(σ₀) ⋯ Q_n(σ_n))_{0x}` for `x < r`.

For `r = D²` this is `exists_isometric_chain_of_eq_mul`, arXiv:2307.01696, eqs. (13)–(15), with
site-dependent tensors as in the paragraph "Inhomogeneous short-range correlated MPS". The
inputs `x ≥ r` are discarded: the remainder of the sweep is applied only to the first `r`
columns of `G`, which are orthonormal after the sweep because the columns of `V` are, so
absorbing it into the last site keeps that site isometric on its first `r` levels. -/
theorem exists_isometric_chain_of_eq_mul_of_le {n : ℕ} (A : MPSChainTensor d D (n + 1))
    {r : ℕ} (hr : r ≤ D * D) (G : Matrix (Fin (D * D)) (Fin (D * D)) ℂ)
    (V : (Fin (n + 1) → Fin d) → Fin (D * D) → ℂ)
    (hV : ∀ σ x, x.val < r → V σ x = ∑ a, eval A σ
      (virtualPairEquiv D a).1 (virtualPairEquiv D a).2 * G a x)
    (hiso : ∀ x y, x.val < r → y.val < r →
      ∑ σ, star (V σ x) * V σ y = if x = y then 1 else 0) :
    ∃ (b : Fin (n + 2) → ℕ) (Q : MPSChainTensor d (D * D) (n + 1)),
      b 0 = 1 ∧ b (Fin.last (n + 1)) = r ∧ (∀ p : Fin (n + 1), b p.succ ≤ D * D) ∧
      (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) ∧
      (∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0) ∧
      (∀ p, IsIsometryOn (b p.succ) (Q p)) ∧
      ∀ σ x, x.val < r → V σ x = eval Q σ ⟨0, x.pos⟩ x := by
  classical
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · refine ⟨fun k => if k = 0 then 1 else r, fun _ _ => 0, by simp,
      by simp [Fin.ext_iff], fun p => by simpa [Fin.succ_ne_zero] using hr,
      fun _ _ α => absurd α.pos (by simp), fun _ _ α => absurd α.pos (by simp),
      fun _ β => absurd β.pos (by simp), fun _ x => absurd x.pos (by simp)⟩
  have hDD : 0 < D * D := Nat.mul_pos hD hD
  -- Only the first `r` columns of `G` are kept.
  set G' : Matrix (Fin (D * D)) (Fin (D * D)) ℂ := Matrix.of fun a x =>
    if x.val < r then G a x else 0 with hG'
  -- The open-boundary product of eq. (13), swept from the left (eq. (14)).
  obtain ⟨b, Q, R, hb0, hbD, -, hrow, hcol, hisoQ, hR, hprod⟩ :=
    exists_isometric_chain_mul (n + 1) 1 hDD (rowMat (pairJoin D))
      (isRowSupportedBelow_rowMat _) fun p i => pairEmbed D (A p i)
  set C := R * G' with hCdef
  have hC : IsRowSupportedBelow (b (Fin.last (n + 1))) C := hR.mul G'
  have hCr : ∀ γ x, r ≤ x.val → C γ x = 0 := fun γ x hx => by
    simp [hCdef, hG', Matrix.mul_apply, show ¬x.val < r by omega]
  have hjoin : ∀ (σ : Fin (n + 1) → Fin d) a,
      (rowMat (pairJoin D) * eval (fun p i => pairEmbed D (A p i)) σ) ⟨0, hDD⟩ a =
      eval A σ (virtualPairEquiv D a).1 (virtualPairEquiv D a).2 :=
    fun σ a => by
      rw [eval_pairEmbed, Matrix.mul_apply]
      exact (Finset.sum_congr rfl fun j _ => by simp [rowMat]).trans
        (sum_pairJoin_mul_pairEmbed _ a)
  have hVC : ∀ σ x, x.val < r → V σ x = (eval Q σ * C) ⟨0, hDD⟩ x := fun σ x hx => by
    rw [hCdef, ← Matrix.mul_assoc, ← hprod σ, hV σ x hx, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [hjoin, hG', Matrix.of_apply, ite_eq_left hx]
  -- The first `r` columns of the remainder are orthonormal because those of `V` are
  -- (eq. (15)).
  let col : Fin (D * D) → Fin (D * D) → ℂ := fun x β => C β x
  have hcol_supp : ∀ x, IsSupportedBelow (b (Fin.last (n + 1))) (col x) :=
    fun x β hβ => hC β x hβ
  have hCiso : ∀ x y, x.val < r → y.val < r →
      star (col x) ⬝ᵥ col y = if x = y then 1 else 0 := fun x y hx hy => by
    rw [← sum_star_eval_mulVec_dotProduct b Q hrow hisoQ _ _ (hcol_supp x) (hcol_supp y),
      ← hiso x y hx hy]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hsupp := isSupportedBelow_eval_mulVec b Q hrow _ (hcol_supp x) σ
    rw [hb0] at hsupp
    rw [star_dotProduct_of_isSupportedBelow_one hDD hsupp, hVC σ x hx, hVC σ y hy]
    simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  -- Absorb the remainder into the last site.
  let b' : Fin (n + 2) → ℕ := fun k => if k = Fin.last (n + 1) then r else b k
  let Q' : MPSChainTensor d (D * D) (n + 1) := fun p i =>
    if p = Fin.last n then Q p i * C else Q p i
  have hcs : ∀ p : Fin (n + 1), b' p.castSucc = b p.castSucc := fun p => by
    simp [b', Fin.castSucc_ne_last]
  have hsc : ∀ p : Fin (n + 1), p ≠ Fin.last n → b' p.succ = b p.succ := fun p hp => by
    have : p.succ ≠ Fin.last (n + 1) := by
      rw [← Fin.succ_last]; exact fun h => hp (Fin.succ_injective _ h)
    simp [b', this]
  refine ⟨b', Q', ?_, by simp [b'], fun p => ?_, fun p i => ?_, fun p i α β hβ => ?_,
    fun p => ?_, fun σ x hx => ?_⟩
  · have : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by simp [Fin.ext_iff]
    simp [b', this, hb0]
  · by_cases hp : p = Fin.last n
    · subst hp; simpa [b'] using hr
    · rw [hsc p hp]; exact hbD _
  · rw [hcs]; simp only [Q']; split_ifs
    · exact (hrow p i).mul _
    · exact hrow p i
  · by_cases hp : p = Fin.last n
    · subst hp
      simp only [b', Fin.succ_last, ite_true] at hβ
      simp [Q', Matrix.mul_apply, hCr _ β hβ]
    · rw [hsc p hp] at hβ
      simp only [Q', hp, ite_false]
      exact hcol p i α β hβ
  · by_cases hp : p = Fin.last n
    · subst hp
      intro x y hx hy
      simp only [b', Fin.succ_last, ite_true] at hx hy
      have h := sum_star_mulVec_dotProduct_of_isIsometryOn (hisoQ (Fin.last n))
        (v := col x) (w := col y) (by rw [Fin.succ_last]; exact hcol_supp x)
        (by rw [Fin.succ_last]; exact hcol_supp y)
      rw [hCiso x y hx hy] at h
      rw [← h]
      simp [Q', col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    · rw [hsc p hp]
      simpa [Q', hp] using hisoQ p
  · rw [hVC σ x hx]
    have hQ' : (fun p : Fin n => Q' p.castSucc) = fun p => Q p.castSucc := by
      funext p i; simp [Q', Fin.castSucc_ne_last]
    rw [eval_succ' Q', hQ', eval_succ' Q]
    simp only [Q', ite_true, Matrix.mul_assoc]

/-- **Sequential factorization of an isometry given by a matrix product.** Let `V`
be an isometry from `ℂ^{D²}` to `(ℂ^d)^{⊗(n+1)}` whose matrix elements are
`⟨σ|V|x⟩ = ∑_{α,β} (A_0^{σ₀} ⋯ A_n^{σ_n})_{αβ} G_{(α,β),x}` for tensors `A_0, …, A_n`,
which may depend on the site. Then there are bond dimensions `b₀ = 1`, `b_{n+1} = D²` and
`b₁, …, b_{n+1} ≤ D²`, and site matrices `Q_p` vanishing outside the `b_p × b_{p+1}` block
and isometric on it, with
`⟨σ|V|x⟩ = (Q₀(σ₀) ⋯ Q_n(σ_n))_{0x}`.

arXiv:2307.01696, eqs. (13)–(15): the map is the open-boundary product of the site
matrices `1_D ⊗ A^i` with the two bond factors joined on the left and `G` absorbed on
the right (eq. (13)), here with a tensor `A_p` depending on the site as in the paragraph
"Inhomogeneous short-range correlated MPS"; successive decompositions from the left make
every site isometric (eq. (14)); and the remainder is an isometry because `V` is, so absorbing
it into the last site keeps that site isometric (eq. (15)). Here `G` plays the role
of `P⁻¹`. -/
theorem exists_isometric_chain_of_eq_mul {n : ℕ} (A : MPSChainTensor d D (n + 1))
    (G : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) (V : (Fin (n + 1) → Fin d) → Fin (D * D) → ℂ)
    (hV : ∀ σ x, V σ x = ∑ a, eval A σ (virtualPairEquiv D a).1
      (virtualPairEquiv D a).2 * G a x)
    (hiso : ∀ x y, ∑ σ, star (V σ x) * V σ y = if x = y then 1 else 0) :
    ∃ (b : Fin (n + 2) → ℕ) (Q : MPSChainTensor d (D * D) (n + 1)),
      b 0 = 1 ∧ b (Fin.last (n + 1)) = D * D ∧ (∀ p : Fin (n + 1), b p.succ ≤ D * D) ∧
      (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) ∧
      (∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0) ∧
      (∀ p, IsIsometryOn (b p.succ) (Q p)) ∧
      ∀ σ x, V σ x = eval Q σ ⟨0, x.pos⟩ x := by
  obtain ⟨b, Q, h0, hl, hb, hrow, hcol, hiso', hV'⟩ := exists_isometric_chain_of_eq_mul_of_le A
    le_rfl G V (fun σ x _ => hV σ x) (fun x y _ _ => hiso x y)
  exact ⟨b, Q, h0, hl, hb, hrow, hcol, hiso', fun σ x => hV' σ x x.isLt⟩

/-- The isometric factor of an injective blocked tensor `B = V P` of a chain of site-dependent
tensors `A₀, …, A_{q-1}` is `V = B P⁻¹`, read as a matrix product map:
`⟨σ|V|x⟩ = ∑_{α,β} (A_0^{σ₁} ⋯ A_{q-1}^{σ_q})_{αβ} (P⁻¹)_{(α,β),x}` (arXiv:2307.01696, eq. (13),
and the paragraph "Inhomogeneous short-range correlated MPS" for tensors that depend on the
site). -/
theorem polarIsoMatrix_chainBlockTensor_eq_sum {q : ℕ} (A : MPSChainTensor d D q)
    (hB : Kraus.IsInjective (MPSChainTensor.blockTensor A)) (σ : Fin q → Fin d)
    (x : Fin (D * D)) :
    MPSTensor.polarIsoMatrix (MPSChainTensor.blockTensor A) ((decodeBlockEquiv d q).symm σ) x =
      ∑ a, eval A σ (virtualPairEquiv D a).1 (virtualPairEquiv D a).2 *
        ((Matrix.polarPos (MPSTensor.physicalMatrix (MPSChainTensor.blockTensor A)))⁻¹.submatrix
          (virtualPairEquiv D) (virtualPairEquiv D)) a x := by
  classical
  set B := MPSChainTensor.blockTensor A with hBdef
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
  change (Matrix.polarIso M) _ (e x) = _
  rw [hVM, Matrix.mul_apply, ← e.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [M, MPSTensor.physicalMatrix, hBdef, e]

/-- The isometric factor of an injective blocked tensor `B = V P` is `V = B P⁻¹`, read as a
matrix product map: `⟨σ|V|x⟩ = ∑_{α,β} (A^{σ₁} ⋯ A^{σ_q})_{αβ} (P⁻¹)_{(α,β),x}`
(arXiv:2307.01696, eq. (13)). This is `polarIsoMatrix_chainBlockTensor_eq_sum` for the constant
chain. -/
theorem polarIsoMatrix_blockTensor_eq_sum (A : MPSTensor d D) {q : ℕ}
    (hB : Kraus.IsInjective (blockTensor A q)) (σ : Fin q → Fin d) (x : Fin (D * D)) :
    MPSTensor.polarIsoMatrix (blockTensor A q) ((decodeBlockEquiv d q).symm σ) x =
      ∑ a, Kraus.evalWord A (List.ofFn σ) (virtualPairEquiv D a).1 (virtualPairEquiv D a).2 *
        ((Matrix.polarPos (MPSTensor.physicalMatrix (blockTensor A q)))⁻¹.submatrix
          (virtualPairEquiv D) (virtualPairEquiv D)) a x := by
  have h := polarIsoMatrix_chainBlockTensor_eq_sum (fun _ : Fin q => A)
    (by rwa [MPSChainTensor.blockTensor_const]) σ x
  simpa only [MPSChainTensor.blockTensor_const, MPSChainTensor.eval_const] using h

/-- **Sequential factorization of the isometric factor of a blocked tensor injective on a set
of bond pairs.** Let `A₀, …, A_{q-1}` be tensors with bond dimension `D`, one on each site,
`q ≥ 1`, and let the blocked tensor `B` be injective on a set `S` of bond pairs, so that the
isometric factor `V` of `B = V P` is an isometry on the inputs `S` and vanishes on the others
(`MPSTensor.sum_star_polarIsoMatrix_mul`). Let `π` enumerate the bond pairs with the pairs of
`S` first. Then there are bond dimensions `b₀ = 1`, `b_q = |S|` and `b₁, …, b_q ≤ D²`, and site
matrices `Q_p`, vanishing outside the `b_p × b_{p+1}` block and isometric on it, such that
`⟨σ| V |π x⟩ = (Q₀(σ₀) ⋯ Q_{q-1}(σ_{q-1}))_{0x}` for every input `x < |S|`.

arXiv:2307.01696, eqs. (13)–(15), and the paragraph "Inhomogeneous short-range correlated MPS"
for tensors that depend on the site; here `V = B G` for a matrix `G` on the bond pairs
(`MPSTensor.exists_polarIsoMatrix_eq_sum`), which is `P⁻¹` for an injective tensor, and only the
inputs in `S` are kept, as in `exists_isometric_chain_of_eq_mul_of_le`. For `S` the set of all
pairs this is `exists_isometric_chain_polarIsoMatrix`. -/
theorem exists_isometric_chain_polarIsoMatrix_of_isInjectiveOn {q : ℕ}
    (A : MPSChainTensor d D q) (hq : 0 < q) {S : Finset (Fin D × Fin D)}
    (hB : MPSTensor.IsInjectiveOn (MPSChainTensor.blockTensor A) (S : Set (Fin D × Fin D)))
    (π : Fin (D * D) ≃ Fin D × Fin D) (hπ : ∀ x, x.val < S.card ↔ π x ∈ S) :
    ∃ (b : Fin (q + 1) → ℕ) (Q : MPSChainTensor d (D * D) q),
      b 0 = 1 ∧ b (Fin.last q) = S.card ∧ (∀ p : Fin q, b p.succ ≤ D * D) ∧
      (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) ∧
      (∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0) ∧
      (∀ p, IsIsometryOn (b p.succ) (Q p)) ∧
      ∀ (σ : Fin q → Fin d) (x : Fin (D * D)), x.val < S.card →
        MPSTensor.polarIsoMatrix (MPSChainTensor.blockTensor A)
            ((decodeBlockEquiv d q).symm σ) ((virtualPairEquiv D).symm (π x)) =
          eval Q σ ⟨0, x.pos⟩ x := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  obtain ⟨G, hG⟩ := MPSTensor.exists_polarIsoMatrix_eq_sum (MPSChainTensor.blockTensor A)
  let V : (Fin (n + 1) → Fin d) → Fin (D * D) → ℂ := fun σ x =>
    MPSTensor.polarIsoMatrix (MPSChainTensor.blockTensor A) ((decodeBlockEquiv d (n + 1)).symm σ)
      ((virtualPairEquiv D).symm (π x))
  have hcard : S.card ≤ D * D := by simpa using S.card_le_univ
  refine exists_isometric_chain_of_eq_mul_of_le A hcard
    (Matrix.of fun a x => G a ((virtualPairEquiv D).symm (π x))) V (fun σ x _ => ?_)
    (fun x y hx _ => ?_)
  · simp only [V, hG, MPSChainTensor.blockTensor_decodeBlockEquiv_symm, Matrix.of_apply]
  · have h := MPSTensor.sum_star_polarIsoMatrix_mul hB ((virtualPairEquiv D).symm (π x))
      ((virtualPairEquiv D).symm (π y))
    rw [← (decodeBlockEquiv d (n + 1)).symm.sum_comp] at h
    simp only [V]
    rw [h]
    have hS := (hπ x).mp hx
    by_cases hxy : x = y
    · subst hxy; simp [hS]
    · simp [hxy]

/-- **Sequential factorization of the isometry** of the polar decomposition of an
injective blocked tensor. Let `A₀, …, A_{q-1}` be tensors with bond dimension `D`, one on
each site, let `q ≥ 1`, and suppose the blocked tensor `B` of the chain is injective, so
that its polar decomposition `B = V P` has an isometry `V : ℂ^{D²} → (ℂ^d)^{⊗q}`. Then
there are bond dimensions `b₀ = 1`, `b_q = D²`, and `b₁, …, b_q ≤ D²`, and site matrices
`Q_p`, vanishing outside the `b_p × b_{p+1}` block, whose site maps
`ℂ^{b_{p+1}} → ℂ^{b_p} ⊗ ℂ^d` are isometries, such that
`⟨σ₁ ⋯ σ_q| V |x⟩ = (Q₀(σ₁) ⋯ Q_{q-1}(σ_q))_{0x}` for every configuration and every
input `x` of `ℂ^{D²}`. Equivalently, `V` is the ordered composition of the `q`
isometries, each acting on one site and the bond to its left. For a constant chain the
blocked tensor is `blockTensor A q` (`MPSChainTensor.blockTensor_const`).

arXiv:2307.01696, eqs. (13)–(15): `V = V_q ⋯ V_1` with isometries
`V_i : ℂ^{D'_i} → ℂ^{d D'_{i+1}}`, `D'_i ≤ D²`, `D'_{q+1} = 1`, where the last factor
`C-tilde = V_1`, carrying the input `ℂ^{D²}`, is an isometry by eq. (15). In the notation
here `Q_p = V_{q-p}` and `b_p = D'_{q+1-p}`. The paragraph "Inhomogeneous short-range
correlated MPS" applies the same decomposition to tensors that depend on the site. -/
theorem exists_isometric_chain_polarIsoMatrix {q : ℕ} (A : MPSChainTensor d D q) (hq : 0 < q)
    (hB : Kraus.IsInjective (MPSChainTensor.blockTensor A)) :
    ∃ (b : Fin (q + 1) → ℕ) (Q : MPSChainTensor d (D * D) q),
      b 0 = 1 ∧ b (Fin.last q) = D * D ∧ (∀ p : Fin q, b p.succ ≤ D * D) ∧
      (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) ∧
      (∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0) ∧
      (∀ p, IsIsometryOn (b p.succ) (Q p)) ∧
      ∀ (σ : Fin q → Fin d) (x : Fin (D * D)),
        MPSTensor.polarIsoMatrix (MPSChainTensor.blockTensor A)
            ((decodeBlockEquiv d q).symm σ) x =
          eval Q σ ⟨0, x.pos⟩ x := by
  classical
  have hc : (Finset.univ : Finset (Fin D × Fin D)).card = D * D := by simp
  obtain ⟨b, Q, h0, hl, hb, hrow, hcol, hiso, hV⟩ :=
    exists_isometric_chain_polarIsoMatrix_of_isInjectiveOn A hq (S := Finset.univ)
      (by simpa using MPSTensor.isInjectiveOn_univ_iff.mpr hB) (virtualPairEquiv D)
      (fun x => by simp [hc, x.isLt])
  exact ⟨b, Q, h0, hl.trans hc, hb, hrow, hcol, hiso, fun σ x => by
    simpa using hV σ x (by rw [hc]; exact x.isLt)⟩

/-- **Sequential factorization of the partial isometry of any blocked tensor.** Let
`A₀, …, A_{q-1}` be tensors with bond dimension `D`, one on each site, `q ≥ 1`, with no
injectivity assumed, and let `B = V P` be the polar decomposition of the blocked tensor, with
`V†V = Π`. Let `T` be a unitary on `ℂ^{D²}` whose first `r` columns span the range of `Π`:
`Π T = T diag(1, …, 1, 0, …, 0)` with `r` ones. Then `V T` vanishes on the inputs `x ≥ r`, and
there are bond dimensions `b₀ = 1`, `b_q = r` and `b₁, …, b_q ≤ D²`, and site matrices `Q_p`,
vanishing outside the `b_p × b_{p+1}` block and isometric on it, such that
`⟨σ| V T |x⟩ = (Q₀(σ₀) ⋯ Q_{q-1}(σ_{q-1}))_{0x}` for every input `x < r`.

arXiv:2307.01696, footnote to the paragraph "The sequential-RG circuit": the derivation of
eqs. (13)–(15) "remains valid also for non-injective tensors `B`. In that case `P⁻¹` is
understood as pseudo-inverse." Here `V = B G` for a matrix `G` on the bond pairs
(`MPSTensor.exists_polarIsoMatrix_eq_sum`), and the first `r` columns of `V T` are orthonormal
because `(V T)† (V T) = T† Π T` is the diagonal projector. -/
theorem exists_isometric_chain_polarIsoMatrix_mul_unitary {q : ℕ} (A : MPSChainTensor d D q)
    (hq : 0 < q) {r : ℕ} (hr : r ≤ D * D) {T : Matrix (Fin (D * D)) (Fin (D * D)) ℂ}
    (hT : T ∈ unitary (Matrix (Fin (D * D)) (Fin (D * D)) ℂ))
    (hET : MPSTensor.polarSupportMatrix (MPSChainTensor.blockTensor A) * T =
      T * Matrix.diagonal fun y => if y.val < r then 1 else 0) :
    ∃ (b : Fin (q + 1) → ℕ) (Q : MPSChainTensor d (D * D) q),
      b 0 = 1 ∧ b (Fin.last q) = r ∧ (∀ p : Fin q, b p.succ ≤ D * D) ∧
      (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) ∧
      (∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0) ∧
      (∀ p, IsIsometryOn (b p.succ) (Q p)) ∧
      (∀ (σ : Fin q → Fin d) (x : Fin (D * D)), x.val < r →
        (MPSTensor.polarIsoMatrix (MPSChainTensor.blockTensor A) * T)
            ((decodeBlockEquiv d q).symm σ) x = eval Q σ ⟨0, x.pos⟩ x) ∧
      ∀ (σ : Fin q → Fin d) (x : Fin (D * D)), r ≤ x.val →
        (MPSTensor.polarIsoMatrix (MPSChainTensor.blockTensor A) * T)
          ((decodeBlockEquiv d q).symm σ) x = 0 := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  set B := MPSChainTensor.blockTensor A with hBdef
  set V := MPSTensor.polarIsoMatrix B with hV
  set dec := decodeBlockEquiv d (n + 1)
  have hgram : (V * T)ᴴ * (V * T) = Matrix.diagonal fun y => if y.val < r then 1 else 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ,
      MPSTensor.conjTranspose_polarIsoMatrix_mul_polarIsoMatrix, hET, ← Matrix.mul_assoc,
      ← Matrix.star_eq_conjTranspose, Unitary.star_mul_self_of_mem hT, Matrix.one_mul]
  have hcol : ∀ x y, ∑ σ, star ((V * T) (dec.symm σ) x) * (V * T) (dec.symm σ) y =
      if x = y then (if x.val < r then 1 else 0) else 0 := fun x y => by
    have h := congrFun (congrFun hgram x) y
    rw [Matrix.mul_apply, ← dec.symm.sum_comp, Matrix.diagonal_apply] at h
    simpa only [Matrix.conjTranspose_apply] using h
  obtain ⟨G₀, hG₀⟩ := MPSTensor.exists_polarIsoMatrix_eq_sum B
  obtain ⟨b, Q, hb0, hbl, hb, hrow, hcolQ, hiso, hVQ⟩ :=
    exists_isometric_chain_of_eq_mul_of_le A hr (G₀ * T) (fun σ y => (V * T) (dec.symm σ) y)
      (fun σ y _ => by
        simp only [Matrix.mul_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hV, hG₀, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hBdef, MPSChainTensor.blockTensor_decodeBlockEquiv_symm, mul_assoc])
      (fun x y hx _ => by
        rw [hcol x y]
        split_ifs <;> simp_all)
  refine ⟨b, Q, hb0, hbl, hb, hrow, hcolQ, hiso, hVQ, fun σ x hx => ?_⟩
  have h := hcol x x
  simp only [↓reduceIte, show ¬ x.val < r by omega] at h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun σ _ => star_mul_self_nonneg
    ((V * T) (dec.symm σ) x)).mp h σ (Finset.mem_univ _)
  rcases mul_eq_zero.mp hz with h' | h'
  · exact star_eq_zero.mp h'
  · exact h'

end MPSPreparation
