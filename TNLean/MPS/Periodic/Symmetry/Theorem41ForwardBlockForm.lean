/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.CPSVBlocking
import TNLean.MPS.Periodic.OrbitUnitary
import TNLean.MPS.Periodic.RefinementNormalization
import TNLean.MPS.Periodic.Symmetry.PhysicalSymmetry
import TNLean.MPS.SharedInfra.BlockInclusionResolution

/-!
# Refinability implies divisibility for a block form with unit weights

Let `B = ⊕_k μ_k B_k` be a direct sum of left-canonical periodic blocks with
`|μ_k| = 1`. If the vectors of `B` can be `p`-refined, then the transfer
channel of `B` is the `p`-th power of a channel. This is the forward
implication of arXiv:1708.00029, Theorem 4.1, lines 735--810.

The proof follows the source. A refinement supplies a tensor `A` whose
`p`-blocked vectors are those of the physically rotated tensor
`⊕_k μ_k C_k`, where every `C_k` is again periodic. The periodic blocks of
`A` are normalized and split into step orbits under blocking
(`lem:blocking-arbitrary`, lines 432--456). The equal-case fundamental theorem
(`thm:bdequal`) matches the orbit blocks with the `C_k` up to roots of unity
(`eq:ZPA-is-cPA`). These phases are redistributed among the cyclic sectors
(`eq:Aprime-is-cPA`), and a final unitary conjugation gives a trace-preserving
tensor `R` with `R^{[p]} = ⊕_k μ_k C_k` exactly (lines 807--810). Hence
`𝔼_B = 𝔼_{⊕ μ C} = 𝔼_R^p`.

**Local fix (trace preservation):** the printed forward implication omits
the trace preservation of `𝔼_B` that the definition of `p`-divisibility at
lines 717--718 presupposes. Here the multiplicities have modulus one, which
makes `𝔼_B` trace preserving. Documented in
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`.

## Main declarations

* `MPSTensor.exists_unitary_stepOrbit_decomposition_toTensorFromBlocks`: the
  step-orbit decomposition of a blocked unit-weight block sum, with phase lifts.
* `MPSTensor.exists_isLeftCanonical_blockTensor_eq_toTensorFromBlocks`: a
  trace-preserving root with exactly prescribed blocking.
* `MPSTensor.isPDivisibleChannel_of_isPRefinable_toTensorFromBlocks`: the
  corrected forward implication of Theorem 4.1.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, *Irreducible forms of Matrix
  Product States: Theory and Applications*, arXiv:1708.00029,
  `lem:blocking-arbitrary`, lines 432--456; `thm:bdequal`, lines 643--693;
  Theorem 4.1, lines 715--810.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- A unit-weight direct sum of trace-preserving tensors is trace preserving.
Source: arXiv:1708.00029, irreducible form II, lines 313--332. -/
theorem isLeftCanonical_toTensorFromBlocks_one {d r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) (hA : ∀ k, IsLeftCanonical (A k)) :
    IsLeftCanonical (toTensorFromBlocks (fun _ ↦ 1) A) := by
  classical
  unfold IsLeftCanonical Kraus.IsTP
  have hres := sum_blockInclusion_mul_conjTranspose dim
  have hcol (k : Fin r) :
      (∑ i, (toTensorFromBlocks (fun _ ↦ 1) A i)ᴴ * toTensorFromBlocks (fun _ ↦ 1) A i) *
          blockInclusion dim k = blockInclusion dim k := by
    rw [Matrix.sum_mul]
    have h (i : Fin d) :
        (toTensorFromBlocks (fun _ ↦ 1) A i)ᴴ * toTensorFromBlocks (fun _ ↦ 1) A i *
            blockInclusion dim k =
          blockInclusion dim k * ((A k i)ᴴ * A k i) := by
      have hl := toTensorFromBlocks_mul_blockInclusion (fun _ ↦ (1 : ℂ)) A k i
      rw [one_smul] at hl
      have hc : (toTensorFromBlocks (fun _ ↦ 1) A i)ᴴ * blockInclusion dim k =
          blockInclusion dim k * (A k i)ᴴ := by
        have h := congrArg Matrix.conjTranspose
          (blockInclusion_conjTranspose_mul_toTensorFromBlocks (fun _ ↦ (1 : ℂ)) A k i)
        simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, one_smul]
          using h
      rw [Matrix.mul_assoc, hl, ← Matrix.mul_assoc, hc, Matrix.mul_assoc]
    simp only [h, ← Matrix.mul_sum]
    have hk := hA k
    unfold IsLeftCanonical Kraus.IsTP at hk
    rw [hk, Matrix.mul_one]
  calc
    ∑ i, (toTensorFromBlocks (fun _ ↦ 1) A i)ᴴ * toTensorFromBlocks (fun _ ↦ 1) A i =
        (∑ i, (toTensorFromBlocks (fun _ ↦ 1) A i)ᴴ * toTensorFromBlocks (fun _ ↦ 1) A i) *
          ∑ k, blockInclusion dim k * (blockInclusion dim k)ᴴ := by rw [hres, Matrix.mul_one]
    _ = ∑ k, (∑ i, (toTensorFromBlocks (fun _ ↦ 1) A i)ᴴ * toTensorFromBlocks (fun _ ↦ 1) A i) *
          blockInclusion dim k * (blockInclusion dim k)ᴴ := by
      rw [Matrix.mul_sum]
      simp only [Matrix.mul_assoc]
    _ = 1 := by simp only [hcol, hres]

/-- A matrix is determined by its products with the members of a resolution of
the identity. -/
private theorem eq_of_mul_eq_of_resolution {n r : ℕ} {dim : Fin r → ℕ}
    (W : (s : Fin r) → Matrix (Fin n) (Fin (dim s)) ℂ) (hW : ∑ s, W s * (W s)ᴴ = 1)
    {M N : Matrix (Fin n) (Fin n) ℂ} (h : ∀ s, M * W s = N * W s) : M = N := by
  calc
    M = M * ∑ s, W s * (W s)ᴴ := by rw [hW, Matrix.mul_one]
    _ = N * ∑ s, W s * (W s)ᴴ := by simp only [Matrix.mul_sum, ← Matrix.mul_assoc, h]
    _ = N := by rw [hW, Matrix.mul_one]

/-- **Step orbits of a blocked block sum.** Blocking a unit-weight direct sum of
periodic tensors `A_k` of periods `m_k` splits each `A_k` into `gcd(m_k, p)`
periodic blocks of period `m_k / gcd(m_k, p)`. One unitary `Y` identifies the
blocked tensor with the unit-weight direct sum of all these blocks. Every
choice of roots of unity `c_s` of these periods lifts to a trace-preserving
tensor whose blocking is the `c`-weighted direct sum in the same coordinates.

Source: arXiv:1708.00029, `lem:blocking-arbitrary`, lines 432--456, and
`eq:ZPA-is-cPA` through `eq:Aprime-is-cPA`, lines 778--807, applied to every
block of the irreducible form as in the proof of Theorem 4.1, lines 750--765. -/
theorem exists_unitary_stepOrbit_decomposition_toTensorFromBlocks
    {d r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) (period : Fin r → ℕ)
    (hPer : ∀ k, IsPeriodic (period k) (A k)) {p : ℕ} (hp : 0 < p) :
    ∃ (fdim : Fin (∑ k, (period k).gcd p) → ℕ)
      (C : (s : Fin (∑ k, (period k).gcd p)) → MPSTensor (blockPhysDim d p) (fdim s))
      (Y : Matrix (Fin (∑ k, dim k)) (Fin (∑ s, fdim s)) ℂ),
      (∀ s, IsPeriodic
        (period ((finSigmaFinEquiv (n := fun k ↦ (period k).gcd p)).symm s).1 /
          (period ((finSigmaFinEquiv (n := fun k ↦ (period k).gcd p)).symm s).1).gcd p)
        (C s)) ∧
      Y * Yᴴ = 1 ∧ Yᴴ * Y = 1 ∧
      (∀ i, blockTensor (toTensorFromBlocks (fun _ ↦ 1) A) p i =
        Y * toTensorFromBlocks (fun _ ↦ 1) C i * Yᴴ) ∧
      ∀ c : Fin (∑ k, (period k).gcd p) → ℂ,
        (∀ s, c s ^
          (period ((finSigmaFinEquiv (n := fun k ↦ (period k).gcd p)).symm s).1 /
            (period ((finSigmaFinEquiv (n := fun k ↦ (period k).gcd p)).symm s).1).gcd p) =
            1) →
        ∃ A' : MPSTensor d (∑ k, dim k), IsLeftCanonical A' ∧
          ∀ i, blockTensor A' p i = Y * toTensorFromBlocks c C i * Yᴴ := by
  classical
  let n : Fin r → ℕ := fun k ↦ (period k).gcd p
  let e := (finSigmaFinEquiv (n := n)).symm
  have hEach (k : Fin r) := IsPeriodic.exists_unitary_stepOrbit_decomposition (A k) (hPer k) hp
  choose P sd B V U hproj hsum _ hdim hperB hrange hUU hU hinc hconj hlift using hEach
  let fdim : Fin (∑ k, n k) → ℕ := fun s ↦ sd (e s).1 (e s).2
  let C : (s : Fin (∑ k, n k)) → MPSTensor (blockPhysDim d p) (fdim s) :=
    fun s ↦ B (e s).1 (e s).2
  let W : (s : Fin (∑ k, n k)) → Matrix (Fin (∑ k, dim k)) (Fin (fdim s)) ℂ :=
    fun s ↦ blockInclusion dim (e s).1 * V (e s).1 (e s).2
  -- each blocked summand intertwines its orbit isometries, also after a phase lift
  have hblockV (k : Fin r) (a : Fin (n k)) (c : Fin (n k) → ℂ)
      (X : MPSTensor (blockPhysDim d p) (dim k))
      (hX : ∀ i, X i = U k * toTensorFromBlocks c (B k) i * (U k)ᴴ) (i) :
      X i * V k a = V k a * (c a • B k a i) := by
    rw [hX, ← hinc k a]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U k)ᴴ, hU k, Matrix.one_mul, toTensorFromBlocks_mul_blockInclusion]
  have hsumV (k : Fin r) : ∑ a, V k a * (V k a)ᴴ = 1 := by
    simp only [hrange, sum_stepOrbitProjection, hsum]
  have hflat (f : ((k : Fin r) × Fin (n k)) → Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ) :
      ∑ s, f (e s) = ∑ k, ∑ a, f ⟨k, a⟩ := by
    rw [Equiv.sum_comp e f, Fintype.sum_sigma]
  have hres : ∑ s, W s * (W s)ᴴ = 1 := by
    refine (hflat fun x ↦
      blockInclusion dim x.1 * V x.1 x.2 * (blockInclusion dim x.1 * V x.1 x.2)ᴴ).trans ?_
    have hk (k : Fin r) :
        ∑ a, blockInclusion dim k * V k a * (blockInclusion dim k * V k a)ᴴ =
          blockInclusion dim k * (blockInclusion dim k)ᴴ := by
      calc
        _ = blockInclusion dim k * (∑ a, V k a * (V k a)ᴴ) * (blockInclusion dim k)ᴴ := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hsumV, Matrix.mul_one]
    exact (Finset.sum_congr rfl fun k _ ↦ hk k).trans (sum_blockInclusion_mul_conjTranspose dim)
  have hdim' : ∑ s, fdim s = ∑ k, dim k := by
    rw [Equiv.sum_comp e (fun x ↦ sd x.1 x.2), Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun k _ ↦ hdim k
  -- the blocked sum intertwines the flattened isometries
  have hblock (X : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k))
      (c : Fin (∑ k, n k) → ℂ)
      (hX : ∀ k a i, X k i * V k a = V k a * (c (finSigmaFinEquiv ⟨k, a⟩) • B k a i))
      (s : Fin (∑ k, n k)) (i : Fin (blockPhysDim d p)) :
      toTensorFromBlocks (fun _ ↦ 1) X i * W s = W s * (c s • C s i) := by
    dsimp only [W, C]
    rw [← Matrix.mul_assoc, toTensorFromBlocks_mul_blockInclusion, one_smul, Matrix.mul_assoc,
      hX, ← Matrix.mul_assoc]
    simp only [e, Sigma.eta, Equiv.apply_symm_apply]
  have hT (i : Fin (blockPhysDim d p)) :
      blockTensor (toTensorFromBlocks (fun _ ↦ 1) A) p i =
        toTensorFromBlocks (fun _ ↦ 1) (fun k ↦ blockTensor (A k) p) i := by
    rw [blockTensor_toTensorFromBlocks_apply]
    simp only [one_pow]
  have hinter (s : Fin (∑ k, n k)) (i : Fin (blockPhysDim d p)) :
      blockTensor (toTensorFromBlocks (fun _ ↦ 1) A) p i * W s = W s * C s i := by
    rw [hT]
    simpa only [one_smul] using hblock (fun k ↦ blockTensor (A k) p) (fun _ ↦ 1)
      (fun k a i ↦ hblockV k a (fun _ ↦ 1) _ (hconj k) i) s i
  obtain ⟨Y, hYY, hY'Y, hYinc, hYconj⟩ :=
    exists_unitary_toTensorFromBlocks_of_resolution
      (blockTensor (toTensorFromBlocks (fun _ ↦ 1) A) p) C W hres hdim' hinter
  refine ⟨fdim, C, Y, fun s ↦ hperB (e s).1 (e s).2, hYY, hY'Y, hYconj, ?_⟩
  intro c hc
  have hroot (k : Fin r) (a : Fin (n k)) :
      c (finSigmaFinEquiv ⟨k, a⟩) ^ (period k / (period k).gcd p) = 1 := by
    simpa only [e, Equiv.symm_apply_apply] using hc (finSigmaFinEquiv ⟨k, a⟩)
  choose A' hA' hA'block using fun k ↦
    hlift k (fun a ↦ c (finSigmaFinEquiv ⟨k, a⟩)) (hroot k)
  refine ⟨toTensorFromBlocks (fun _ ↦ 1) A', isLeftCanonical_toTensorFromBlocks_one A' hA',
    fun i ↦ ?_⟩
  refine eq_of_mul_eq_of_resolution W hres fun s ↦ ?_
  have hYW : Y * toTensorFromBlocks c C i * Yᴴ * W s = W s * (c s • C s i) := by
    rw [← hYinc]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Yᴴ Y, hY'Y, Matrix.one_mul, toTensorFromBlocks_mul_blockInclusion]
  rw [hYW, blockTensor_toTensorFromBlocks_apply]
  simp only [one_pow]
  exact hblock (fun k ↦ blockTensor (A' k) p) c
    (fun k a i ↦ hblockV k a _ _ (hA'block k) i) s i

/-- **Trace-preserving root with prescribed blocking.** Let `ν_k` have modulus
one and let `B_k` be left-canonical periodic tensors on the blocked physical
alphabet. If the `p`-blocking of some tensor `A` generates the same vectors as
`⊕_k ν_k B_k` at every positive length, then a trace-preserving tensor `R` on
the original alphabet satisfies `R^{[p]} = ⊕_k ν_k B_k` letter by letter.

No normalization of `A` is assumed. Source: arXiv:1708.00029, Theorem 4.1,
lines 750--810: the periodic blocks of `A` are normalized (lines 750--756),
matched with the target by `thm:bdequal` (`eq:ZPA-is-cPA`), and the phases are
absorbed into a trace-preserving tensor (`eq:Aprime-is-cPA`, lines 778--810). -/
theorem exists_isLeftCanonical_blockTensor_eq_toTensorFromBlocks
    {d D s p : ℕ} {dim' : Fin s → ℕ} (A : MPSTensor d D) (hp : 0 < p)
    (B : (k : Fin s) → MPSTensor (blockPhysDim d p) (dim' k))
    (ν : Fin s → ℂ) (hν : ∀ k, ‖ν k‖ = 1)
    (period : Fin s → ℕ) (hPer : ∀ k, IsPeriodic (period k) (B k))
    (hSame : SameMPV₂Pos (blockTensor A p) (toTensorFromBlocks ν B)) :
    ∃ R : MPSTensor d (∑ k, dim' k),
      IsLeftCanonical R ∧ blockTensor R p = toTensorFromBlocks ν B := by
  classical
  have hν0 (k : Fin s) : ν k ≠ 0 := Complex.ne_zero_of_norm_eq_one (hν k)
  -- group the target into a basis of periodic tensors with unit-modulus weights
  let classes := mpvPhaseClassData B
  obtain ⟨ξ, hξ, hdimQ, hPerQ, hNonRepQ, hnormQ, hSameQ, _⟩ :=
    classes.exists_unitary_sectorDecomposition ν hν0 period hPer
  -- normalize the periodic blocks of `A`
  obtain ⟨r, dim, A₁, period₁, hPer₁, _, _, hSameA⟩ :=
    exists_unitWeight_periodic_presentation_of_blocked_sameMPV₂Pos A hp
      (classes.toSectorDecomposition ν ξ hν0 hξ) (fun j ↦ period (classes.repr j))
      hPerQ hNonRepQ (hSame.trans hSameQ) fun j q ↦ (hnormQ j q).trans (hν _)
  -- split the blocked normalized blocks into step orbits
  obtain ⟨fdim, C, Y, hPerC, hYY, hY'Y, hYconj, hlift⟩ :=
    exists_unitary_stepOrbit_decomposition_toTensorFromBlocks A₁ period₁ hPer₁ hp
  have hSameC : SameMPV₂Pos (toTensorFromBlocks (fun _ ↦ 1) C) (toTensorFromBlocks ν B) := by
    have hCY : SameMPV₂Pos (blockTensor (toTensorFromBlocks (fun _ ↦ 1) A₁) p)
        (toTensorFromBlocks (fun _ ↦ 1) C) := by
      apply sameMPV₂Pos_of_coisometry_reconstruction _ _ Yᴴ
        (by simpa only [Matrix.conjTranspose_conjTranspose] using hY'Y)
      intro i
      simpa only [Matrix.conjTranspose_conjTranspose] using hYconj i
    exact hCY.symm.trans ((sameMPV₂Pos_blockTensor A _ hSameA p hp).symm.trans hSame)
  -- match the orbit blocks with the target up to roots of unity
  obtain ⟨c, W, hc, hWW, hW'W, hMatch⟩ :=
    exists_unitary_matching_of_periodic_block_families C (fun _ ↦ 1) (fun _ ↦ one_ne_zero)
      B ν hν0 _ period hPerC hPer hSameC
  simp only [mul_one] at hMatch
  obtain ⟨A', hA', hA'block⟩ := hlift c hc
  -- conjugate back to the bond space of the target
  let T := Y * W
  have hTT : T * Tᴴ = 1 := by
    simp only [T, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W, hWW, Matrix.one_mul, hYY]
  have hT'T : Tᴴ * T = 1 := by
    simp only [T, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Yᴴ, hY'Y, Matrix.one_mul, hW'W]
  let R : MPSTensor d (∑ k, dim' k) := fun i ↦ Tᴴ * A' i * T
  refine ⟨R, ?_, ?_⟩
  · have hA'TP := hA'
    unfold IsLeftCanonical Kraus.IsTP at hA'TP ⊢
    calc
      ∑ i, (R i)ᴴ * R i = Tᴴ * (∑ i, (A' i)ᴴ * A' i) * T := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [R, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
        rw [← Matrix.mul_assoc T Tᴴ, hTT, Matrix.one_mul]
      _ = 1 := by rw [hA'TP, Matrix.mul_one, hT'T]
  · funext I
    have hw : Kraus.wordOfBlock d p I ≠ [] := by
      intro h
      have := congrArg List.length h
      simp only [Kraus.length_wordOfBlock, List.length_nil] at this
      exact hp.ne' this
    have h := evalWord_eq_coisometry_reconstruction_of_ne_nil T hTT
      (A := R) (B := A') (fun _ ↦ rfl) (Kraus.wordOfBlock d p I) hw
    change blockTensor R p I = Tᴴ * blockTensor A' p I * T at h
    rw [h, hA'block, hMatch]
    simp only [T, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Yᴴ Y, hY'Y, Matrix.one_mul, ← Matrix.mul_assoc Wᴴ W, hW'W,
      Matrix.one_mul, ← Matrix.mul_assoc Yᴴ Y, hY'Y, Matrix.one_mul, hW'W, Matrix.mul_one]

/-- A `p`-refinable direct sum of left-canonical periodic blocks with
unit-modulus weights has a trace-preserving `p`-th root of its transfer map.
Source: arXiv:1708.00029, Theorem 4.1, lines 735--810. -/
theorem exists_isLeftCanonical_transferMap_eq_pow_of_isPRefinable
    {d r p : ℕ} {dim : Fin r → ℕ}
    (B : (k : Fin r) → MPSTensor d (dim k)) (μ : Fin r → ℂ) (hμ : ∀ k, ‖μ k‖ = 1)
    (period : Fin r → ℕ) (hPer : ∀ k, IsPeriodic (period k) (B k))
    (hp : 0 < p) (hRefine : IsPRefinable (toTensorFromBlocks μ B) p) :
    ∃ R : MPSTensor d (∑ k, dim k), IsLeftCanonical R ∧
      Kraus.transferMap (toTensorFromBlocks μ B) = Kraus.transferMap R ^ p := by
  classical
  obtain ⟨A, W, hW, hTransfer, hSame⟩ :=
    pRefinementCanonicalization_pullback (toTensorFromBlocks μ B) p hRefine
  let C : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k) :=
    fun k τ ↦ ∑ σ, W τ σ • B k σ
  have hLetters : (fun τ ↦ ∑ σ, W τ σ • toTensorFromBlocks μ B σ) = toTensorFromBlocks μ C :=
    funext (toTensorFromBlocks_sum_smul μ B W)
  have hTarget : SameMPV₂Pos (blockTensor A p) (toTensorFromBlocks μ C) := by
    rw [← hLetters]
    exact fun N _ σ ↦ (hSame N σ).symm
  obtain ⟨R, hR, hRoot⟩ := exists_isLeftCanonical_blockTensor_eq_toTensorFromBlocks A hp C μ hμ
    period (fun k ↦ isPeriodic_kraus_isometry (B k) W hW (hPer k)) hTarget
  refine ⟨R, hR, ?_⟩
  rw [← transferMap_blockTensor, hRoot, ← hLetters, hTransfer]

/-- **Corrected forward implication of Theorem 4.1.** A `p`-refinable direct
sum of left-canonical periodic blocks with unit-modulus weights has a
`p`-divisible transfer channel. Source: arXiv:1708.00029, Theorem 4.1,
lines 735--810, with the trace-preservation correction recorded in the module
docstring. -/
theorem isPDivisibleChannel_of_isPRefinable_toTensorFromBlocks
    {d r p : ℕ} {dim : Fin r → ℕ}
    (B : (k : Fin r) → MPSTensor d (dim k)) (μ : Fin r → ℂ) (hμ : ∀ k, ‖μ k‖ = 1)
    (period : Fin r → ℕ) (hPer : ∀ k, IsPeriodic (period k) (B k))
    (hp : 0 < p) (hRefine : IsPRefinable (toTensorFromBlocks μ B) p) :
    IsPDivisibleChannel (Kraus.transferMap (toTensorFromBlocks μ B)) p := by
  obtain ⟨R, hR, hRoot⟩ :=
    exists_isLeftCanonical_transferMap_eq_pow_of_isPRefinable B μ hμ period hPer hp hRefine
  exact ⟨Kraus.transferMap R, Kraus.isChannel_mapLM R hR, hRoot⟩

end MPSTensor
