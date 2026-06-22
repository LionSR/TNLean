import TNLean.PEPS.CycleMPSOverlapInsertion
import TNLean.PEPS.CycleMPSFundamentalTheorem

/-!
# The closed-chain corollaries at `n ≥ 2L + 1` via overlapping windows

This file delivers the strengthened closed-chain corollaries of the
Fundamental Theorem for normal PEPS announced in arXiv:1804.04964 at line
1623 and proved in its Section `normal_alt` (the corollary after Lemma 5,
lines 2256--2295 of `Papers/1804.04964/paper_normal.tex`): two normal
translation-invariant MPS on `n ≥ 2L + 1` sites — two matrix tensors, each
`L`-block injective — generating the same closed-chain state are related by

* a single gauge `Z` and a constant `λ` with `λ^n = 1` and
  `B^i = λ · Z⁻¹ A^i Z`
  (`fundamentalTheorem_normalMPS_translationInvariant_of_overlap`), and
* equivalently a per-bond gauge family `Z_v` with `B^i = Z_v⁻¹ A^i Z_{v+1}`
  (`fundamentalTheorem_normalMPS_of_overlap`), the form delivered at
  `n ≥ 3L` by `fundamentalTheorem_normalMPS` through the three-arc cover.

The uniqueness clause of the source corollary — the gauge `Z` is unique up
to a multiplicative constant — needs no system size and is already delivered
by `fundamentalTheorem_normalMPS_translationInvariant_gauge_unique`.

The route consumes the insertion correspondence built from Lemma 5
(`MPSTensor.exists_conjugation_of_mpv_eq`): the two networks have conjugate
word products at length `n`, `B^w = Z ⬝ A^w ⬝ Z⁻¹`.  The remaining step is a
rigidity lemma (`MPSTensor.proportional_of_evalWord_eq`): two `L`-block
injective tensors with *equal* word products at one length `n ≥ 2L + 1` are
proportional letterwise, `C^i = λ A^i` with `λ^n = 1`.  Its proof transports
words of intermediate lengths between the two networks, shows the transport
of the identity is a nonzero scalar — it commutes with every letter of `C`
by comparing the two one-letter extensions — and peels one letter off the
full-length equality through the spanning windows.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section `normal_alt`, the corollary after Lemma 5, lines 2256--2295 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ### Rigidity: equal word products at one length force proportional letters -/

/-- **The transport of the identity is a nonzero scalar.**  For two tensors
with matched word transports at lengths `k` and `k + 1`, the transported
identity commutes with every letter of `C` — its two one-letter extensions
agree — hence with the full matrix algebra by block injectivity, so it is a
scalar; surjectivity of the transport makes the scalar nonzero.

This is the mechanism by which the source's Lemma 5 route pins the inserted
identity (arXiv:1804.04964, lines 2045--2255 of
`Papers/1804.04964/paper_normal.tex`, applied to the gauge-absorbed pair). -/
private theorem transport_one_eq_smul_one {A C : MPSTensor d D} {L k : ℕ}
    (hD : 0 < D)
    (hAk : IsNBlkInjective A k) (hCk : IsNBlkInjective C k)
    (hCL : IsNBlkInjective C L)
    {Λk Λk1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hΛk : ∀ τ : Fin k → Fin d,
      Λk (evalWord A (List.ofFn τ)) = evalWord C (List.ofFn τ))
    (hΛk1 : ∀ τ : Fin (k + 1) → Fin d,
      Λk1 (evalWord A (List.ofFn τ)) = evalWord C (List.ofFn τ)) :
    ∃ c : ℂ, c ≠ 0 ∧ Λk 1 = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  -- The two one-letter extension relations.
  have hR1 : ∀ (i : Fin d) (M : Matrix (Fin D) (Fin D) ℂ),
      Λk1 (A i * M) = C i * Λk M := by
    intro i
    have hext := LinearMap.ext_on_range
      (v := fun τ : Fin k → Fin d => evalWord A (List.ofFn τ)) (hv := hAk)
      (f := Λk1 ∘ₗ LinearMap.mulLeft ℂ (A i))
      (g := (LinearMap.mulLeft ℂ (C i)) ∘ₗ Λk)
      (fun τ => by
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
        rw [← evalWord_ofFn_cons, hΛk1 (Fin.cons i τ), evalWord_ofFn_cons, hΛk τ])
    intro M
    have := congrArg (· M) hext
    simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply] using this
  have hR2 : ∀ (i : Fin d) (M : Matrix (Fin D) (Fin D) ℂ),
      Λk1 (M * A i) = Λk M * C i := by
    intro i
    have hext := LinearMap.ext_on_range
      (v := fun τ : Fin k → Fin d => evalWord A (List.ofFn τ)) (hv := hAk)
      (f := Λk1 ∘ₗ LinearMap.mulRight ℂ (A i))
      (g := (LinearMap.mulRight ℂ (C i)) ∘ₗ Λk)
      (fun τ => by
        simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
        rw [← evalWord_ofFn_snoc, hΛk1 (Fin.snoc τ i), evalWord_ofFn_snoc, hΛk τ])
    intro M
    have := congrArg (· M) hext
    simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply] using this
  -- The transported identity commutes with every letter of `C`.
  have hcomm_letter : ∀ i : Fin d, Commute (C i) (Λk 1) := by
    intro i
    have h1 : C i * Λk 1 = Λk1 (A i) := by
      rw [← hR1 i 1, Matrix.mul_one]
    have h2 : Λk 1 * C i = Λk1 (A i) := by
      rw [← hR2 i 1, Matrix.one_mul]
    exact h1.trans h2.symm
  -- Hence with every word product, hence with the full matrix algebra.
  have hcomm_word : ∀ w : List (Fin d), Commute (evalWord C w) (Λk 1) := by
    intro w
    induction w with
    | nil => exact Commute.one_left (Λk 1)
    | cons i w ih => exact (hcomm_letter i).mul_left ih
  have hcomm_maps :
      LinearMap.mulRight ℂ (Λk 1) = LinearMap.mulLeft ℂ (Λk 1) := by
    apply LinearMap.ext_on_range
      (v := fun τ : Fin L → Fin d => evalWord C (List.ofFn τ)) (hv := hCL)
    intro τ
    simpa only [LinearMap.mulRight_apply, LinearMap.mulLeft_apply] using
      (hcomm_word (List.ofFn τ)).eq
  have hcomm : ∀ M : Matrix (Fin D) (Fin D) ℂ, Commute M (Λk 1) := by
    intro M
    exact (commute_iff_eq M (Λk 1)).mpr (by
      simpa only [LinearMap.mulRight_apply, LinearMap.mulLeft_apply] using
        congrArg (fun f => f M) hcomm_maps)
  -- A matrix commuting with everything is a scalar.
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr
    (fun i j => hcomm (Matrix.single i j 1))
  have hV : Λk 1 = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  -- The transport is surjective, hence injective, so the scalar is nonzero.
  have hsurj : Function.Surjective Λk := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    calc (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ))
        = Submodule.span ℂ (Set.range fun τ : Fin k → Fin d =>
            evalWord C (List.ofFn τ)) := hCk.symm
      _ ≤ LinearMap.range Λk := by
          rw [Submodule.span_le]
          rintro _ ⟨τ, rfl⟩
          exact ⟨evalWord A (List.ofFn τ), hΛk τ⟩
  have hinj : Function.Injective Λk := LinearMap.injective_iff_surjective.mpr hsurj
  refine ⟨c, fun hc0 => ?_, hV⟩
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  apply (show (1 : Matrix (Fin D) (Fin D) ℂ) ≠ 0 from one_ne_zero)
  apply hinj
  rw [hV, hc0, zero_smul, map_zero]

/-- Some length-`n` word product of a block-injective tensor is nonzero. -/
private theorem exists_evalWord_ne_zero {A : MPSTensor d D} {L n : ℕ}
    (hL : 0 < L) (hD : 0 < D) (hA : IsNBlkInjective A L) (hn : L ≤ n) :
    ∃ σ : Fin n → Fin d, evalWord A (List.ofFn σ) ≠ 0 := by
  by_contra hall
  push Not at hall
  have hspan : Submodule.span ℂ (Set.range fun σ : Fin n → Fin d =>
      evalWord A (List.ofFn σ)) = ⊤ := isNBlkInjective_of_le hL hA hn
  have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ Submodule.span ℂ
      (Set.range fun σ : Fin n → Fin d => evalWord A (List.ofFn σ)) :=
    hspan ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp h1
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  apply (show (1 : Matrix (Fin D) (Fin D) ℂ) ≠ 0 from one_ne_zero)
  rw [← hc]
  exact Finset.sum_eq_zero fun σ _ => by rw [hall σ, smul_zero]

/-- **Rigidity of word products at one length** (arXiv:1804.04964, the
endgame of the corollary after Lemma 5, lines 2256--2295 of
`Papers/1804.04964/paper_normal.tex`, after the gauge is absorbed).

Two `L`-block injective tensors with *equal* word products at one length
`n ≥ 2L + 1` are proportional letterwise: `C^i = λ A^i` with `λ^n = 1`.
The transports of the identity at window length `L` and at the complementary
length `n - 1 - L` are nonzero scalars; peeling one letter off the
full-length equality through the two spanning windows leaves
`C^i = (c_L c_{n-1-L})⁻¹ A^i`. -/
theorem proportional_of_evalWord_eq {A C : MPSTensor d D} {n L : ℕ}
    (hL : 0 < L) (hn : 2 * L + 1 ≤ n) (hD : 0 < D)
    (hA : IsNBlkInjective A L) (hC : IsNBlkInjective C L)
    (hw : ∀ w : List (Fin d), w.length = n → evalWord C w = evalWord A w) :
    ∃ lam : ℂ, lam ^ n = 1 ∧ ∀ i : Fin d, C i = lam • A i := by
  classical
  -- The window transports at length `L` and at the complementary length.
  set k₁ : ℕ := n - 1 - L with hk₁def
  have hk₁L : L ≤ k₁ := by omega
  obtain ⟨ΛL, hΛL⟩ := exists_evalWordTransport (k := L) (q := n - L) (by omega)
    hA (isNBlkInjective_of_le hL hA (by omega)) hw
  obtain ⟨ΛL1, hΛL1⟩ := exists_evalWordTransport (k := L + 1) (q := n - (L + 1))
    (by omega) (isNBlkInjective_of_le hL hA (by omega))
    (isNBlkInjective_of_le hL hA (by omega)) hw
  obtain ⟨Λk, hΛk⟩ := exists_evalWordTransport (k := k₁) (q := n - k₁) (by omega)
    (isNBlkInjective_of_le hL hA hk₁L) (isNBlkInjective_of_le hL hA (by omega)) hw
  obtain ⟨Λk1, hΛk1⟩ := exists_evalWordTransport (k := k₁ + 1) (q := n - (k₁ + 1))
    (by omega) (isNBlkInjective_of_le hL hA (by omega))
    (isNBlkInjective_of_le hL hA (by omega)) hw
  -- The transported identities are nonzero scalars.
  obtain ⟨cL, hcL0, hcL⟩ := transport_one_eq_smul_one hD hA
    (isNBlkInjective_of_le hL hC le_rfl) hC hΛL hΛL1
  obtain ⟨ck, hck0, hck⟩ := transport_one_eq_smul_one hD
    (isNBlkInjective_of_le hL hA hk₁L) (isNBlkInjective_of_le hL hC hk₁L) hC
    hΛk hΛk1
  -- Peel one letter off the full-length equality.
  have hc0 : ∀ (i : Fin d) (v : Fin k₁ → Fin d) (w : Fin L → Fin d),
      C i * evalWord C (List.ofFn v) * evalWord C (List.ofFn w) =
        A i * evalWord A (List.ofFn v) * evalWord A (List.ofFn w) := by
    intro i v w
    have hword := hw (i :: (List.ofFn v ++ List.ofFn w)) (by simp; omega)
    rw [evalWord_cons, evalWord_cons, evalWord_append, evalWord_append] at hword
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    exact hword
  -- Linearize the trailing window through `Λ_L`.
  have hΛL_inv : ΛL (cL⁻¹ • (1 : Matrix (Fin D) (Fin D) ℂ)) = 1 := by
    rw [map_smul, hcL, smul_smul, inv_mul_cancel₀ hcL0, one_smul]
  have hc2 : ∀ (i : Fin d) (v : Fin k₁ → Fin d),
      C i * evalWord C (List.ofFn v) = cL⁻¹ • (A i * evalWord A (List.ofFn v)) := by
    intro i v
    have hext := LinearMap.ext_on_range
      (v := fun w : Fin L → Fin d => evalWord A (List.ofFn w)) (hv := hA)
      (f := (LinearMap.mulLeft ℂ (C i * evalWord C (List.ofFn v))) ∘ₗ ΛL)
      (g := LinearMap.mulLeft ℂ (A i * evalWord A (List.ofFn v)))
      (fun w => by
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
        rw [hΛL w]
        exact hc0 i v w)
    have happ := congrArg (· (cL⁻¹ • (1 : Matrix (Fin D) (Fin D) ℂ))) hext
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, hΛL_inv] at happ
    rw [Matrix.mul_one] at happ
    rw [happ, Matrix.mul_smul, Matrix.mul_one]
  -- Linearize the remaining window through `Λ_{k₁}`.
  have hΛk_inv : Λk (ck⁻¹ • (1 : Matrix (Fin D) (Fin D) ℂ)) = 1 := by
    rw [map_smul, hck, smul_smul, inv_mul_cancel₀ hck0, one_smul]
  have hc4 : ∀ i : Fin d, C i = (cL⁻¹ * ck⁻¹) • A i := by
    intro i
    have hext := LinearMap.ext_on_range
      (v := fun v : Fin k₁ → Fin d => evalWord A (List.ofFn v))
      (hv := isNBlkInjective_of_le hL hA hk₁L)
      (f := (LinearMap.mulLeft ℂ (C i)) ∘ₗ Λk)
      (g := cL⁻¹ • LinearMap.mulLeft ℂ (A i))
      (fun v => by
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
          LinearMap.smul_apply]
        rw [hΛk v]
        exact hc2 i v)
    have happ := congrArg (· (ck⁻¹ • (1 : Matrix (Fin D) (Fin D) ℂ))) hext
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.smul_apply, hΛk_inv] at happ
    rw [Matrix.mul_one] at happ
    rw [happ, Matrix.mul_smul, smul_smul, Matrix.mul_one]
  -- The scalar is an `n`-th root of unity.
  set lam : ℂ := cL⁻¹ * ck⁻¹ with hlam
  have hCfam : C = fun i => lam • A i := funext fun i => hc4 i
  obtain ⟨σ, hσ⟩ := exists_evalWord_ne_zero hL hD hA (by omega : L ≤ n)
  have hlamn : lam ^ n = 1 := by
    have hCw : evalWord C (List.ofFn σ) = lam ^ n • evalWord A (List.ofFn σ) := by
      rw [hCfam]
      have := evalWord_smul lam A (List.ofFn σ)
      simpa using this
    have heq := hw (List.ofFn σ) (by simp)
    rw [hCw] at heq
    have hzero : (lam ^ n - 1) • evalWord A (List.ofFn σ) = 0 := by
      rw [sub_smul, one_smul, heq, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hσ
  exact ⟨lam, hlamn, hc4⟩

/-- Block injectivity is preserved by conjugation. -/
private theorem isNBlkInjective_conj {B : MPSTensor d D} {L : ℕ}
    (hB : IsNBlkInjective B L) (Q : GL (Fin D) ℂ) :
    IsNBlkInjective (fun i => (Q : Matrix (Fin D) (Fin D) ℂ) * B i *
      ((Q⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) L := by
  set C : MPSTensor d D := fun i => (Q : Matrix (Fin D) (Fin D) ℂ) * B i *
    ((Q⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) with hCdef
  have hCw : ∀ w : List (Fin d), evalWord C w =
      (Q : Matrix (Fin D) (Fin D) ℂ) * evalWord B w *
        ((Q⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
    evalWord_gauge Q (fun i => rfl)
  have hmem : ∀ N ∈ Submodule.span ℂ (Set.range fun τ : Fin L → Fin d =>
      evalWord B (List.ofFn τ)),
      (Q : Matrix (Fin D) (Fin D) ℂ) * N *
          ((Q⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) ∈
        Submodule.span ℂ (Set.range fun τ : Fin L → Fin d =>
          evalWord C (List.ofFn τ)) := by
    intro N hN
    induction hN using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨τ, rfl⟩ := hx
        exact Submodule.subset_span ⟨τ, hCw (List.ofFn τ)⟩
    | zero =>
        rw [Matrix.mul_zero, Matrix.zero_mul]
        exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
        rw [Matrix.mul_add, Matrix.add_mul]
        exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
        rw [Matrix.mul_smul, Matrix.smul_mul]
        exact Submodule.smul_mem _ a hx
  rw [IsNBlkInjective, eq_top_iff]
  intro M _
  have hQQ : (Q : Matrix (Fin D) (Fin D) ℂ) *
      ((Q⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMrep : M = (Q : Matrix (Fin D) (Fin D) ℂ) *
      (((Q⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * M *
        (Q : Matrix (Fin D) (Fin D) ℂ)) *
      ((Q⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    calc M = 1 * M * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
      _ = ((Q : Matrix (Fin D) (Fin D) ℂ) *
            ((Q⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) * M *
          ((Q : Matrix (Fin D) (Fin D) ℂ) *
            ((Q⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by rw [hQQ]
      _ = (Q : Matrix (Fin D) (Fin D) ℂ) *
            (((Q⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * M *
              (Q : Matrix (Fin D) (Fin D) ℂ)) *
          ((Q⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
        simp only [Matrix.mul_assoc]
  rw [hMrep]
  apply hmem
  rw [show Submodule.span ℂ (Set.range fun τ : Fin L → Fin d =>
    evalWord B (List.ofFn τ)) = ⊤ from hB]
  exact Submodule.mem_top

end MPSTensor

namespace TNLean
namespace PEPS

/-! ### The strengthened closed-chain corollaries -/

/-- **Fundamental Theorem for translation-invariant normal MPS at
`n ≥ 2L + 1`, single-gauge form** (arXiv:1804.04964, Section `normal_alt`,
the corollary after Lemma 5, lines 2256--2295 of
`Papers/1804.04964/paper_normal.tex`).

Two matrix tensors `A` and `B` on `n ≥ 2L + 1` sites, each `L`-block
injective — the matrix form of "blocking `L` consecutive sites results in an
injective tensor" — generating the same closed-chain state at the single
size `n`, are related by one invertible matrix `Z` and a constant `λ` with
`λ^n = 1` through `B^i = λ · Z⁻¹ A^i Z` for every `i`.

This strengthens `fundamentalTheorem_normalMPS_translationInvariant` from
`n ≥ 3L` to the source's `n ≥ 2L + 1` by replacing the three-arc cover with
the overlapping-window route: the insertion correspondence of Lemma 5 gives
conjugate word products at length `n`
(`MPSTensor.exists_conjugation_of_mpv_eq`), and the rigidity of word
products at one length (`MPSTensor.proportional_of_evalWord_eq`) turns the
conjugation into the letterwise gauge relation.  The uniqueness clause of
the source corollary needs no system size and is
`fundamentalTheorem_normalMPS_translationInvariant_gauge_unique`.

Source: arXiv:1804.04964, Section `normal_alt`, the corollary after Lemma 5,
lines 2256--2295 of `Papers/1804.04964/paper_normal.tex`. -/
theorem fundamentalTheorem_normalMPS_translationInvariant_of_overlap
    {n L d D : ℕ} (hL : 0 < L) (hn : 2 * L + 1 ≤ n) (A B : MPSTensor d D)
    (hA : MPSTensor.IsNBlkInjective A L) (hB : MPSTensor.IsNBlkInjective B L)
    (hAB : ∀ σ : Fin n → Fin d, MPSTensor.mpv A σ = MPSTensor.mpv B σ) :
    ∃ (Z : GL (Fin D) ℂ) (lam : ℂ), lam ^ n = 1 ∧
      ∀ i : Fin d, B i = lam • ((Z⁻¹ : GL (Fin D) ℂ) * A i * (Z : GL (Fin D) ℂ)) := by
  rcases Nat.eq_zero_or_pos D with hD0 | hD
  · subst hD0
    refine ⟨1, 1, one_pow n, fun i => ?_⟩
    apply Matrix.ext
    intro a b
    exact a.elim0
  -- The conjugation at length `n` from the insertion correspondence.
  obtain ⟨P, hP⟩ := MPSTensor.exists_conjugation_of_mpv_eq hL hn A B hA hB hAB
  -- Absorb the gauge: the conjugated `B` has equal word products with `A`.
  set Q : GL (Fin D) ℂ := P⁻¹ with hQdef
  set C : MPSTensor d D := fun i => (Q : Matrix (Fin D) (Fin D) ℂ) * B i *
    ((Q⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) with hCdef
  have hCw : ∀ w : List (Fin d), MPSTensor.evalWord C w =
      (Q : Matrix (Fin D) (Fin D) ℂ) * MPSTensor.evalWord B w *
        ((Q⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
    MPSTensor.evalWord_gauge Q (fun i => rfl)
  have hCA : ∀ w : List (Fin d), w.length = n →
      MPSTensor.evalWord C w = MPSTensor.evalWord A w := by
    intro w hwlen
    rw [hCw w, hP w hwlen, hQdef]
    rw [inv_inv]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  have hC : MPSTensor.IsNBlkInjective C L := MPSTensor.isNBlkInjective_conj hB Q
  -- Rigidity: the conjugated `B` is proportional to `A`.
  obtain ⟨lam, hlamn, hCi⟩ :=
    MPSTensor.proportional_of_evalWord_eq hL hn hD hA hC hCA
  refine ⟨Q, lam, hlamn, fun i => ?_⟩
  -- Reassemble: `B^i = λ · Q⁻¹ A^i Q`.
  have hBi : B i = ((Q⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * C i *
      (Q : Matrix (Fin D) (Fin D) ℂ) := by
    rw [hCdef]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  rw [hBi, hCi i, Matrix.mul_smul, Matrix.smul_mul]

/-- **Fundamental Theorem for translation-invariant normal MPS on a closed
chain at `n ≥ 2L + 1`, per-bond form** (arXiv:1804.04964, Section
`normal_alt`, the corollary after Lemma 5, lines 2256--2295 of
`Papers/1804.04964/paper_normal.tex`).

The per-bond gauge family delivered by `fundamentalTheorem_normalMPS` at
`n ≥ 3L` exists already at the source's `n ≥ 2L + 1`: invertible matrices
`Z_v`, one per bond of the closed chain, with `B^i = Z_v⁻¹ A^i Z_{v+1}` at
every site.  The family dresses the single gauge of the strengthened
translation-invariant corollary with powers of its root of unity,
`Z_v = λ^v Z`; conversely the matrix-level collapse
(`fundamentalTheorem_normalMPS_translationInvariant`) recovers the single
gauge from any such family, so the two forms agree.

Source: arXiv:1804.04964, Section `normal_alt`, the corollary after Lemma 5,
lines 2256--2295 of `Papers/1804.04964/paper_normal.tex`. -/
theorem fundamentalTheorem_normalMPS_of_overlap {n L d D : ℕ} [NeZero n]
    (hL : 0 < L) (hn : 2 * L + 1 ≤ n) (A B : MPSTensor d D)
    (hA : MPSTensor.IsNBlkInjective A L) (hB : MPSTensor.IsNBlkInjective B L)
    (hAB : ∀ σ : Fin n → Fin d, MPSTensor.mpv A σ = MPSTensor.mpv B σ) :
    ∃ Z : Fin n → GL (Fin D) ℂ, ∀ (v : Fin n) (i : Fin d),
      B i = ((Z v)⁻¹ : GL (Fin D) ℂ) * A i * (Z (v + 1) : GL (Fin D) ℂ) := by
  obtain ⟨Z₀, lam, hlamn, hZ₀⟩ :=
    fundamentalTheorem_normalMPS_translationInvariant_of_overlap hL hn A B hA hB hAB
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : n ≠ 0)] at hlamn
    exact zero_ne_one hlamn
  have hpow0 : ∀ m : ℕ, lam ^ m ≠ 0 := fun m => pow_ne_zero m hlam0
  -- The per-bond gauges: powers of the root of unity dress the single gauge.
  refine ⟨fun v => Units.mk (lam ^ v.val • (Z₀ : Matrix (Fin D) (Fin D) ℂ))
    ((lam ^ v.val)⁻¹ • ((Z₀⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (by rw [smul_mul_smul_comm, mul_inv_cancel₀ (hpow0 v.val), ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_smul])
    (by rw [smul_mul_smul_comm, inv_mul_cancel₀ (hpow0 v.val), ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_smul]), fun v i => ?_⟩
  rw [Units.inv_mk]
  change B i = ((lam ^ v.val)⁻¹ •
      ((Z₀⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) * A i *
    (lam ^ (v + 1).val • (Z₀ : Matrix (Fin D) (Fin D) ℂ))
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  -- The scalar collected around the bond is `λ`, including across the seam.
  have hscal : (lam ^ v.val)⁻¹ * lam ^ (v + 1).val = lam := by
    have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
    rw [Fin.val_add_eq_ite, h1]
    have hv := v.isLt
    by_cases hwrap : n ≤ v.val + 1
    · rw [if_pos hwrap]
      have hv' : v.val = n - 1 := by omega
      have hexp : v.val + 1 - n = 0 := by omega
      rw [hexp, pow_zero, mul_one, hv']
      -- `(λ^(n-1))⁻¹ = λ` because `λ · λ^(n-1) = λ^n = 1`.
      have hmul : lam * lam ^ (n - 1) = 1 := by
        rw [← pow_succ', show n - 1 + 1 = n by omega, hlamn]
      field_simp
      rw [← hmul]
      ring
    · rw [if_neg hwrap, pow_succ]
      rw [← mul_assoc, inv_mul_cancel₀ (hpow0 v.val), one_mul]
  rw [mul_comm (lam ^ ((v + 1 : Fin n) : ℕ)) ((lam ^ (v : ℕ))⁻¹), hscal]
  exact hZ₀ i

end PEPS
end TNLean
