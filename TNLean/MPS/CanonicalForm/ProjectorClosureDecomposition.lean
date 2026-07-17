/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.ProjectorClosure
import TNLean.MPS.CanonicalForm.CyclicSectors.Compression

/-!
# Direct-sum decomposition under invariant-projector closure

This file combines the reducing projections produced by the invariant-projector
closure condition of Cirac, Pérez-García, Schuch, and Verstraete,
arXiv:1606.00608, lines 253--254, into a direct-sum decomposition into
irreducible corner tensors.  This is the decomposition step towards the
canonical form \(A^i = \oplus_k \mu_k A_k^i\) of arXiv:1606.00608,
eq:II_CF1, lines 237--241.

Under projector closure every invariant orthogonal projection commutes with all
tensor matrices (`MPSTensor.commutes_of_hasInvariantProjectorClosure_of_lowerZero`),
so the two corners of such a projection are genuine compressions
\(V^\dagger A^i V\) along support isometries, not merely trace-equal blocks.
Strong induction on the bond dimension yields a family of isometries with
pairwise orthogonal ranges summing to the identity whose corner tensors are all
irreducible and intertwine the original tensor matrices.  No left-canonical or
unital normalization is assumed anywhere; the source proposition does not
provide one.

The remaining steps towards the full sufficient condition for canonical form —
rescaling each block to spectral radius one and converting the absence of
nontrivial periodic vectors into primitivity of every rescaled block — are
carried out in `TNLean.MPS.CanonicalForm.ProjectorClosureSpectral`; the
positive-length treatment of zero blocks is recorded in
`docs/paper-gaps/cpsv16_projector_closure_canonical_form.tex`.
-/

open scoped Matrix BigOperators

/-- Every orthogonal projection is the range projection of an isometry: there
are `n` and `V` with `Vᴴ * V = 1`, `V * Vᴴ = P`, and `n = tr P`.

This is the support-isometry factorization used by the sector compressions of
arXiv:1606.00608, Appendix A; it is stated here without any trace-preservation
hypothesis on a tensor. -/
theorem IsOrthogonalProjection.exists_support_isometry {D : ℕ}
    {P : Matrix (Fin D) (Fin D) ℂ} (hP : IsOrthogonalProjection P) :
    ∃ (n : ℕ) (V : Matrix (Fin D) (Fin n) ℂ),
      ((n : ℂ) = Matrix.trace P) ∧ Vᴴ * V = 1 ∧ V * Vᴴ = P := by
  obtain ⟨n, _C, _φ, V, hdim, _hTP, _hMPV, _hInt, _hMul, _hStar, _hLetter,
      hViso, hVrange, _hEmbed⟩ :=
    MPSTensor.exists_compressedTensor_of_supported_projection_with_letter_and_isometry
      (d := 1) (fun _ => P) P hP
      (fun _ => by simp [hP.2])
      (by simp [hP.1.eq, hP.2])
  exact ⟨n, V, hdim, hViso, hVrange⟩

namespace MPSTensor

variable {d D : ℕ}

/-- If the range projection `V * Vᴴ` of the isometry `V` commutes with every
tensor matrix, then each `A i` intertwines `V` with the corner matrix
`Vᴴ * A i * V`.

This records that the corners of a reducing projection in
arXiv:1606.00608, lines 253--254, are genuine compressions. -/
private lemma mul_isometry_of_commutes {n : ℕ} (A : MPSTensor d D)
    (V : Matrix (Fin D) (Fin n) ℂ) (hV : Vᴴ * V = 1)
    (hComm : ∀ i : Fin d, A i * (V * Vᴴ) = (V * Vᴴ) * A i) (i : Fin d) :
    A i * V = V * (Vᴴ * A i * V) := by
  have hPV : (V * Vᴴ) * V = V := by rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  calc A i * V
      = A i * ((V * Vᴴ) * V) := by rw [hPV]
    _ = (A i * (V * Vᴴ)) * V := (Matrix.mul_assoc _ _ _).symm
    _ = ((V * Vᴴ) * A i) * V := by rw [hComm i]
    _ = V * (Vᴴ * A i * V) := by simp only [Matrix.mul_assoc]

/-- Adjoint counterpart of `mul_isometry_of_commutes`: the corner matrix
`Vᴴ * A i * V` intertwines `Vᴴ` with `A i`. -/
private lemma conjTranspose_isometry_mul_of_commutes {n : ℕ} (A : MPSTensor d D)
    (V : Matrix (Fin D) (Fin n) ℂ) (hV : Vᴴ * V = 1)
    (hComm : ∀ i : Fin d, A i * (V * Vᴴ) = (V * Vᴴ) * A i) (i : Fin d) :
    Vᴴ * A i = (Vᴴ * A i * V) * Vᴴ := by
  have hVP : Vᴴ * (V * Vᴴ) = Vᴴ := by rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  calc Vᴴ * A i
      = (Vᴴ * (V * Vᴴ)) * A i := by rw [hVP]
    _ = Vᴴ * ((V * Vᴴ) * A i) := Matrix.mul_assoc _ _ _
    _ = Vᴴ * (A i * (V * Vᴴ)) := by rw [← hComm i]
    _ = (Vᴴ * A i * V) * Vᴴ := by simp only [Matrix.mul_assoc]

/-- Corner tensors inherit invariant-projector closure.

If `A` satisfies the projector hypothesis of arXiv:1606.00608, lines 253--254,
and `V` is an isometry whose range projection `V * Vᴴ` commutes with every
tensor matrix, then the corner tensor `Vᴴ * A i * V` satisfies the same
projector hypothesis.  A left-invariant projection of the corner lifts along
`V` to a left-invariant projection of `A`, closure applies in the ambient
algebra, and compressing back returns the closure identity for the corner.
No normalization on `A` is assumed. -/
theorem hasInvariantProjectorClosure_compress_of_commutes
    (A : MPSTensor d D) (hClosure : HasInvariantProjectorClosure A)
    {n : ℕ} (V : Matrix (Fin D) (Fin n) ℂ) (hV : Vᴴ * V = 1)
    (hComm : ∀ i : Fin d, A i * (V * Vᴴ) = (V * Vᴴ) * A i) :
    HasInvariantProjectorClosure (fun i => Vᴴ * A i * V) := by
  intro Q hQ hQleft
  -- The ambient lift `V * Q * Vᴴ` is an orthogonal projection.
  have hQ' : IsOrthogonalProjection (V * Q * Vᴴ) := by
    constructor
    · change (V * Q * Vᴴ)ᴴ = V * Q * Vᴴ
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hQ.1.eq]
      simp only [Matrix.mul_assoc]
    · show V * Q * Vᴴ * (V * Q * Vᴴ) = V * Q * Vᴴ
      calc V * Q * Vᴴ * (V * Q * Vᴴ)
          = V * Q * ((Vᴴ * V) * (Q * Vᴴ)) := by simp only [Matrix.mul_assoc]
        _ = V * Q * (Q * Vᴴ) := by rw [hV, Matrix.one_mul]
        _ = V * (Q * Q) * Vᴴ := by simp only [Matrix.mul_assoc]
        _ = V * Q * Vᴴ := by rw [hQ.2]
  -- The lift is left-invariant for the ambient tensor.
  have hlift : ∀ i : Fin d,
      (V * Q * Vᴴ) * A i = (V * Q * Vᴴ) * A i * (V * Q * Vᴴ) := by
    intro i
    have h1 : Vᴴ * A i = (Vᴴ * A i * V) * Vᴴ :=
      conjTranspose_isometry_mul_of_commutes A V hV hComm i
    have h2 : Q * (Vᴴ * A i * V) = Q * (Vᴴ * A i * V) * Q := hQleft i
    set B : Matrix (Fin n) (Fin n) ℂ := Vᴴ * A i * V with hB
    have hRHS : (V * Q * Vᴴ) * A i * (V * Q * Vᴴ) = V * (Q * B * Q) * Vᴴ := by
      calc (V * Q * Vᴴ) * A i * (V * Q * Vᴴ)
          = V * Q * ((Vᴴ * A i) * (V * Q * Vᴴ)) := by simp only [Matrix.mul_assoc]
        _ = V * Q * ((B * Vᴴ) * (V * Q * Vᴴ)) := by rw [h1]
        _ = V * Q * (B * ((Vᴴ * V) * (Q * Vᴴ))) := by simp only [Matrix.mul_assoc]
        _ = V * Q * (B * (Q * Vᴴ)) := by rw [hV, Matrix.one_mul]
        _ = V * (Q * B * Q) * Vᴴ := by simp only [Matrix.mul_assoc]
    calc (V * Q * Vᴴ) * A i
        = V * Q * (Vᴴ * A i) := by simp only [Matrix.mul_assoc]
      _ = V * Q * (B * Vᴴ) := by rw [h1]
      _ = V * (Q * B) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * (Q * B * Q) * Vᴴ := by rw [← h2]
      _ = (V * Q * Vᴴ) * A i * (V * Q * Vᴴ) := hRHS.symm
  -- Apply ambient closure and compress back.
  have happly := hClosure (V * Q * Vᴴ) hQ' hlift
  intro i
  change Vᴴ * A i * V * Q = Q * (Vᴴ * A i * V) * Q
  have h4 : Vᴴ * (A i * (V * Q * Vᴴ)) * V =
      Vᴴ * ((V * Q * Vᴴ) * A i * (V * Q * Vᴴ)) * V := by
    rw [happly i]
  have hL : Vᴴ * (A i * (V * Q * Vᴴ)) * V = Vᴴ * A i * V * Q := by
    calc Vᴴ * (A i * (V * Q * Vᴴ)) * V
        = (Vᴴ * A i * V) * (Q * (Vᴴ * V)) := by simp only [Matrix.mul_assoc]
      _ = (Vᴴ * A i * V) * Q := by rw [hV, Matrix.mul_one]
  have hR : Vᴴ * ((V * Q * Vᴴ) * A i * (V * Q * Vᴴ)) * V =
      Q * (Vᴴ * A i * V) * Q := by
    calc Vᴴ * ((V * Q * Vᴴ) * A i * (V * Q * Vᴴ)) * V
        = (Vᴴ * V) * (Q * ((Vᴴ * A i * V) * (Q * (Vᴴ * V)))) := by
          simp only [Matrix.mul_assoc]
      _ = Q * ((Vᴴ * A i * V) * Q) := by rw [hV, Matrix.one_mul, Matrix.mul_one]
      _ = Q * (Vᴴ * A i * V) * Q := (Matrix.mul_assoc _ _ _).symm
  rw [hL, hR] at h4
  exact h4

/-- Word evaluation is intertwined by an isometry that intertwines the letters. -/
private lemma evalWord_intertwine {n : ℕ} (A : MPSTensor d D) (B : MPSTensor d n)
    (V : Matrix (Fin D) (Fin n) ℂ) (hInt : ∀ i : Fin d, A i * V = V * B i) :
    ∀ w : List (Fin d), evalWord A w * V = V * evalWord B w := by
  intro w
  induction w with
  | nil => rw [evalWord_nil, evalWord_nil, Matrix.one_mul, Matrix.mul_one]
  | cons i w ihw =>
      rw [evalWord_cons, evalWord_cons]
      calc A i * evalWord A w * V
          = A i * (evalWord A w * V) := Matrix.mul_assoc _ _ _
        _ = A i * (V * evalWord B w) := by rw [ihw]
        _ = (A i * V) * evalWord B w := (Matrix.mul_assoc _ _ _).symm
        _ = (V * B i) * evalWord B w := by rw [hInt i]
        _ = V * (B i * evalWord B w) := Matrix.mul_assoc _ _ _

/-- If isometries with ranges summing to the identity intertwine the tensor
matrices with corner tensors, then the matrix product vectors of the tensor
agree with those of the unit-weight direct sum of the corner tensors.

This is the trace decomposition along the partition of unity used in the
direct-sum step of arXiv:1606.00608, eq:II_CF1, lines 237--241. -/
theorem sameMPV₂_toTensorFromBlocks_of_isometry_family
    {r : ℕ} {dim : Fin r → ℕ} (A : MPSTensor d D)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (V : (k : Fin r) → Matrix (Fin D) (Fin (dim k)) ℂ)
    (hiso : ∀ k, (V k)ᴴ * V k = 1)
    (hsum : ∑ k : Fin r, V k * (V k)ᴴ = 1)
    (hint : ∀ (k : Fin r) (i : Fin d), A i * V k = V k * blocks k i) :
    SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin r => (1 : ℂ)) blocks) := by
  intro N σ
  rw [mpv_toTensorFromBlocks_eq_sum]
  simp only [one_pow, one_smul]
  simp only [mpv, coeff]
  set w : List (Fin d) := List.ofFn σ with hw
  calc Matrix.trace (evalWord A w)
      = Matrix.trace ((∑ k : Fin r, V k * (V k)ᴴ) * evalWord A w) := by
        rw [hsum, Matrix.one_mul]
    _ = ∑ k : Fin r, Matrix.trace (V k * (V k)ᴴ * evalWord A w) := by
        rw [Finset.sum_mul, Matrix.trace_sum]
    _ = ∑ k : Fin r, Matrix.trace (evalWord (blocks k) w) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        calc Matrix.trace (V k * (V k)ᴴ * evalWord A w)
            = Matrix.trace (V k * ((V k)ᴴ * evalWord A w)) := by
              rw [Matrix.mul_assoc]
          _ = Matrix.trace (((V k)ᴴ * evalWord A w) * V k) := Matrix.trace_mul_comm _ _
          _ = Matrix.trace ((V k)ᴴ * (evalWord A w * V k)) := by rw [Matrix.mul_assoc]
          _ = Matrix.trace ((V k)ᴴ * (V k * evalWord (blocks k) w)) := by
              rw [evalWord_intertwine A (blocks k) (V k) (hint k) w]
          _ = Matrix.trace (((V k)ᴴ * V k) * evalWord (blocks k) w) := by
              rw [Matrix.mul_assoc]
          _ = Matrix.trace (evalWord (blocks k) w) := by rw [hiso k, Matrix.one_mul]

/-- Strong-induction core of the direct-sum decomposition under
invariant-projector closure (arXiv:1606.00608, lines 253--254): every tensor with projector
closure carries a family of isometries with pairwise orthogonal ranges summing
to the identity whose corner tensors are irreducible and intertwine the tensor
matrices. -/
private theorem exists_irreducible_isometry_family_aux :
    ∀ (D : ℕ) (A : MPSTensor d D), HasInvariantProjectorClosure A →
      ∃ (r : ℕ) (dim : Fin r → ℕ) (blocks : (k : Fin r) → MPSTensor d (dim k))
        (V : (k : Fin r) → Matrix (Fin D) (Fin (dim k)) ℂ),
        (∀ k, 0 < dim k) ∧
        (∀ k, (V k)ᴴ * V k = 1) ∧
        (∑ k : Fin r, V k * (V k)ᴴ = 1) ∧
        (∀ k l, k ≠ l → (V k)ᴴ * V l = 0) ∧
        (∀ (k : Fin r) (i : Fin d), A i * V k = V k * blocks k i) ∧
        (∀ (k : Fin r) (i : Fin d), (V k)ᴴ * A i = blocks k i * (V k)ᴴ) ∧
        (∀ k, IsIrreducibleTensor (blocks k)) := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro A hClosure
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · -- Trivial bond dimension: the empty family.
    subst hD0
    exact ⟨0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0,
      fun k => k.elim0, fun k => k.elim0,
      by ext i j; exact i.elim0,
      fun k => k.elim0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0⟩
  by_cases hirrA : IsIrreducibleTensor A
  · -- Base case: `A` itself is irreducible; take the single corner `V = 1`.
    refine ⟨1, fun _ => D, fun _ => A, fun _ => (1 : Matrix (Fin D) (Fin D) ℂ),
      fun _ => hDpos, fun _ => by simp, by simp, ?_, fun _ i => by simp,
      fun _ i => by simp, fun _ => hirrA⟩
    intro k l hkl
    exact absurd (Subsingleton.elim k l) hkl
  -- Inductive step: split along a reducing projection and recurse on the corners.
  rw [IsIrreducibleTensor, not_not] at hirrA
  obtain ⟨P, hPproj, hP0, hP1, hLower⟩ := hirrA
  have hCommP : ∀ i : Fin d, P * A i = A i * P :=
    commutes_of_hasInvariantProjectorClosure_of_lowerZero A P hClosure hPproj hLower
  obtain ⟨n, V₁, hn_tr, hV₁iso, hV₁range⟩ := hPproj.exists_support_isometry
  obtain ⟨m, V₂, hm_tr, hV₂iso, hV₂range⟩ := hPproj.one_sub.exists_support_isometry
  -- Corner bond dimensions are positive and sum to `D`.
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h
    · exfalso
      apply hP0
      rw [← hV₁range]
      subst h0
      ext i j
      simp [Matrix.mul_apply]
    · exact h
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · exfalso
      apply sub_ne_zero_of_ne (Ne.symm hP1)
      rw [← hV₂range]
      subst h0
      ext i j
      simp [Matrix.mul_apply]
    · exact h
  have hnm : n + m = D := by
    have h1 : ((n : ℂ) + (m : ℂ)) = (D : ℂ) := by
      rw [hn_tr, hm_tr, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin]
      ring
    exact_mod_cast h1
  have hn_lt : n < D := by omega
  have hm_lt : m < D := by omega
  -- The two range projections commute with every tensor matrix.
  have hComm₁ : ∀ i : Fin d, A i * (V₁ * V₁ᴴ) = (V₁ * V₁ᴴ) * A i := by
    intro i
    rw [hV₁range]
    exact (hCommP i).symm
  have hComm₂ : ∀ i : Fin d, A i * (V₂ * V₂ᴴ) = (V₂ * V₂ᴴ) * A i := by
    intro i
    rw [hV₂range, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      hCommP i]
  -- Both corners inherit projector closure; recurse.
  have hClosure₁ : HasInvariantProjectorClosure (fun i => V₁ᴴ * A i * V₁) :=
    hasInvariantProjectorClosure_compress_of_commutes A hClosure V₁ hV₁iso hComm₁
  have hClosure₂ : HasInvariantProjectorClosure (fun i => V₂ᴴ * A i * V₂) :=
    hasInvariantProjectorClosure_compress_of_commutes A hClosure V₂ hV₂iso hComm₂
  obtain ⟨r₁, dim₁, blocks₁, W₁, hpos₁, hiso₁, hsum₁, horth₁, hint₁raw, hintstar₁raw,
      hirr₁⟩ := ih n hn_lt (fun i => V₁ᴴ * A i * V₁) hClosure₁
  obtain ⟨r₂, dim₂, blocks₂, W₂, hpos₂, hiso₂, hsum₂, horth₂, hint₂raw, hintstar₂raw,
      hirr₂⟩ := ih m hm_lt (fun i => V₂ᴴ * A i * V₂) hClosure₂
  have hint₁ : ∀ (a : Fin r₁) (i : Fin d),
      V₁ᴴ * A i * V₁ * W₁ a = W₁ a * blocks₁ a i := hint₁raw
  have hint₂ : ∀ (a : Fin r₂) (i : Fin d),
      V₂ᴴ * A i * V₂ * W₂ a = W₂ a * blocks₂ a i := hint₂raw
  have hintstar₁ : ∀ (a : Fin r₁) (i : Fin d),
      (W₁ a)ᴴ * (V₁ᴴ * A i * V₁) = blocks₁ a i * (W₁ a)ᴴ := hintstar₁raw
  have hintstar₂ : ∀ (a : Fin r₂) (i : Fin d),
      (W₂ a)ᴴ * (V₂ᴴ * A i * V₂) = blocks₂ a i * (W₂ a)ᴴ := hintstar₂raw
  have hAmb₁ : ∀ i : Fin d, A i * V₁ = V₁ * (V₁ᴴ * A i * V₁) :=
    mul_isometry_of_commutes A V₁ hV₁iso hComm₁
  have hAmb₂ : ∀ i : Fin d, A i * V₂ = V₂ * (V₂ᴴ * A i * V₂) :=
    mul_isometry_of_commutes A V₂ hV₂iso hComm₂
  have hAmbStar₁ : ∀ i : Fin d, V₁ᴴ * A i = (V₁ᴴ * A i * V₁) * V₁ᴴ :=
    conjTranspose_isometry_mul_of_commutes A V₁ hV₁iso hComm₁
  have hAmbStar₂ : ∀ i : Fin d, V₂ᴴ * A i = (V₂ᴴ * A i * V₂) * V₂ᴴ :=
    conjTranspose_isometry_mul_of_commutes A V₂ hV₂iso hComm₂
  -- Cross-orthogonality of the two support isometries.
  have hV₁V₂ : V₁ᴴ * V₂ = 0 := by
    have hV₂supp : (1 - P) * V₂ = V₂ := by
      rw [← hV₂range, Matrix.mul_assoc, hV₂iso, Matrix.mul_one]
    have hV₁P : V₁ᴴ * P = V₁ᴴ := by
      rw [← hV₁range, ← Matrix.mul_assoc, hV₁iso, Matrix.one_mul]
    calc V₁ᴴ * V₂
        = V₁ᴴ * ((1 - P) * V₂) := by rw [hV₂supp]
      _ = (V₁ᴴ * (1 - P)) * V₂ := (Matrix.mul_assoc _ _ _).symm
      _ = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hV₁P, sub_self, Matrix.zero_mul]
  have hV₂V₁ : V₂ᴴ * V₁ = 0 := by
    have h := congrArg Matrix.conjTranspose hV₁V₂
    simpa [Matrix.conjTranspose_mul] using h
  -- Combine the two recursive families over the sum index type.
  let dimS : Fin r₁ ⊕ Fin r₂ → ℕ := Sum.elim dim₁ dim₂
  let blocksS : (s : Fin r₁ ⊕ Fin r₂) → MPSTensor d (dimS s) := fun s =>
    Sum.rec (motive := fun s => MPSTensor d (dimS s))
      (fun a => blocks₁ a) (fun a => blocks₂ a) s
  let VS : (s : Fin r₁ ⊕ Fin r₂) → Matrix (Fin D) (Fin (dimS s)) ℂ := fun s =>
    Sum.rec (motive := fun s => Matrix (Fin D) (Fin (dimS s)) ℂ)
      (fun a => V₁ * W₁ a) (fun a => V₂ * W₂ a) s
  have hposS : ∀ s, 0 < dimS s := by
    rintro (a | a)
    exacts [hpos₁ a, hpos₂ a]
  have hisoS : ∀ s, (VS s)ᴴ * VS s = 1 := by
    rintro (a | a)
    · change (V₁ * W₁ a)ᴴ * (V₁ * W₁ a) = 1
      calc (V₁ * W₁ a)ᴴ * (V₁ * W₁ a)
          = (W₁ a)ᴴ * ((V₁ᴴ * V₁) * W₁ a) := by
            rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = (W₁ a)ᴴ * W₁ a := by rw [hV₁iso, Matrix.one_mul]
        _ = 1 := hiso₁ a
    · change (V₂ * W₂ a)ᴴ * (V₂ * W₂ a) = 1
      calc (V₂ * W₂ a)ᴴ * (V₂ * W₂ a)
          = (W₂ a)ᴴ * ((V₂ᴴ * V₂) * W₂ a) := by
            rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = (W₂ a)ᴴ * W₂ a := by rw [hV₂iso, Matrix.one_mul]
        _ = 1 := hiso₂ a
  have hsumS : ∑ s : Fin r₁ ⊕ Fin r₂, VS s * (VS s)ᴴ = 1 := by
    have h₁ : ∀ a : Fin r₁, VS (Sum.inl a) * (VS (Sum.inl a))ᴴ
        = V₁ * (W₁ a * (W₁ a)ᴴ) * V₁ᴴ := by
      intro a
      change (V₁ * W₁ a) * (V₁ * W₁ a)ᴴ = V₁ * (W₁ a * (W₁ a)ᴴ) * V₁ᴴ
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have h₂ : ∀ a : Fin r₂, VS (Sum.inr a) * (VS (Sum.inr a))ᴴ
        = V₂ * (W₂ a * (W₂ a)ᴴ) * V₂ᴴ := by
      intro a
      change (V₂ * W₂ a) * (V₂ * W₂ a)ᴴ = V₂ * (W₂ a * (W₂ a)ᴴ) * V₂ᴴ
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have hleft : ∑ a : Fin r₁, V₁ * (W₁ a * (W₁ a)ᴴ) * V₁ᴴ = P := by
      rw [← Matrix.sum_mul, ← Matrix.mul_sum, hsum₁, Matrix.mul_one, hV₁range]
    have hright : ∑ a : Fin r₂, V₂ * (W₂ a * (W₂ a)ᴴ) * V₂ᴴ = 1 - P := by
      rw [← Matrix.sum_mul, ← Matrix.mul_sum, hsum₂, Matrix.mul_one, hV₂range]
    calc ∑ s : Fin r₁ ⊕ Fin r₂, VS s * (VS s)ᴴ
        = (∑ a : Fin r₁, VS (Sum.inl a) * (VS (Sum.inl a))ᴴ) +
          (∑ a : Fin r₂, VS (Sum.inr a) * (VS (Sum.inr a))ᴴ) :=
          Fintype.sum_sum_type (fun s : Fin r₁ ⊕ Fin r₂ => VS s * (VS s)ᴴ)
      _ = (∑ a : Fin r₁, V₁ * (W₁ a * (W₁ a)ᴴ) * V₁ᴴ) +
          (∑ a : Fin r₂, V₂ * (W₂ a * (W₂ a)ᴴ) * V₂ᴴ) := by
          congr 1
          · exact Finset.sum_congr rfl fun a _ => h₁ a
          · exact Finset.sum_congr rfl fun a _ => h₂ a
      _ = P + (1 - P) := by rw [hleft, hright]
      _ = 1 := by abel
  have horthS : ∀ s t : Fin r₁ ⊕ Fin r₂, s ≠ t → (VS s)ᴴ * VS t = 0 := by
    rintro (a | a) (b | b) hst
    · have hab : a ≠ b := fun h => hst (congrArg Sum.inl h)
      change (V₁ * W₁ a)ᴴ * (V₁ * W₁ b) = 0
      calc (V₁ * W₁ a)ᴴ * (V₁ * W₁ b)
          = (W₁ a)ᴴ * ((V₁ᴴ * V₁) * W₁ b) := by
            rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = (W₁ a)ᴴ * W₁ b := by rw [hV₁iso, Matrix.one_mul]
        _ = 0 := horth₁ a b hab
    · change (V₁ * W₁ a)ᴴ * (V₂ * W₂ b) = 0
      calc (V₁ * W₁ a)ᴴ * (V₂ * W₂ b)
          = (W₁ a)ᴴ * ((V₁ᴴ * V₂) * W₂ b) := by
            rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hV₁V₂, Matrix.zero_mul, Matrix.mul_zero]
    · change (V₂ * W₂ a)ᴴ * (V₁ * W₁ b) = 0
      calc (V₂ * W₂ a)ᴴ * (V₁ * W₁ b)
          = (W₂ a)ᴴ * ((V₂ᴴ * V₁) * W₁ b) := by
            rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hV₂V₁, Matrix.zero_mul, Matrix.mul_zero]
    · have hab : a ≠ b := fun h => hst (congrArg Sum.inr h)
      change (V₂ * W₂ a)ᴴ * (V₂ * W₂ b) = 0
      calc (V₂ * W₂ a)ᴴ * (V₂ * W₂ b)
          = (W₂ a)ᴴ * ((V₂ᴴ * V₂) * W₂ b) := by
            rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = (W₂ a)ᴴ * W₂ b := by rw [hV₂iso, Matrix.one_mul]
        _ = 0 := horth₂ a b hab
  have hintS : ∀ (s : Fin r₁ ⊕ Fin r₂) (i : Fin d),
      A i * VS s = VS s * blocksS s i := by
    rintro (a | a) i
    · change A i * (V₁ * W₁ a) = (V₁ * W₁ a) * blocks₁ a i
      have h1 : A i * V₁ = V₁ * (V₁ᴴ * A i * V₁) := hAmb₁ i
      have h2 : (V₁ᴴ * A i * V₁) * W₁ a = W₁ a * blocks₁ a i := hint₁ a i
      set B : Matrix (Fin n) (Fin n) ℂ := V₁ᴴ * A i * V₁ with hB
      calc A i * (V₁ * W₁ a)
          = (A i * V₁) * W₁ a := (Matrix.mul_assoc _ _ _).symm
        _ = (V₁ * B) * W₁ a := by rw [h1]
        _ = V₁ * (B * W₁ a) := Matrix.mul_assoc _ _ _
        _ = V₁ * (W₁ a * blocks₁ a i) := by rw [h2]
        _ = (V₁ * W₁ a) * blocks₁ a i := (Matrix.mul_assoc _ _ _).symm
    · change A i * (V₂ * W₂ a) = (V₂ * W₂ a) * blocks₂ a i
      have h1 : A i * V₂ = V₂ * (V₂ᴴ * A i * V₂) := hAmb₂ i
      have h2 : (V₂ᴴ * A i * V₂) * W₂ a = W₂ a * blocks₂ a i := hint₂ a i
      set B : Matrix (Fin m) (Fin m) ℂ := V₂ᴴ * A i * V₂ with hB
      calc A i * (V₂ * W₂ a)
          = (A i * V₂) * W₂ a := (Matrix.mul_assoc _ _ _).symm
        _ = (V₂ * B) * W₂ a := by rw [h1]
        _ = V₂ * (B * W₂ a) := Matrix.mul_assoc _ _ _
        _ = V₂ * (W₂ a * blocks₂ a i) := by rw [h2]
        _ = (V₂ * W₂ a) * blocks₂ a i := (Matrix.mul_assoc _ _ _).symm
  have hintStarS : ∀ (s : Fin r₁ ⊕ Fin r₂) (i : Fin d),
      (VS s)ᴴ * A i = blocksS s i * (VS s)ᴴ := by
    rintro (a | a) i
    · change (V₁ * W₁ a)ᴴ * A i = blocks₁ a i * (V₁ * W₁ a)ᴴ
      rw [Matrix.conjTranspose_mul]
      have h1 : V₁ᴴ * A i = (V₁ᴴ * A i * V₁) * V₁ᴴ := hAmbStar₁ i
      have h2 : (W₁ a)ᴴ * (V₁ᴴ * A i * V₁) = blocks₁ a i * (W₁ a)ᴴ := hintstar₁ a i
      set B : Matrix (Fin n) (Fin n) ℂ := V₁ᴴ * A i * V₁ with hB
      calc ((W₁ a)ᴴ * V₁ᴴ) * A i
          = (W₁ a)ᴴ * (V₁ᴴ * A i) := Matrix.mul_assoc _ _ _
        _ = (W₁ a)ᴴ * (B * V₁ᴴ) := by rw [h1]
        _ = ((W₁ a)ᴴ * B) * V₁ᴴ := (Matrix.mul_assoc _ _ _).symm
        _ = (blocks₁ a i * (W₁ a)ᴴ) * V₁ᴴ := by rw [h2]
        _ = blocks₁ a i * ((W₁ a)ᴴ * V₁ᴴ) := Matrix.mul_assoc _ _ _
    · change (V₂ * W₂ a)ᴴ * A i = blocks₂ a i * (V₂ * W₂ a)ᴴ
      rw [Matrix.conjTranspose_mul]
      have h1 : V₂ᴴ * A i = (V₂ᴴ * A i * V₂) * V₂ᴴ := hAmbStar₂ i
      have h2 : (W₂ a)ᴴ * (V₂ᴴ * A i * V₂) = blocks₂ a i * (W₂ a)ᴴ := hintstar₂ a i
      set B : Matrix (Fin m) (Fin m) ℂ := V₂ᴴ * A i * V₂ with hB
      calc ((W₂ a)ᴴ * V₂ᴴ) * A i
          = (W₂ a)ᴴ * (V₂ᴴ * A i) := Matrix.mul_assoc _ _ _
        _ = (W₂ a)ᴴ * (B * V₂ᴴ) := by rw [h1]
        _ = ((W₂ a)ᴴ * B) * V₂ᴴ := (Matrix.mul_assoc _ _ _).symm
        _ = (blocks₂ a i * (W₂ a)ᴴ) * V₂ᴴ := by rw [h2]
        _ = blocks₂ a i * ((W₂ a)ᴴ * V₂ᴴ) := Matrix.mul_assoc _ _ _
  have hirrS : ∀ s, IsIrreducibleTensor (blocksS s) := by
    rintro (a | a)
    exacts [hirr₁ a, hirr₂ a]
  -- Reindex the sum type to `Fin (r₁ + r₂)`.
  refine ⟨r₁ + r₂, fun k => dimS (finSumFinEquiv.symm k),
    fun k => blocksS (finSumFinEquiv.symm k), fun k => VS (finSumFinEquiv.symm k),
    fun k => hposS (finSumFinEquiv.symm k),
    fun k => hisoS (finSumFinEquiv.symm k), ?_,
    fun k l hkl => horthS _ _ fun h => hkl (finSumFinEquiv.symm.injective h),
    fun k i => hintS (finSumFinEquiv.symm k) i,
    fun k i => hintStarS (finSumFinEquiv.symm k) i,
    fun k => hirrS (finSumFinEquiv.symm k)⟩
  calc ∑ k : Fin (r₁ + r₂), VS (finSumFinEquiv.symm k) * (VS (finSumFinEquiv.symm k))ᴴ
      = ∑ s : Fin r₁ ⊕ Fin r₂, VS s * (VS s)ᴴ :=
        Equiv.sum_comp finSumFinEquiv.symm (fun s => VS s * (VS s)ᴴ)
    _ = 1 := hsumS

/-- **Direct-sum decomposition into irreducible corners under projector
closure** (arXiv:1606.00608, lines 253--254).

If `A` satisfies the invariant-projector closure condition, then there are
isometries `V k` with pairwise orthogonal ranges summing to the identity such
that every tensor matrix `A i` commutes with each range projection, the corner
tensors `blocks k i = (V k)ᴴ * A i * V k` are irreducible, and the matrix
product vectors of `A` equal those of the unit-weight direct sum of the corner
tensors.

This combines the reducing projections of
`MPSTensor.exists_reducing_projection_of_hasInvariantProj` into the direct-sum
decomposition of the canonical form of arXiv:1606.00608, eq:II_CF1,
lines 237--241.
Unlike `MPSTensor.exists_irreducible_blockDecomp`, the corner tensors are
related to `A` by the intertwining `A i * V k = V k * blocks k i`, not only by
equality of matrix product vectors, and no left-canonical normalization is
assumed.  The spectral steps — rescaling every block to spectral radius one
and deducing blockwise primitivity from the absence of nontrivial periodic
vectors — are carried out in
`TNLean.MPS.CanonicalForm.ProjectorClosureSpectral`. -/
theorem exists_irreducible_blockDecomp_with_isometry_of_hasInvariantProjectorClosure
    (A : MPSTensor d D) (hClosure : HasInvariantProjectorClosure A) :
    ∃ (r : ℕ) (dim : Fin r → ℕ) (blocks : (k : Fin r) → MPSTensor d (dim k))
      (V : (k : Fin r) → Matrix (Fin D) (Fin (dim k)) ℂ),
      (∀ k, 0 < dim k) ∧
      (∀ k, (V k)ᴴ * V k = 1) ∧
      (∑ k : Fin r, V k * (V k)ᴴ = 1) ∧
      (∀ k l, k ≠ l → (V k)ᴴ * V l = 0) ∧
      (∀ (k : Fin r) (i : Fin d), A i * V k = V k * blocks k i) ∧
      (∀ (k : Fin r) (i : Fin d), (V k)ᴴ * A i = blocks k i * (V k)ᴴ) ∧
      (∀ (k : Fin r) (i : Fin d), blocks k i = (V k)ᴴ * A i * V k) ∧
      (∀ k, IsIrreducibleTensor (blocks k)) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin r => (1 : ℂ)) blocks) := by
  obtain ⟨r, dim, blocks, V, hpos, hiso, hsum, horth, hint, hintstar, hirr⟩ :=
    exists_irreducible_isometry_family_aux D A hClosure
  have hcorner : ∀ (k : Fin r) (i : Fin d), blocks k i = (V k)ᴴ * A i * V k := by
    intro k i
    calc blocks k i
        = ((V k)ᴴ * V k) * blocks k i := by rw [hiso k, Matrix.one_mul]
      _ = (V k)ᴴ * (V k * blocks k i) := Matrix.mul_assoc _ _ _
      _ = (V k)ᴴ * (A i * V k) := by rw [← hint k i]
      _ = (V k)ᴴ * A i * V k := (Matrix.mul_assoc _ _ _).symm
  exact ⟨r, dim, blocks, V, hpos, hiso, hsum, horth, hint, hintstar, hcorner, hirr,
    sameMPV₂_toTensorFromBlocks_of_isometry_family A blocks V hiso hsum hint⟩

end MPSTensor
