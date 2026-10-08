/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.IntersectionProperty
import TNLean.MPS.ParentHamiltonian.CyclicWordSpan

/-!
# Cyclic boundary matrices and the one-step intersection property

The boundary map of a periodic tensor need only be injective on the opposite
cyclic matrix degree relevant to the interval length. Under this restricted
injectivity, the usual comparison of the two overlapping boundaries gives
the one-step intersection property. The left-canonical identity reconstructs
the boundary matrix of the enlarged interval.

The declarations below isolate this algebraic implication; they do not assume
injectivity on the whole matrix algebra. The eventual restricted injectivity
of a periodic tensor is a separate step.

Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.10)--(3.11)
and Lemma existenceinteraction; arXiv:1708.00029, Lemma bdcf.
-/

open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d D m : ℕ}

/-- The opposite cyclic degree-\(n\) boundary matrices satisfy
\(P_{u+n}X=XP_u\). Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.10)--(3.11), with the cyclic-sector coordinates of
arXiv:1708.00029, Lemma bdcf. -/
def cyclicBoundarySpace
    (P : ZMod m → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) where
  carrier := {X | ∀ u, P (u + n) * X = X * P u}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY u
    simp only [Matrix.mul_add, Matrix.add_mul, hX u, hY u]
  smul_mem' := by
    intro c X hX u
    simp only [Matrix.mul_smul, Matrix.smul_mul, hX u]

/-- Multiplication by one physical matrix lowers the opposite cyclic degree.
Source: arXiv:1708.00029, Lemma bdcf. -/
theorem cyclicBoundarySpace_mul_left
    (A : MPSTensor d D) (P : ZMod m → Matrix (Fin D) (Fin D) ℂ)
    (hCycle : ∀ u i, P u * A i = A i * P (u + 1))
    {n : ℕ} {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ cyclicBoundarySpace P (n + 1)) (i : Fin d) :
    A i * X ∈ cyclicBoundarySpace P n := by
  intro u
  rw [← Matrix.mul_assoc, hCycle, Matrix.mul_assoc]
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, Matrix.mul_assoc] using
    congrArg (fun Y => A i * Y) (hX u)

/-- Right multiplication by one physical matrix lowers the opposite cyclic degree.
Source: arXiv:1708.00029, Lemma bdcf. -/
theorem cyclicBoundarySpace_mul_right
    (A : MPSTensor d D) (P : ZMod m → Matrix (Fin D) (Fin D) ℂ)
    (hCycle : ∀ u i, P u * A i = A i * P (u + 1))
    {n : ℕ} {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ cyclicBoundarySpace P (n + 1)) (i : Fin d) :
    X * A i ∈ cyclicBoundarySpace P n := by
  intro u
  have h := hX (u - 1)
  have hindex : u - 1 + ((n + 1 : ℕ) : ZMod m) = u + n := by
    simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [← hindex, ← Matrix.mul_assoc, h, Matrix.mul_assoc, hCycle,
    sub_add_cancel, ← Matrix.mul_assoc]

/-- Restricted cyclic-boundary injectivity gives the one-step intersection
property. Source: Nachtergaele, arXiv:cond-mat/9410110, equations
(3.10)--(3.11) and Lemma existenceinteraction. The hypotheses concern
only the relevant cyclic matrix corners, not the full matrix algebra. -/
theorem mem_groundSpace_of_cyclicBoundary_restrictions
    (A : MPSTensor d D) (P : ZMod m → Matrix (Fin D) (Fin D) ℂ)
    (hCycle : ∀ u i, P u * A i = A i * P (u + 1))
    (hLeftCanonical : ∑ i, (A i)ᴴ * A i = 1) {n : ℕ}
    (hRepresent : ∀ ψ ∈ groundSpace A (n + 1),
      ∃ X ∈ cyclicBoundarySpace P (n + 1), groundSpaceMap A (n + 1) X = ψ)
    (hInjective : Set.InjOn (groundSpaceMap A n)
      (cyclicBoundarySpace P n : Set (Matrix (Fin D) (Fin D) ℂ)))
    {ψ : NSiteSpace d (n + 2)}
    (hLeft : InLeftGround A (n + 1) ψ)
    (hRight : InRightGround A (n + 1) ψ) :
    ψ ∈ groundSpace A (n + 2) := by
  classical
  choose Y hYmem hY using fun i => hRepresent _ (hRight i)
  choose Z hZmem hZ using fun j => hRepresent _ (hLeft j)
  have hCompat : ∀ i j, A j * Y i = Z j * A i := fun i j =>
    hInjective (cyclicBoundarySpace_mul_left A P hCycle (hYmem i) j)
      (cyclicBoundarySpace_mul_right A P hCycle (hZmem j) i)
      (groundSpaceMap_mul_eq_of_restrict (fun i => (hY i).symm)
        (fun j => (hZ j).symm) i j)
  exact mem_groundSpace_succ_of_intertwine (fun j => (A j)ᴴ) hLeftCanonical
    (fun i => (hY i).symm) hCompat

/-- The cyclic-boundary criterion identifies the intersection of both
one-site restrictions with the enlarged ground space.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.10)--(3.11). -/
theorem groundSpace_eq_restriction_intersection_of_cyclicBoundary
    (A : MPSTensor d D) (P : ZMod m → Matrix (Fin D) (Fin D) ℂ)
    (hCycle : ∀ u i, P u * A i = A i * P (u + 1))
    (hLeftCanonical : ∑ i, (A i)ᴴ * A i = 1) {n : ℕ}
    (hRepresent : ∀ ψ ∈ groundSpace A (n + 1),
      ∃ X ∈ cyclicBoundarySpace P (n + 1), groundSpaceMap A (n + 1) X = ψ)
    (hInjective : Set.InjOn (groundSpaceMap A n)
      (cyclicBoundarySpace P n : Set (Matrix (Fin D) (Fin D) ℂ))) :
    ((⨅ b : Fin d, (groundSpace A (n + 1)).comap (restrictLastₗ b)) ⊓
      ⨅ a : Fin d, (groundSpace A (n + 1)).comap (restrictFirstₗ a)) =
      groundSpace A (n + 2) := by
  ext ψ
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
  exact ⟨fun h => mem_groundSpace_of_cyclicBoundary_restrictions A P hCycle
      hLeftCanonical hRepresent hInjective h.1 h.2,
    fun h => ⟨groundSpace_inLeftGround A (n + 1) h,
      groundSpace_inRightGround A (n + 1) h⟩⟩

/-- Compression to opposite cyclic corners has the required boundary degree.
Source: arXiv:1708.00029, Lemma bdcf. -/
theorem sum_cyclicBoundary_mem [NeZero m]
    (P : ZMod m → Matrix (Fin D) (Fin D) ℂ)
    (hOrth : ∀ u v, P u * P v = if u = v then P u else 0)
    (n : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    (∑ u : ZMod m, P (u + n) * X * P u) ∈ cyclicBoundarySpace P n := by
  classical
  intro v
  have hL : P (v + n) * (∑ u : ZMod m, P (u + n) * X * P u) =
      P (v + n) * X * P v := by
    simp [Finset.mul_sum, ← Matrix.mul_assoc, hOrth]
  have hR : (∑ u : ZMod m, P (u + n) * X * P u) * P v =
      P (v + n) * X * P v := by
    simp [Finset.sum_mul, Matrix.mul_assoc, hOrth]
  exact hL.trans hR.symm

/-- Compression to opposite cyclic corners preserves every open-boundary MPS vector.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.10)--(3.11). -/
theorem groundSpaceMap_sum_cyclicBoundary [NeZero m]
    (A : MPSTensor d D) (P : ZMod m → Matrix (Fin D) (Fin D) ℂ)
    (hOrth : ∀ u v, P u * P v = if u = v then P u else 0)
    (hSum : ∑ u : ZMod m, P u = 1) (n : ℕ)
    (hWord : ∀ u (σ : Fin n → Fin d),
      P u * Kraus.evalWord A (List.ofFn σ) =
        Kraus.evalWord A (List.ofFn σ) * P (u + n))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    groundSpaceMap A n (∑ u : ZMod m, P (u + n) * X * P u) =
      groundSpaceMap A n X := by
  ext σ
  have hCorner (u : ZMod m) :
      P u * Kraus.evalWord A (List.ofFn σ) * P (u + n) =
        P u * Kraus.evalWord A (List.ofFn σ) := by
    rw [hWord, Matrix.mul_assoc, hOrth]
    simp
  have hTerm (u : ZMod m) :
      Matrix.trace (Kraus.evalWord A (List.ofFn σ) * (P (u + n) * X * P u)) =
        Matrix.trace (P u * Kraus.evalWord A (List.ofFn σ) * X) := by
    simpa only [← Matrix.mul_assoc, hCorner] using
      Matrix.trace_mul_cycle' (Kraus.evalWord A (List.ofFn σ)) (P (u + n) * X) (P u)
  simp only [groundSpaceMap_apply, Finset.mul_sum, Matrix.trace_sum, hTerm]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.sum_mul, hSum, Matrix.one_mul]

/-- Every open-boundary MPS vector has a representative in its opposite cyclic degree.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.10)--(3.11). -/
theorem exists_cyclicBoundary_of_mem_groundSpace [NeZero m]
    (A : MPSTensor d D) (P : ZMod m → Matrix (Fin D) (Fin D) ℂ)
    (hOrth : ∀ u v, P u * P v = if u = v then P u else 0)
    (hSum : ∑ u : ZMod m, P u = 1) (n : ℕ)
    (hWord : ∀ u (σ : Fin n → Fin d),
      P u * Kraus.evalWord A (List.ofFn σ) =
        Kraus.evalWord A (List.ofFn σ) * P (u + n))
    {ψ : NSiteSpace d n} (hψ : ψ ∈ groundSpace A n) :
    ∃ X ∈ cyclicBoundarySpace P n, groundSpaceMap A n X = ψ := by
  obtain ⟨X, rfl⟩ := LinearMap.mem_range.mp hψ
  exact ⟨_, sum_cyclicBoundary_mem P hOrth n X,
    groundSpaceMap_sum_cyclicBoundary A P hOrth hSum n hWord X⟩

/-- The boundary map is injective on a subspace whose adjoints are spanned by words.
The trace pairing tests each difference against its own adjoint.
Source: FNW92, Section 3; Nachtergaele, arXiv:cond-mat/9410110, equation (3.7). -/
theorem groundSpaceMap_injOn_of_adjoint_mem_wordSpan
    (A : MPSTensor d D) (n : ℕ)
    (S : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ))
    (hAdjoint : ∀ X ∈ S, Xᴴ ∈ Kraus.wordSpan A n) :
    Set.InjOn (groundSpaceMap A n) (S : Set (Matrix (Fin D) (Fin D) ℂ)) := by
  intro X hX Y hY hXY
  have hΓ : groundSpaceMap A n (X - Y) = 0 := by
    rw [map_sub, hXY, sub_self]
  have hWord : Kraus.wordSpan A n ≤
      ((Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulRight ℂ (X - Y))).ker := by
    rw [Kraus.wordSpan, Submodule.span_le]
    rintro _ ⟨σ, rfl⟩
    simpa [LinearMap.mem_ker, Matrix.traceLinearMap_apply, groundSpaceMap_apply] using
      congrArg (fun ψ => ψ σ) hΓ
  have hTrace : Matrix.trace ((X - Y)ᴴ * (X - Y)) = 0 :=
    hWord (hAdjoint (X - Y) (S.sub_mem hX hY))
  exact sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hTrace)

/-- Taking the adjoint exchanges boundary and word cyclic degrees.
Source: arXiv:1708.00029, Lemma bdcf. -/
theorem conjTranspose_mem_cyclicMatrixSubspace_of_cyclicBoundary
    (P : ZMod m → Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ u, (P u).IsHermitian) {n : ℕ}
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ cyclicBoundarySpace P n) :
    Xᴴ ∈ cyclicMatrixSubspace P n := by
  intro u
  simpa only [Matrix.conjTranspose_mul, (hP u).eq, (hP (u + n)).eq] using
    (congrArg Matrix.conjTranspose (hX u)).symm

/-- Full spanning of the relevant cyclic degree gives the original one-step
intersection. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.10)--(3.11) and Lemma existenceinteraction. -/
theorem groundSpace_eq_restriction_intersection_of_cyclic_wordSpan [NeZero m]
    (A : MPSTensor d D) (P : ZMod m → Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ u, (P u).IsHermitian)
    (hOrth : ∀ u v, P u * P v = if u = v then P u else 0)
    (hSum : ∑ u : ZMod m, P u = 1)
    (hCycle : ∀ u i, P u * A i = A i * P (u + 1))
    (hLeftCanonical : ∑ i, (A i)ᴴ * A i = 1) {n : ℕ}
    (hSpan : Kraus.wordSpan A n = cyclicMatrixSubspace P n) :
    ((⨅ b : Fin d, (groundSpace A (n + 1)).comap (restrictLastₗ b)) ⊓
      ⨅ a : Fin d, (groundSpace A (n + 1)).comap (restrictFirstₗ a)) =
      groundSpace A (n + 2) := by
  apply groundSpace_eq_restriction_intersection_of_cyclicBoundary A P hCycle hLeftCanonical
  case hInjective =>
    exact groundSpaceMap_injOn_of_adjoint_mem_wordSpan A n _ fun X hX =>
      hSpan.symm ▸ conjTranspose_mem_cyclicMatrixSubspace_of_cyclicBoundary P hP hX
  case hRepresent =>
    exact fun ψ hψ => exists_cyclicBoundary_of_mem_groundSpace A P hOrth hSum (n + 1)
      (fun u σ => by
        simpa only [List.length_ofFn] using
          (evalWord_mem_cyclicMatrixSubspace A P hCycle (List.ofFn σ) u)) hψ

end MPSTensor

