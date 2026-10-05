/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.GroupCocycleMPO.FusionTensors
import TNLean.MPS.FundamentalTheorem.Reduction.AbsorbingCompression

/-!
# The virtual support projector of the periodic group construction

The periodic tensors of Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3,
`Papers/2203.12563/REsubmission.tex`, lines 2243–2287, satisfy a projected right zipper.
On the stacked bond the projector is the diagonal selector of pairs `(hk, k)`.
Writing `B = T̂_g T̂_h`, its letters satisfy `Bⁱ P = Bⁱ` and
`P Bⁱ = F^> T̂_{gh}ⁱ F^<`. Thus `P Bⁱ F^> = F^> T̂_{gh}ⁱ`, and inserting `P` in the
trace of any nonempty word leaves the trace unchanged. For every nontrivial group and
unit-valued three-cochain, both unprojected right identities fail at some physical letter.

## Main definitions

* `MPOTensor.GroupCocycle.fusionProjector`: the compatible-pair projector `P_{g,h}`;
  it is independent of `g` and of the three-cochain.

## Main statements

* `MPOTensor.GroupCocycle.fusionW_mul_fusionV`: `F^> F^< = P`.
* `MPOTensor.GroupCocycle.fusionProjector_mul_mulTensor`: the projected factorization.
* `MPOTensor.GroupCocycle.fusionProjector_mul_mulTensor_mul_fusionW`: the projected
  right zipper.
* `MPOTensor.GroupCocycle.fusionProjector_mul_evalWord`: the projected factorization
  for all words, including the empty word.
* `MPOTensor.GroupCocycle.trace_fusionProjector_mul_evalWord`: the projector does not
  change nonempty closed-chain contractions.
* `MPOTensor.GroupCocycle.trace_evalWord_mulTensor_eq`: the nonempty closed-chain fusion law.
* `MPOTensor.GroupCocycle.exists_mulTensor_mul_fusionW_ne` and
  `MPOTensor.GroupCocycle.exists_mulTensor_ne_fusionW_mul_tensor_mul_fusionV`:
  failure of the unprojected right identities on every nontrivial group.

## Notation

`V = F^<` reduces a product bond to one bond, and `W = F^>` expands it.
Pairs `(a, b)` are ordered with the `g` bond first and the `h` bond second;
`finProdFinEquiv` identifies them with `Fin (n * n)`.
No new Lean notation is introduced.

## Implementation notes

The projector is a diagonal matrix with entries zero and one. Its definition and support
identities need only a three-cochain with values in `ℂˣ`, not normalization or unit modulus;
the projected factorization and fused trace identity additionally use the cocycle equation.
The nonempty-word condition on right support and trace closure is essential: the empty word
is the identity on the full product bond, which is larger than the projector for nontrivial `G`.

**Local fix (single shift per site):** The tensor uses the single-shift reading of the
source's periodic operator already documented in
`docs/paper-gaps/glm23_pbc_group_mpo_single_shift.tex`.
For a normalized cochain on a nontrivial group, the identity tensor `T̂_e` is not normal
(`MPOTensor.GroupCocycle.not_isNormal_tensor_one`). No normality hypothesis or
normal-representation uniqueness theorem is used here.

## References

* [Garre-Rubio, Lootens, Molnár, *Classifying phases protected by matrix product operator
  symmetries using matrix product states*](https://arxiv.org/abs/2203.12563),
  v3, `Papers/2203.12563/REsubmission.tex`, lines 2243–2287.

## Tags

matrix product operator, periodic boundary conditions, group cohomology, projector, zipper
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace MPOTensor.GroupCocycle

open TNLean.Algebra

variable {G : Type} [Group G] {n : ℕ} (e : G ≃ Fin n)

/-- The projector `P_{g,h}` of arXiv:2203.12563v3, lines 2264–2287: its diagonal component
at `(k', k)` is `δ_{k',hk}`. The matrix is independent of `g` and of the three-cochain. -/
def fusionProjector (h : G) : Matrix (Fin (n * n)) (Fin (n * n)) ℂ :=
  Matrix.diagonal fun p ↦
    if (finProdFinEquiv.symm p).1 = siteShift e h (finProdFinEquiv.symm p).2 then 1 else 0

/-- The product-bond components of the projector printed in arXiv:2203.12563v3,
lines 2264–2286. -/
theorem fusionProjector_apply (h : G) (p q : Fin n × Fin n) :
    fusionProjector e h (finProdFinEquiv p) (finProdFinEquiv q) =
      if p = q then if p.1 = siteShift e h p.2 then 1 else 0 else 0 := by
  simp only [fusionProjector, Matrix.diagonal_apply, Equiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq]

/-- The support selector is idempotent, as asserted at arXiv:2203.12563v3, line 2264. -/
theorem fusionProjector_mul_self (h : G) :
    fusionProjector e h * fusionProjector e h = fusionProjector e h := by
  simp only [fusionProjector, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> simp

/-- The selector in arXiv:2203.12563v3, lines 2264–2286, is an orthogonal projector. -/
theorem fusionProjector_conjTranspose (h : G) :
    (fusionProjector e h)ᴴ = fusionProjector e h := by
  simp only [fusionProjector, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  simp only [Pi.star_apply]
  split_ifs <;> simp

variable {e}

/-- Multiplication by the right fusion tensor selects the compatible outgoing pair.

Source: the compatible pairs in arXiv:2203.12563v3, lines 2264–2286. -/
theorem mul_fusionW_apply {m : ℕ} (ω : ScalarThreeCochain G) (g h : G)
    (M : Matrix (Fin m) (Fin (n * n)) ℂ) (q : Fin m) (r : Fin n) :
    (M * fusionW e ω g h) q r = M q (pairLabel e h r) * (ω g h (e.symm r) : ℂ) := by
  simp [fusionW, Matrix.mul_apply, mul_ite, mul_zero, Finset.sum_ite_eq']

/-- Multiplication on the other side of the right fusion tensor vanishes outside its support.

Source: the compatible pairs in arXiv:2203.12563v3, lines 2264–2286. -/
theorem fusionW_mul_apply {m : ℕ} (ω : ScalarThreeCochain G) (g h : G)
    (M : Matrix (Fin n) (Fin m) ℂ) (p : Fin n × Fin n) (q : Fin m) :
    (fusionW e ω g h * M) (finProdFinEquiv p) q =
      if p.1 = siteShift e h p.2 then (ω g h (e.symm p.2) : ℂ) * M p.2 q else 0 := by
  obtain ⟨a, b⟩ := p
  simp only [Matrix.mul_apply, fusionW, Matrix.of_apply, ite_mul, zero_mul, pairLabel,
    EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hab : a = siteShift e h b
  · simp [hab]
  · simp only [hab, ↓reduceIte]
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    simp only [ite_eq_right_iff, and_imp]
    rintro h1 rfl
    exact absurd h1 hab

variable (e) in
/-- The projector is the reverse product of the two fusion tensors of equation `ftexam`.

Source: arXiv:2203.12563v3, lines 2243–2287. -/
theorem fusionW_mul_fusionV (ω : ScalarThreeCochain G) (g h : G) :
    fusionW e ω g h * fusionV e ω g h = fusionProjector e h := by
  ext p q
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective q
  rw [fusionW_mul_apply, fusionProjector_apply]
  simp only [fusionV, Matrix.of_apply, pairLabel, EmbeddingLike.apply_eq_iff_eq]
  simp only [show q = (siteShift e h p.2, p.2) ↔
    q.1 = siteShift e h p.2 ∧ q.2 = p.2 from Prod.ext_iff]
  by_cases hp : p.1 = siteShift e h p.2
  · by_cases hpq : p = q
    · subst hpq
      simp only [hp, and_self, ↓reduceIte, Units.mul_inv]
    · have hq : ¬ (q.1 = siteShift e h p.2 ∧ q.2 = p.2) := by
        rintro ⟨hq, hq'⟩
        apply hpq
        exact Prod.ext (hp.trans hq.symm) hq'.symm
      simp only [hp, hpq, hq, ↓reduceIte, mul_zero]
  · by_cases hpq : p = q
    · subst hpq
      simp only [hp, ↓reduceIte]
    · simp only [hp, hpq, ↓reduceIte]

variable (e) in
/-- The stacked letter has outgoing bond pair `(hj,j)`; its incoming bond is unrestricted.
This is the component contraction of the two periodic tensors at
arXiv:2203.12563v3, lines 2245–2259. -/
theorem mulTensor_tensor_apply (ω : ScalarThreeCochain G) (g h : G) (i j : Fin n)
    (p q : Fin n × Fin n) :
    mulTensor (tensor e ω g) (tensor e ω h) i j
        (finProdFinEquiv p) (finProdFinEquiv q) =
      (if i = siteShift e g (siteShift e h j) ∧ q.1 = siteShift e h j then
        (ω g (e.symm (siteShift e h j))
          ((e.symm (siteShift e h j))⁻¹ * e.symm p.1) : ℂ) else 0) *
      (if q.2 = j then (ω h (e.symm j) ((e.symm j)⁻¹ * e.symm p.2) : ℂ) else 0) := by
  simp only [mulTensor_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.sum_apply, Matrix.kroneckerMap_apply]
  rw [Finset.sum_eq_single (siteShift e h j)
    (fun k _ hk ↦ by
      have hk' : k ≠ e (h * e.symm j) := by simpa only [siteShift_apply] using hk
      simp [tensor_apply, hk']) (by simp)]
  simp [tensor_apply]

variable (e) in
/-- Every stacked letter is right-supported on the source projector. The side matters:
`B P = B` holds, whereas generally `P B ≠ B`.

Source: the periodic support statement at arXiv:2203.12563v3, line 2287. -/
theorem mulTensor_mul_fusionProjector (ω : ScalarThreeCochain G) (g h : G) (i j : Fin n) :
    mulTensor (tensor e ω g) (tensor e ω h) i j * fusionProjector e h =
      mulTensor (tensor e ω g) (tensor e ω h) i j := by
  ext p q
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective q
  simp only [fusionProjector, Matrix.mul_diagonal, Equiv.symm_apply_apply,
    mulTensor_tensor_apply]
  by_cases hq : q.1 = siteShift e h q.2
  · simp [hq]
  · by_cases hj : q.2 = j
    · simp [hj] at hq
      simp [hj, hq]
    · simp [hj]

/-- The source's modified exact factorization, with the projector on the incoming product
bond: `P_{g,h} (T̂_g T̂_h)^{ij} = F^>_{g,h} T̂_{gh}^{ij} F^<_{g,h}`.

Source: arXiv:2203.12563v3, lines 2243–2263. -/
theorem fusionProjector_mul_mulTensor {ω : ScalarThreeCochain G}
    (hω : ScalarThreeCochain.IsCocycle ω) (g h : G) (i j : Fin n) :
    fusionProjector e h * mulTensor (tensor e ω g) (tensor e ω h) i j =
      fusionW e ω g h * tensor e ω (g * h) i j * fusionV e ω g h := by
  rw [← fusionW_mul_fusionV e ω g h, Matrix.mul_assoc,
    fusionV_mul_mulTensor e hω, ← Matrix.mul_assoc]

/-- The right zipper after projection onto the compatible incoming bond pairs.

Source: arXiv:2203.12563v3, lines 2243–2263, followed by contraction with `F^>`. -/
theorem fusionProjector_mul_mulTensor_mul_fusionW {ω : ScalarThreeCochain G}
    (hω : ScalarThreeCochain.IsCocycle ω) (g h : G) (i j : Fin n) :
    fusionProjector e h * mulTensor (tensor e ω g) (tensor e ω h) i j * fusionW e ω g h =
      fusionW e ω g h * tensor e ω (g * h) i j := by
  rw [fusionProjector_mul_mulTensor hω, Matrix.mul_assoc, fusionV_mul_fusionW, Matrix.mul_one]

/-- The exact factorization extends to every word, with the empty word giving `P = F^>F^<`.

Source: consequence of the projected identity at arXiv:2203.12563v3, lines 2243–2263. -/
theorem fusionProjector_mul_evalWord {ω : ScalarThreeCochain G}
    (hω : ScalarThreeCochain.IsCocycle ω) (g h : G) (w : List (Fin (n * n))) :
    fusionProjector e h *
        Kraus.evalWord (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor w =
      fusionW e ω g h * Kraus.evalWord (tensor e ω (g * h)).toMPSTensor w * fusionV e ω g h := by
  have hw := Kraus.evalWord_intertwine (tensor e ω (g * h)).toMPSTensor
    (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor (fusionV e ω g h)
    (fun ij ↦ (fusionV_mul_mulTensor e hω g h ij.divNat ij.modNat).symm) w
  rw [← fusionW_mul_fusionV e ω g h, Matrix.mul_assoc, ← hw, ← Matrix.mul_assoc]

/-- The outgoing support restriction persists along every nonempty chain.

Source: arXiv:2203.12563v3, line 2287. -/
theorem evalWord_mul_fusionProjector (ω : ScalarThreeCochain G) (g h : G)
    (w : List (Fin (n * n))) (hw : w ≠ []) :
    Kraus.evalWord (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor w *
        fusionProjector e h =
      Kraus.evalWord (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor w := by
  rw [← fusionW_mul_fusionV e ω g h]
  apply Kraus.evalWord_mul_of_right_absorb
    (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor
    (fusionV e ω g h) (fusionW e ω g h) _ w hw
  intro ij
  rw [fusionW_mul_fusionV]
  exact mulTensor_mul_fusionProjector e ω g h ij.divNat ij.modNat

/-- Closing a nonempty chain makes the projector act as the identity: inserting it at the
cut leaves every periodic coefficient unchanged.

Source: arXiv:2203.12563v3, line 2287. -/
theorem trace_fusionProjector_mul_evalWord (ω : ScalarThreeCochain G) (g h : G)
    (w : List (Fin (n * n))) (hw : w ≠ []) :
    Matrix.trace (fusionProjector e h *
        Kraus.evalWord (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor w) =
      Matrix.trace (Kraus.evalWord (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor w) := by
  rw [Matrix.trace_mul_comm, evalWord_mul_fusionProjector ω g h w hw]

/-- The projected factorization and periodic support recover the unprojected closed-chain
fusion law without a normality assumption.

Source: arXiv:2203.12563v3, lines 2243–2287. -/
theorem trace_evalWord_mulTensor_eq {ω : ScalarThreeCochain G}
    (hω : ScalarThreeCochain.IsCocycle ω) (g h : G)
    (w : List (Fin (n * n))) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor w) =
      Matrix.trace (Kraus.evalWord (tensor e ω (g * h)).toMPSTensor w) := by
  rw [← trace_fusionProjector_mul_evalWord ω g h w hw, fusionProjector_mul_evalWord hω,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, fusionV_mul_fusionW, Matrix.one_mul]

/-- On a nontrivial group the unprojected right zipper fails for every unit-valued three-cochain.
An incoming pair `(ha,b)` with `a ≠ b` gives a nonzero component of `B F^>` and a zero
component of `F^> T̂_{gh}`.

Source: arXiv:2203.12563v3, line 2243 (failure of the right zipper). -/
theorem exists_mulTensor_mul_fusionW_ne [Nontrivial G] (ω : ScalarThreeCochain G)
    (g h : G) :
    ∃ i j, mulTensor (tensor e ω g) (tensor e ω h) i j * fusionW e ω g h ≠
      fusionW e ω g h * tensor e ω (g * h) i j := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne G
  have hs : e (h * a) ≠ siteShift e h (e b) := by
    intro hh
    have hh' : h * a = h * b := e.injective (by simpa only
      [siteShift_apply, Equiv.symm_apply_apply] using hh)
    exact hab (mul_left_cancel hh')
  refine ⟨siteShift e g (siteShift e h (e b)), e b, fun hzip ↦ ?_⟩
  have hentry := congrArg (fun M ↦ M (finProdFinEquiv (e (h * a), e b)) (e b)) hzip
  simp only [mul_fusionW_apply, pairLabel, mulTensor_tensor_apply, and_self, ↓reduceIte,
    fusionW_mul_apply, hs] at hentry
  exact (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
    (Units.ne_zero _)) hentry

/-- The unprojected exact factorization also fails on every nontrivial group.

Source: arXiv:2203.12563v3, line 2243 (failure of equation `fusiontensorG`). -/
theorem exists_mulTensor_ne_fusionW_mul_tensor_mul_fusionV [Nontrivial G]
    (ω : ScalarThreeCochain G) (g h : G) :
    ∃ i j, mulTensor (tensor e ω g) (tensor e ω h) i j ≠
      fusionW e ω g h * tensor e ω (g * h) i j * fusionV e ω g h := by
  obtain ⟨i, j, hij⟩ := exists_mulTensor_mul_fusionW_ne (e := e) ω g h
  refine ⟨i, j, fun heq ↦ hij ?_⟩
  rw [heq, Matrix.mul_assoc, fusionV_mul_fusionW, Matrix.mul_one]

end MPOTensor.GroupCocycle
