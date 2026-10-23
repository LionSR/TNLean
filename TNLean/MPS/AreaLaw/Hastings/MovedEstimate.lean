/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.GaussianTimeAverage
import TNLean.Algebra.ToEuclideanLinApply

/-!
# The Gaussian time average next to the cut-offs

Step five of the proof of Lemma 1 of Hastings' one-dimensional area law (arXiv:0705.2024v4,
`References/0705.2024/law16.tex`, lines 843–878) multiplies the Gaussian time average
`P_q(M)` of the shifted Hamiltonian on the right by the cut-off product `O_L O_R`, eq.
`moved`. This file records the resulting estimate.

Writing `P₀ = |Ω⟩⟨Ω|` for the ground-state projector, the two sources of error add:
`P_q(M)` differs from `P₀` by the gap bound `e^{-q/2}` and the perturbation
`√q/ΔE · ‖M − H‖` (Theorem `norm_gaussianTimeAverage_sub_groundProjector_le_add`), while
`O_L O_R` moves `Ω` by `‖Ω − O_L O_R Ω‖`. Multiplying `P₀` on the right by `O_L O_R` changes
it, as an operator, by exactly `‖O_L O_R Ω − Ω‖`, because `P₀` is rank one.

## Main results

* `TNLean.MPS.AreaLaw.Hastings.norm_gaussianTimeAverage_mul_mul_sub_groundProjector_le`: for
  Hermitian `M` and `H` with `‖M − H‖ ≤ δ`, a gapped ground vector `Ω` of `H` with energy `0`
  and gap `ΔE > 0`, commuting orthogonal projections `O_L`, `O_R` with
  `‖Ω − O_L O_R Ω‖ ≤ ε`, and every real `q`,
  `‖P_q(M) O_L O_R − |Ω⟩⟨Ω|‖ ≤ e^{-q/2} + √q/ΔE · δ + ε`.

**Local fix (exponent at line 848):** the gap bound keeps the factor `e^{-q/2}`, as in
`GaussianTimeAverage`; see `docs/paper-gaps/hastings07_gaussian_average_exponent.tex`. The
estimate keeps `q`, `δ` and `ε` free. All norms are Euclidean operator norms.

## References

* M. B. Hastings, *An area law for one-dimensional quantum systems*, J. Stat. Mech. (2007)
  P08024, arXiv:0705.2024v4, `law16.tex`, lines 843–878.
-/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.Hastings

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rank-one change of the ground-state projector `P₀ = |Ω⟩⟨Ω|` when it is multiplied on
the right by `O_L O_R`: `‖P₀ O_L O_R − P₀‖ ≤ ‖O_L O_R Ω − Ω‖`. The operator `P₀ (O_L O_R − 1)`
has the same norm as its conjugate transpose `(O_L O_R − 1) P₀`, which sends `ψ` to
`⟪Ω, ψ⟫ (O_L O_R Ω − Ω)`. -/
private theorem norm_groundProjector_mul_sub_le {Ω : EuclideanSpace ℂ n} (hΩ1 : ‖Ω‖ = 1)
    {X : Matrix n n ℂ} (hX : Xᴴ = X) :
    ‖vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) * X -
        vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤ ‖toEuclideanLin X Ω - Ω‖ := by
  have hP₀H : (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))ᴴ =
      vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) := by
    rw [conjTranspose_vecMulVec, star_star]
  rw [← l2_opNorm_conjTranspose]
  have hconj : (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) * X -
      vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))ᴴ =
      X * vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) -
        vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) := by
    rw [conjTranspose_sub, conjTranspose_mul, hX, hP₀H]
  rw [hconj, cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ψ => ?_
  have happly : toEuclideanCLM (n := n) (𝕜 := ℂ)
      (X * vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) -
        vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ψ
      = ⟪Ω, ψ⟫_ℂ • (toEuclideanLin X Ω - Ω) := by
    show toEuclideanLin (X * vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) -
      vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ψ = _
    rw [map_sub, LinearMap.sub_apply, toEuclideanLin_mul_apply,
      toEuclideanLin_vecMulVec_star_self_apply, toEuclideanLin_vecMulVec_star_self_apply,
      map_smul, smul_sub]
  rw [happly, norm_smul]
  calc ‖⟪Ω, ψ⟫_ℂ‖ * ‖toEuclideanLin X Ω - Ω‖
        ≤ (‖Ω‖ * ‖ψ‖) * ‖toEuclideanLin X Ω - Ω‖ := by
          gcongr; exact norm_inner_le_norm (𝕜 := ℂ) Ω ψ
    _ = ‖toEuclideanLin X Ω - Ω‖ * ‖ψ‖ := by rw [hΩ1, one_mul, mul_comm]

/-- **The Gaussian time average next to the cut-offs**, eq. `moved` of Hastings,
arXiv:0705.2024v4, `law16.tex`, lines 843–878. Let `M` and `H` be Hermitian with
`‖M − H‖ ≤ δ`, let `Ω` be a gapped ground vector of `H` with energy `0` and gap `ΔE > 0`, and
let `O_L`, `O_R` be commuting orthogonal projections with `‖Ω − O_L O_R Ω‖ ≤ ε`. Then for
every real `q`,
`‖P_q(M) O_L O_R − |Ω⟩⟨Ω|‖ ≤ e^{-q/2} + √q/ΔE · δ + ε`.
The first two terms bound `‖P_q(M) − |Ω⟩⟨Ω|‖`
(`norm_gaussianTimeAverage_sub_groundProjector_le_add`) times `‖O_L O_R‖ ≤ 1`; the last bounds
the rank-one change `‖|Ω⟩⟨Ω| O_L O_R − |Ω⟩⟨Ω|‖`. -/
theorem norm_gaussianTimeAverage_mul_mul_sub_groundProjector_le {M H : Matrix n n ℂ}
    (hM : M.IsHermitian) (hH : H.IsHermitian) {ΔE : ℝ} {Ω : EuclideanSpace ℂ n}
    (hΩ : IsGappedGroundState H 0 Ω ΔE) (hΔ : 0 < ΔE) {OL OR : Matrix n n ℂ}
    (hOL : IsStarProjection OL) (hOR : IsStarProjection OR) (hcomm : Commute OL OR) (q : ℝ)
    {δ ε : ℝ} (hδ : ‖M - H‖ ≤ δ) (hε : ‖Ω - toEuclideanLin (OL * OR) Ω‖ ≤ ε) :
    ‖gaussianTimeAverage q ΔE M * (OL * OR) -
        vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤
      Real.exp (-q / 2) + Real.sqrt q / ΔE * δ + ε := by
  have hΩ1 : ‖Ω‖ = 1 := hΩ.1
  have hc : (0 : ℝ) ≤ Real.sqrt q / ΔE := div_nonneg (Real.sqrt_nonneg q) hΔ.le
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hδ
  have hXH : (OL * OR)ᴴ = OL * OR := (hOL.mul hOR hcomm).isSelfAdjoint.isHermitian
  -- `‖O_L O_R‖ ≤ 1`, as a product of orthogonal projections.
  have hXnorm : ‖OL * OR‖ ≤ 1 :=
    (norm_mul_le _ _).trans (by nlinarith [hOL.norm_le, hOR.norm_le, norm_nonneg OL])
  -- First term: `‖(P_q(M) − P₀) O_L O_R‖ ≤ (e^{-q/2} + √q/ΔE δ) · 1`.
  have hGP : ‖gaussianTimeAverage q ΔE M -
      vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤
      Real.exp (-q / 2) + Real.sqrt q / ΔE * δ :=
    (norm_gaussianTimeAverage_sub_groundProjector_le_add hM hH hΩ hΔ q).trans
      (add_le_add_left (mul_le_mul_of_nonneg_left hδ hc) _)
  have h0c : 0 ≤ Real.exp (-q / 2) + Real.sqrt q / ΔE * δ :=
    add_nonneg (Real.exp_pos _).le (mul_nonneg hc hδ0)
  have hfirst : ‖(gaussianTimeAverage q ΔE M -
      vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) * (OL * OR)‖ ≤
      Real.exp (-q / 2) + Real.sqrt q / ΔE * δ :=
    (norm_mul_le _ _).trans <| by simpa using mul_le_mul hGP hXnorm (norm_nonneg _) h0c
  -- Second term: `‖P₀ O_L O_R − P₀‖ ≤ ε`, from the rank-one structure of `P₀`.
  have hsecond : ‖vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) * (OL * OR) -
      vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤ ε :=
    (norm_groundProjector_mul_sub_le hΩ1 hXH).trans (by rw [norm_sub_rev]; exact hε)
  -- Combine the two terms.
  have hsplit : gaussianTimeAverage q ΔE M * (OL * OR) -
      vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) =
      (gaussianTimeAverage q ΔE M - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) * (OL * OR) +
        (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) * (OL * OR) -
          vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) := by
    rw [sub_mul]; abel
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

end TNLean.MPS.AreaLaw.Hastings
