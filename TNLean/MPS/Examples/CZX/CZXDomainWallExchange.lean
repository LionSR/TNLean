/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.CZX.CZXDomainWalls
import TNLean.MPS.Symmetry.MPOSymmetry.DomainWallExchange

/-!
# CZX: equal domain-wall phases and a string over a pair of walls

**Source.** Garre-Rubio, Schuch 2024 (arXiv:2405.00439), Section III.F,
`Papers/2405.00439/MPU-DW.tex` lines 1660--1672: for the CZX symmetry the double exchange of
domain walls gives `c_{AB} c_{BA} = ω = -1` (`DWstat`), the phases can be chosen
`c_{AB} = c_{BA} = i` (line 1664), so that the exchange of two domain walls is the phase `i`,
and a symmetry string passing over a pair of domain walls acquires `ω` (`signphysop`).

**Formalized here.** With the action tensors of `CZXCompression.czxBlockActionData`, the walls
`e_{AB} = |0⟩` and `e_{BA} = i|1⟩` are exchanged by the generator with `c_{AB} = c_{BA} = i`, and
the local action of the generator on an open chain containing the pair `e_{AB}`, `e_{BA}` is
`-1`. These are the tensor identities behind the semionic statistics of the source; the
truncated string operators and their exchange relation are not constructed.

**Local fix (printed left action vectors):** the explicit walls use the action tensors of
`CZXCompression.czxBlockActionData`, whose left action vectors `⟨1|` and `-⟨0|` replace the vector
`⟨+̂|` printed at lines 1272 and 1300; this affects `czx_isDomainWallAction_semion` and
`czx_domainWall_pair`. Documented in `docs/paper-gaps/gs24_czx_action_left_vectors.tex`.

## Main results

* `CZXCompression.czx_isDomainWallAction_semion`: `c_{AB} = c_{BA} = i`.
* `CZXCompression.czx_domainWall_pair`: a string over the pair acquires `-1`.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

noncomputable section

open scoped Matrix Kronecker
open MPOTensor MPOTensor.GroupFamily

namespace CZXCompression

/-- The domain wall `e_{BA} = i|1⟩` from `|1⟩^{⊗ N}` to `|0⟩^{⊗ N}`, the rescaling
`(1 / i) (-|1⟩)` of `CZXCompression.czxWallBA`. -/
def czxWallBASemion : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ :=
  fun i ↦ (1 / Complex.I) • czxWallBA i

/-- **Equal domain-wall phases for CZX** (arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line
1664: "we can choose `c_{AB} = c_{BA} = i`"): the generator carries `e_{AB} = |0⟩` to
`e_{BA} = i|1⟩` and back, both with phase `i`. -/
theorem czx_isDomainWallAction_semion :
    czxBlockActionData.IsDomainWallAction czxGen czxGen_smul_zero czxGen_smul_one czxWallAB
        czxWallBASemion Complex.I ∧
      czxBlockActionData.IsDomainWallAction czxGen czxGen_smul_one czxGen_smul_zero
        czxWallBASemion czxWallAB Complex.I :=
  BlockActionData.IsDomainWallAction.exists_eq_of_mul_self czx_isDomainWallAction_ab
    czx_isDomainWallAction_ba one_ne_zero (by simp) Complex.I_ne_zero

/-- **A CZX string over a pair of domain walls acquires `-1`** (arXiv:2405.00439, `signphysop`,
`Papers/2405.00439/MPU-DW.tex` lines 1667--1672, with `ω = -1`): the local action of the
generator on an open chain `|0…0⟩ e_{AB} |1…1⟩ e_{BA} |0…0⟩` with long regions is `-1` times the
exchanged chain. -/
theorem czx_domainWall_pair :
    ∃ N : ℕ, ∀ (u v w : List (Fin 2)) (i j : Fin 2), N ≤ u.length → N ≤ v.length →
      N ≤ w.length →
      castIndex czxBlockDim czxGen_smul_zero *
          (czxBlockActionData.V czxGen (Multiplicative.ofAdd 0) *
            (Kraus.evalWord (actTensor (czxFamily.tensor czxGen)
                (czxBlock (Multiplicative.ofAdd 0))) u *
              actRect (czxFamily.tensor czxGen) czxWallAB i *
              Kraus.evalWord (actTensor (czxFamily.tensor czxGen)
                (czxBlock (Multiplicative.ofAdd 1))) v *
              actRect (czxFamily.tensor czxGen) czxWallBA j *
              Kraus.evalWord (actTensor (czxFamily.tensor czxGen)
                (czxBlock (Multiplicative.ofAdd 0))) w) *
            czxBlockActionData.W czxGen (Multiplicative.ofAdd 0)) *
          castIndex czxBlockDim czxGen_smul_zero.symm =
        (-1 : ℂ) • (Kraus.evalWord (czxBlock (Multiplicative.ofAdd 1)) u * czxWallBA i *
          Kraus.evalWord (czxBlock (Multiplicative.ofAdd 0)) v * czxWallAB j *
            Kraus.evalWord (czxBlock (Multiplicative.ofAdd 1)) w) := by
  obtain ⟨N, hN⟩ := BlockActionData.IsDomainWallAction.pair czx_carriesMPV
    czx_isDomainWallAction_ab czx_isDomainWallAction_ba
  exact ⟨N, fun u v w i j hu hv hw ↦ by simpa using hN u v w i j hu hv hw⟩

end CZXCompression
