/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.CZX.CZXDomainWalls
import TNLean.MPS.Symmetry.MPOSymmetry.DomainWallStringExchange

/-!
# CZX: domain-wall strings and their semionic exchange

**Source.** Garre-Rubio, Schuch 2024 (arXiv:2405.00439), Sections III.E--III.F,
`Papers/2405.00439/MPU-DW.tex` lines 1365--1425 (the string operators `O^{[i,j]}` with the
endpoint tensors of `eq:defEndT`) and lines 1660--1672: for the CZX symmetry, whose anomaly is
`ω = -1`, two domain-wall strings on sites `i₂ < i₁ < j₁ < j₂` satisfy
`O^{[i₁,j₁]} O^{[i₂,j₂]} |ψ_A⟩ = c_{AB} c_{BA} O^{[i₂,j₂]} O^{[i₁,j₁]} |ψ_A⟩` with
`c_{AB} c_{BA} = ω = -1` (`signphysop`), the semionic statistics of the domain walls.

**Formalized here.** For the CZX representation acting on the product states `|0⟩^{⊗ N}` and
`|1⟩^{⊗ N}`, with the action tensors of `CZXCompression.czxBlockActionData`, the domain walls
`e_{AB} = |0⟩`, `e_{BA} = -|1⟩`, and the left inverses `⟨0|` and `⟨1|` of the two product
states, the string operator creates the state with two domain walls on `|0⟩^{⊗ N}`, and two
strings on sites `i₂ < i₁ < j₁ < j₂` anticommute on `|0⟩^{⊗ N}` when the regions between the
walls are long.

**Local fix (printed left action vectors):** the action tensors of
`CZXCompression.czxBlockActionData` have the left action vectors `⟨1|` and `-⟨0|` in place of
the vector `⟨+̂|` printed at lines 1272 and 1300; documented in
`docs/paper-gaps/gs24_czx_action_left_vectors.tex`.

**Local fix (nondegenerate domain walls, blocked local action):**
`CZXCompression.czx_wallString_exchange` rests on `IsDomainWallAction`, whose local relation
holds against regions longer than a buffer; documented in
`docs/paper-gaps/gs24_domain_wall_nondegenerate.tex`.

## Main results

* `CZXCompression.czx_isSeparatingLeftInverse`: `⟨0|` and `⟨1|` are left inverses of the two
  product states with separated supports.
* `CZXCompression.czx_wallString_mulVec_mpv`: `O^{[i,j]} |0…0⟩ = |ψ(0-1-0)⟩`.
* `CZXCompression.czx_wallString_exchange`: the two orders of the strings differ by `-1`.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

noncomputable section

open scoped Matrix Kronecker
open MPOTensor MPOTensor.GroupFamily

namespace CZXCompression

local notation "x₀" => (Multiplicative.ofAdd (0 : Fin 2) : Multiplicative (Fin 2))
local notation "x₁" => (Multiplicative.ofAdd (1 : Fin 2) : Multiplicative (Fin 2))

/-- **Left inverses of the CZX product states** (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` lines 1422--1425): the one-site tensors `⟨0|` and `⟨1|` of the
product states are left inverses of `|0⟩` and `|1⟩` with separated supports. -/
theorem czx_isSeparatingLeftInverse :
    IsSeparatingLeftInverse (czxBlock x₀) (czxBlock x₁) (czxBlock x₀) (czxBlock x₁) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext ⟨α, β⟩ ⟨γ, δ⟩
    fin_cases α; fin_cases β; fin_cases γ; fin_cases δ
    simp [physPairing, czxBlock, MPSTensor.ghzSectorTensor, Fin.sum_univ_two]

/-- The CZX domain-wall string `O^{[i,j]}` with endpoints at the sites `k` and `k + 1 + l` of the
periodic chain of `L` sites. -/
abbrev czxWallString {L : ℕ} (k l n : ℕ) (h : k + 1 + l + 1 + n = L) :
    Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ :=
  czxBlockActionData.wallString czxGen czxGen_smul_zero czxGen_smul_one (czxBlock x₀)
    (czxBlock x₁) czxWallAB czxWallBA k l n h

/-- **A CZX string creates two domain walls** (arXiv:2405.00439, `eq:DWophys`,
`Papers/2405.00439/MPU-DW.tex` lines 1365--1388): on `|0⟩^{⊗ L}` the string creates the state
with the domain wall `e_{AB}` at its left end and `e_{BA}` at its right end. -/
theorem czx_wallString_mulVec_mpv {k l n L : ℕ} (h : k + 1 + l + 1 + n = L) :
    czxWallString k l n h *ᵥ (fun σ ↦ MPSTensor.mpv (czxBlock x₀) σ) =
      fun τ ↦ twoWallMPV (czxBlock x₀) czxWallAB (czxBlock x₁) czxWallBA (τ ∘ Fin.cast h) :=
  czxBlockActionData.wallString_mulVec_mpv_left czx_isSeparatingLeftInverse h

/-- **Semionic exchange of CZX domain-wall strings** (arXiv:2405.00439, `signphysop`,
`Papers/2405.00439/MPU-DW.tex` lines 1660--1672, with `ω = -1`): for strings on sites
`i₂ < i₁ < j₁ < j₂`, `O^{[i₁,j₁]} O^{[i₂,j₂]} |0…0⟩ = -O^{[i₂,j₂]} O^{[i₁,j₁]} |0…0⟩` whenever the
three regions between the walls are longer than a fixed buffer. -/
theorem czx_wallString_exchange :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
      (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L), N ≤ u' → N ≤ v → N ≤ w' →
      (czxWallString (u + 1 + u') v (w' + 1 + w) h₁ * czxWallString u (u' + 1 + v + 1 + w') w h₂) *ᵥ
          (fun σ ↦ MPSTensor.mpv (czxBlock x₀) σ) =
        (-1 : ℂ) • ((czxWallString u (u' + 1 + v + 1 + w') w h₂ *
          czxWallString (u + 1 + u') v (w' + 1 + w) h₁) *ᵥ
            (fun σ ↦ MPSTensor.mpv (czxBlock x₀) σ)) := by
  obtain ⟨N, hN⟩ := czxBlockActionData.wallString_mul_wallString_mulVec_mpv czx_carriesMPV
    czx_isSeparatingLeftInverse czx_isDomainWallAction_ab czx_isDomainWallAction_ba
  refine ⟨N, fun u u' v w' w L h₁ h₂ hu' hv hw' ↦ ?_⟩
  rw [hN u u' v w' w L h₁ h₂ hu' hv hw', smul_smul]
  norm_num

end CZXCompression
