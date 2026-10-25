# The product of compressed site-0 operators in the low-energy example

In `TNLean/Lattice/LowEnergyCommutatorExample.lean`, the example of non-commuting
low-energy terms in Hastings' Appendix B, `compress_siteOp_zero_mul` proved
`P X₀ P · P Y₀ P = P (XY)₀ P` by summing over the ground configurations, which
are parametrized by the spin of site `0`. It now follows from
`QuantumCircuit.siteOp_mul`. The ground projection `P` constrains only the sites
`i ≠ 0`, so it commutes with every operator on site `0`
(`groundProj_commute_siteOp_zero`), and `P² = P` (`groundProj_mul_self`).
The statement of `compress_siteOp_zero_mul` does not change.

## Removed declarations and their replacements

| Removed declaration | Replacement |
|---|---|
| `TNLean.Lattice.LowEnergyExample.sum_isGround` | none needed: its only use was the old proof of `compress_siteOp_zero_mul` |
| `TNLean.Lattice.LowEnergyExample.eq_groundConfig_of_isGround` | none needed: its only use was the proof of `sum_isGround` |

No blueprint `\lean{...}` tag cites either name, and no other use exists in
`TNLean`, `TNLeanTest`, `blueprint`, `docs` or `scripts`.
