# ch08/ch09 audit

Scope checked:
- `blueprint/src/chapter/ch08_canonical.tex`
- `blueprint/src/chapter/ch09_block_perm.tex`
- `TNLean/MPS/CanonicalForm/`
- `TNLean/PiAlgebra/`

Quick status:
- All tagged declarations resolve in Lean (`92/92` from these two chapters).
- I did not find a missing declaration that should be `\notready`.
- The relevant `TNLean/MPS/CanonicalForm` and `TNLean/PiAlgebra` files appear sorry-free; `\leanok` is broadly fine.

## Issues

1. `ch08` overstates `MPSTensor.exists_twoBlock_decomp_of_posSemidef_fixedPoint_strict`.
   - Blueprint: [blueprint/src/chapter/ch08_canonical.tex](/Users/siruilu/Library/Mobile%20Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/blueprint/src/chapter/ch08_canonical.tex):232 says "`A` is unitarily equivalent to a two-block upper-triangular tensor", then separately says the diagonal truncation has the same MPV.
   - Lean only gives existence of smaller blocks `A₁ A₂` with `SameMPV₂ A (twoBlockTensor A₁ A₂)`, i.e. direct MPV-equivalence to the block-diagonal tensor. See `TNLean/MPS/Irreducible/FixedPointProjection.lean:535`.
   - Suggested fix: move the unitary/upper-triangular discussion into the proof sketch and state the theorem directly as existence of a two-block decomposition with the same MPV family.

2. `ch08` overstates `MPSTensor.exists_irreducible_blockDecomp`.
   - Blueprint: [blueprint/src/chapter/ch08_canonical.tex](/Users/siruilu/Library/Mobile%20Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/blueprint/src/chapter/ch08_canonical.tex):272 says the decomposition is "up to unitary equivalence".
   - Lean states only `SameMPV₂ A (toTensorFromBlocks (fun _ => 1) blocks)` with irreducible blocks. See `TNLean/MPS/CanonicalForm/Reduction.lean:106`.
   - Suggested fix: drop "up to unitary equivalence" from the theorem statement.

3. `ch08` `MPSTensor.exists_irreducible_blockDecomp_with_CFII` has an editorial glitch.
   - Blueprint: [blueprint/src/chapter/ch08_canonical.tex](/Users/siruilu/Library/Mobile%20Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/blueprint/src/chapter/ch08_canonical.tex):753 is a sentence fragment: "The conclusion is the left-canonical normalization; the remaining reduction to normal canonical form."
   - Lean-side content is fine; this just reads unfinished.

4. `ch08` seriously compresses `MPSTensor.exists_irreducible_blockDecomp_with_tpGauge` past what Lean actually says.
   - Blueprint: [blueprint/src/chapter/ch08_canonical.tex](/Users/siruilu/Library/Mobile%20Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/blueprint/src/chapter/ch08_canonical.tex):1457 says: "After removing a trivial block, one obtains a block decomposition into irreducible blocks with a trace-preserving gauge."
   - Lean theorem is more conditional: from an irreducible block decomposition, each block with a nonzero Kraus operator admits a TP-gauge representative; zero blocks cannot just be dropped because `SameMPV₂` remembers the `N = 0` sector. See `TNLean/MPS/CanonicalForm/Existence.lean:306`.
   - Suggested fix: mention the nonzero-Kraus side condition explicitly, or rewrite this as a continuation theorem rather than a global decomposition theorem.

5. `ch09` omits nonzero-dimension assumptions on several declarations.
   - Affected tags:
     - `MPSTensor.dim_preserved`
     - `MPSTensor.algEquiv_pi_matrix_decomposition`
     - `MPSTensor.piAlgEquiv`
     - `MPSTensor.piAlgEquiv_decomposition`
   - Blueprint locations: [blueprint/src/chapter/ch09_block_perm.tex](/Users/siruilu/Library/Mobile%20Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/blueprint/src/chapter/ch09_block_perm.tex):49, :66, :110, :122.
   - Lean requires `[∀ k, NeZero (D k)]` / `[∀ k, NeZero (dim k)]` for these declarations. See `TNLean/MPS/Structure/BlockPermutation.lean:232`, `TNLean/MPS/Structure/BlockPermutation.lean:257`, and `TNLean/PiAlgebra/Construction.lean:184`, `TNLean/PiAlgebra/Construction.lean:222`.
   - Suggested fix: add "positive bond dimensions" (or equivalent nonzero-size hypothesis) where these declarations are stated.

6. `ch09` proof text for `MPSTensor.piAlgEquiv_decomposition` claims more than the tagged theorem states.
   - Blueprint: [blueprint/src/chapter/ch09_block_perm.tex](/Users/siruilu/Library/Mobile%20Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/blueprint/src/chapter/ch09_block_perm.tex):146-149 says the permutation is actually `id`.
   - Lean theorem `piAlgEquiv_decomposition` only returns some permutation/decomposition witness; it does not expose a specialized `σ = id` conclusion under that name. See `TNLean/PiAlgebra/Construction.lean:222`.
   - This may still be mathematically true from the construction, but the blueprint should not present it as what the tagged theorem itself says unless a dedicated lemma is cited.
