# ch14_parent_hamiltonian audit

Workspace: `/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean`
Date: 2026-04-08

## A. `chainGroundSpace_eq_mpvSubmodule` `\lean{}` tag

### Blueprint location
- `blueprint/src/chapter/ch14_parent_hamiltonian.tex:495-503`
  - theorem `\label{thm:chain_ground_space_eq_mpv_blk}`
  - tagged as `\lean{MPSTensor.chainGroundSpace_eq_mpvSubmodule}`

### Actual Lean declaration
- `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:294-296`
```lean
theorem chainGroundSpace_eq_mpvSubmodule {A : MPSTensor d D} [NeZero D]
    (hA : IsInjective A) {L N : ℕ} (hN : 2 ≤ N) (hL : 1 < L) (hLN : L ≤ N) :
    chainGroundSpace A L N = mpvSubmodule A N := by
```

### Finding
- The tagged Lean declaration **exists**, so this is not a nonexistent-name issue.
- But the blueprint theorem does **not** match that declaration.
- The blueprint statement is about **`L₀`-block-injective** tensors with **`L ≥ 2L₀`**.
- The Lean theorem is about **injective** tensors (`IsInjective A`) with hypotheses:
  - `[NeZero D]`
  - `2 ≤ N`
  - `1 < L`
  - `L ≤ N`
- The blueprint theorem also omits the crucial hypothesis `L ≤ N`; it only says `N ≥ 2`, which is too weak because `chainGroundSpace` is defined as `⊤` when `L > N` (`UniqueGroundState.lean:98-103`).

### Exact fix
- Do **not** use `\lean{MPSTensor.chainGroundSpace_eq_mpvSubmodule}` on the current block-injective theorem statement.
- Choose one of these two fixes:
  1. If the blueprint theorem is meant to document the existing Lean theorem, rewrite the theorem statement to the injective version:
     - assume `A` injective;
     - assume `D ≥ 1`;
     - assume `N ≥ 2`, `L ≥ 2`, and `L ≤ N`;
     - conclude `\mathcal G_{N,L}(A) = \operatorname{span}\{V^{(N)}(A)\}`.
  2. If the blueprint theorem is meant to stay block-injective, remove this `\lean{}` tag for now. There is currently **no Lean theorem in these files** whose statement matches the block-injective equality claim.

## B. Martingale criterion and symmetry of `c_{ij}`

### Blueprint location
- Statement: `blueprint/src/chapter/ch14_parent_hamiltonian.tex:753-769`
- Proof: `blueprint/src/chapter/ch14_parent_hamiltonian.tex:772-819`

### Lean comparison
- The only relevant Lean file is `TNLean/MPS/ParentHamiltonian/Martingale.lean:48-66`.
- It contains only the scaffolded final theorem
  `MPSTensor.parentHamiltonian_gapped`; there is **no formal Lean declaration**
  of the abstract martingale criterion with constants `c_{ij}`.

### Finding
- The blueprint theorem statement is missing a symmetry assumption on the constants.
- The proof explicitly needs symmetry:
  - lines `790-799` say that one may symmetrize `c_{ij}` to `\bar c_{ij}`, but also note that this can break the row-sum bound;
  - lines `806-815` then collect coefficients using `c_{ij} = c_{ji}`.
- So the theorem as stated at `761-767` is too weak for the proof that follows.
- This is an **internal blueprint bug**, not a mismatch against a Lean theorem signature, because Lean does not formalize this criterion yet.

### Exact fix
- Strengthen the theorem statement at `761-767` by adding:
  - `c_{ij} = c_{ji}` for every overlapping pair `i,j`.
- A cleaner alternative is to index the constants by unordered pairs `\{i,j\}` instead of ordered pairs.
- If symmetry is not added to the statement, then the proof must be rewritten to show that the chosen symmetrization preserves the row-sum hypothesis. The current proof does not do that.

## C. `gs_eq_bnt_span` conflates two different Lean results

### Blueprint location
- `blueprint/src/chapter/ch14_parent_hamiltonian.tex:971-986`
  - theorem `\label{thm:gs_eq_bnt_span}`
  - tagged with both
    - `\lean{MPSTensor.bnt_mem_groundSpace}`
    - `\lean{MPSTensor.parentHamiltonian_gs_eq_bnt_span}`

### Actual Lean declarations
- Inclusion only:
  - `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean:110-114`
```lean
theorem bnt_mem_groundSpace
    ...
    (j : Fin r) :
    (mpv (A j) : NSiteSpace d N) ∈ parentHamiltonianGroundSpace (μ := μ) A L N := by
```
- Equality:
  - `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean:135-138`
```lean
theorem parentHamiltonian_gs_eq_bnt_span
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N : ℕ} (hL : 1 < L) (hN : N ≥ L + 1) :
    parentHamiltonianGroundSpace (μ := μ) A L N = bntSpan A N := by
```

### Finding
- The blueprint theorem mixes together:
  1. the **one-sided inclusion** `bnt_mem_groundSpace`, and
  2. the **equality** `parentHamiltonian_gs_eq_bnt_span`.
- More importantly, the blueprint statement is about
  `\ker(H_N(A, L_0+1))`, while the Lean equality theorem is about
  `parentHamiltonianGroundSpace (μ := μ) A L N`, where
  `parentHamiltonianGroundSpace` is defined by
  `chainGroundSpace (toTensorFromBlocks μ A) L N`
  (`DegenerateGS.lean:36-44`).
- So the blueprint theorem currently conflates:
  - the chain-ground-space formalization in Lean, and
  - the kernel-of-the-Hamiltonian formulation in prose.
- There is no theorem in the three inspected Lean files identifying this BNT ground space directly with
  `ker(H_N(...))`.

### Exact fix
- If the theorem is meant to correspond to `MPSTensor.parentHamiltonian_gs_eq_bnt_span`, rewrite the blueprint statement to match Lean:
  - state equality with the formal chain-ground-space object, not directly with `\ker(H_N(A,L_0+1))`;
  - use hypotheses `L > 1` and `N ≥ L + 1`;
  - keep `\lean{MPSTensor.parentHamiltonian_gs_eq_bnt_span}`.
- Move `\lean{MPSTensor.bnt_mem_groundSpace}` out of this theorem header unless the theorem is split into a separate inclusion lemma.
- If the blueprint wants to keep the `\ker(H_N(...))` formulation, it needs an additional bridge theorem equating that kernel with the formal `parentHamiltonianGroundSpace`; without that bridge, the current `\lean{}` tags are not exact.

## D. Missing `D ≥ 1` / `[NeZero D]` hypotheses

The following blueprint theorems in ch14 correspond to Lean declarations whose signatures include `[NeZero D]`. To match Lean exactly, each statement should explicitly assume `D ≥ 1` (or equivalent nonzero virtual dimension).

### 1. MPV nonvanishing for block-injective tensors
- Blueprint: `blueprint/src/chapter/ch14_parent_hamiltonian.tex:470-476`
- Lean: `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:218-221`
```lean
theorem mpv_ne_zero_of_isNBlkInjective {A : MPSTensor d D} [NeZero D]
```
- Fix: add `D ≥ 1` to the blueprint theorem statement.

### 2. Chain ground space for block-injective tensors
- Blueprint: `blueprint/src/chapter/ch14_parent_hamiltonian.tex:495-503`
- Lean: `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:294-296`
```lean
theorem chainGroundSpace_eq_mpvSubmodule {A : MPSTensor d D} [NeZero D]
```
- Fix: add `D ≥ 1` if this theorem is rewritten to match the Lean injective theorem.
- Note: this theorem also has the larger mismatch discussed in item A.

### 3. Chain ground space for normal tensors
- Blueprint: `blueprint/src/chapter/ch14_parent_hamiltonian.tex:506-519`
- Lean: `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:357-360`
```lean
theorem chainGroundSpace_eq_mpvSubmodule_normal {A : MPSTensor d D} [NeZero D]
```
- Fix: add `D ≥ 1` to the blueprint theorem statement.

### 4. Unique ground state on the periodic chain
- Blueprint: `blueprint/src/chapter/ch14_parent_hamiltonian.tex:522-530`
- Lean: `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:375-377`
```lean
theorem groundSpace_unique_periodic {A : MPSTensor d D} [NeZero D] ...
```
- Fix: add `D ≥ 1` to the blueprint theorem statement.

### 5. Unique ground state for block-injective tensors
- Blueprint: `blueprint/src/chapter/ch14_parent_hamiltonian.tex:575-581`
- Lean: `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:404-407`
```lean
theorem parentHamiltonian_unique_gs_injective {A : MPSTensor d D} [NeZero D] ...
```
- Fix: add `D ≥ 1` to the blueprint theorem statement.

### 6. Optimal unique ground state for normal tensors
- Blueprint: `blueprint/src/chapter/ch14_parent_hamiltonian.tex:584-590`
- Lean: `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:424-427`
```lean
theorem parentHamiltonian_unique_gs_normal {A : MPSTensor d D} [NeZero D] ...
```
- Fix: add `D ≥ 1` to the blueprint theorem statement.

## Short summary

- A: the `\lean{MPSTensor.chainGroundSpace_eq_mpvSubmodule}` tag names a real theorem, but it is the **injective** equality theorem, not the blueprint's **block-injective** theorem.
- B: the martingale criterion should explicitly assume symmetric `c_{ij}` (or be reformulated with unordered pairs); the current proof uses symmetry.
- C: `thm:gs_eq_bnt_span` mixes an inclusion theorem with an equality theorem and also switches from Lean's `chainGroundSpace` formalization to `\ker(H_N)` without a bridge theorem.
- D: six ch14 theorems should add `D ≥ 1` to match Lean signatures exactly.
