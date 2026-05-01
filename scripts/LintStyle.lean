/-
Copyright (c) 2026 The TNLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic.Linter.TextBased

/-!
# `lake exe lint_style` for TNLean

Invokes Mathlib's `Mathlib.Linter.TextBased.lintModules` on every `.lean` file under
`TNLean/` and on the top-level `TNLean.lean` import surface. Runs the text-based style
linters with their default `LinterOptions`: trailing whitespace, Windows line endings,
space-before-semicolon, disallowed Unicode characters, module naming conventions.

Flags:
* `--github` — emit GitHub problem-matcher annotations
* `--fix`    — apply auto-fixable style errors in place
-/

open Mathlib.Linter.TextBased System

/-- Recursively collect every `.lean` file under `dir` as a `Lean.Name`. -/
partial def collectLeanModules (dir : FilePath) : IO (Array Lean.Name) := do
  let mut acc : Array Lean.Name := #[]
  for entry in (← dir.readDir) do
    let p := entry.path
    if ← p.isDir then
      acc := acc ++ (← collectLeanModules p)
    else if p.extension = some "lean" then
      let parts := (p.withExtension "").components
      acc := acc.push (parts.foldl Lean.Name.mkStr Lean.Name.anonymous)
  return acc

def main (args : List String) : IO UInt32 := do
  let style : ErrorFormat :=
    if args.contains "--github" then ErrorFormat.github else ErrorFormat.humanReadable
  let fix := args.contains "--fix"
  let mut modules ← collectLeanModules "TNLean"
  if ← (FilePath.mk "TNLean.lean").pathExists then
    modules := modules.push `TNLean
  if modules.isEmpty then
    throw <| IO.userError "lint_style: no `.lean` files found under TNLean/ or at TNLean.lean"
  lintModules ({} : LinterOptions) #[] modules style fix
