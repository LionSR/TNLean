/-
Copyright (c) 2026 The TNLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lake.CLI.Main
import Mathlib.Tactic.Linter.TextBased

/-!
# `lake exe lint_style` for TNLean

Invokes Mathlib's `Mathlib.Linter.TextBased.lintModules` on every `.lean` file under
`TNLean/` and on the top-level `TNLean.lean` import surface. Runs the text-based style
linters with the project's Lake linter options: trailing whitespace, Windows line
endings, space-before-semicolon, disallowed Unicode characters, and module naming
conventions.

Flags:
* `--github` — emit GitHub problem-matcher annotations
* `--fix`    — apply auto-fixable style errors in place
-/

open Mathlib.Linter.TextBased System
open Lean.Linter

section LinterSetsElab

open Lean

instance [ToExpr α] : ToExpr (NameMap α) where
  toExpr s := mkApp4 (.const ``Std.TreeMap.ofArray [.zero, .zero])
    (toTypeExpr Name) (toTypeExpr α)
    (toExpr s.toArray)
    (.const ``Lean.Name.quickCmp [])
  toTypeExpr := .const ``LinterSets []

instance : ToExpr LinterSets := inferInstanceAs <| ToExpr (NameMap _)

/-- Return the linter sets defined when this executable is elaborated. -/
elab "linter_sets%" : term => do
  return toExpr <| linterSetsExt.getState (← getEnv)

end LinterSetsElab

/-- Convert Lake's Lean options into `Lean.Options`, stripping `weak.` like Lean does. -/
def toLeanOptions (opts : Lean.LeanOptions) : Lean.Options := Id.run do
  let mut out := Lean.Options.empty
  for ⟨name, value⟩ in opts.values do
    if name.getRoot == `weak then
      out := out.insert (name.replacePrefix `weak Lean.Name.anonymous) value.toDataValue
    else
      out := out.insert name value.toDataValue
  return out

/-- Get the root package of the Lake workspace we are running in. -/
def getWorkspaceRoot : IO Lake.Package := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← Lake.findInstall?
  let config ← Lake.MonadError.runEIO <|
    Lake.mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some workspace ← Lake.loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "failed to load Lake workspace"
  return workspace.root

/-- Determine the Lean options configured by the current Lake project. -/
def getLakefileLeanOptions : IO Lean.Options := do
  let root ← getWorkspaceRoot
  let rootOpts := root.leanOptions
  let defaultOpts := root.defaultTargets.flatMap fun target ↦
    if let some lib := root.findLeanLib? target then
      lib.config.leanOptions
    else if let some exe := root.findLeanExe? target then
      exe.config.leanOptions
    else
      #[]
  return toLeanOptions (rootOpts.appendArray defaultOpts)

/-- Build linter options from Lake's project options and the elaborated linter-set table. -/
def getProjectLinterOptions : IO Lean.Linter.LinterOptions := do
  return {
    toOptions := ← getLakefileLeanOptions
    linterSets := linter_sets%
  }

/-- Read committed text-linter exceptions for pre-existing source-tree issues. -/
def readStyleExceptions : IO (Array String) := do
  let path := FilePath.mk "scripts/nolints-style.txt"
  if ← path.pathExists then
    return (← IO.FS.readFile path).splitOn "\n" |>.toArray
  else
    return #[]

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
  let opts ← getProjectLinterOptions
  let nolints ← readStyleExceptions
  lintModules opts nolints modules style fix
