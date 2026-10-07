import Mathlib.Tactic.Linter.TextBased

/-! Focused text-style validation of the changed coordinate-unitary modules. -/

open Mathlib.Linter.TextBased

private def modules : Array Lean.Name := #[
  `TNLean.PEPS.AreaLaw,
  `TNLean.PEPS.AreaLaw.RegularizedPatchCoordinate,
  `TNLean.PEPS.AreaLaw.RegularizedPatchStationarity,
  `TNLean.PEPS.AreaLaw.RegularizedPatchMarginal,
  `TNLeanTest.RegularizedPatchStationarity,
  `TNLeanTest.RegularizedPatchMarginal,
  `TNLeanTest.RegularizedPatchZeroWeight]

def main : IO UInt32 := do
  let opts : Lean.Linter.LinterOptions := {
    toOptions := Lean.Options.empty
      |>.setBool `linter.adaptationNote true
      |>.setBool `linter.trailingWhitespace true
      |>.setBool `linter.whitespaceBeforeSemicolon true
      |>.setBool `linter.unicodeLinter true
      |>.setBool `linter.modulesUpperCamelCase true
      |>.setBool `linter.modulesForbiddenWindows true
    linterSets := {} }
  let sourceErrors ← lintModules opts #[] modules .humanReadable false
  let nameErrors ← modulesNotUpperCamelCase opts modules
  let osErrors ← modulesOSForbidden opts modules
  if sourceErrors == 0 && nameErrors == 0 && osErrors == 0 then
    IO.println "PASS: coordinate-unitary text and module names satisfy Mathlib style."
    return 0
  else
    return 1
