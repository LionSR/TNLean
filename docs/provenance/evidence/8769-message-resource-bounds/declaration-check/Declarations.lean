import TNLean

run_cmd do
  let environment ← Lean.getEnv
  let declarations ← IO.FS.lines "lean_declarations.txt"
  let declarations := declarations.filter (fun s ↦ !s.isEmpty)
  let missing := declarations.filter (fun s ↦ !environment.contains s.toName)
  unless missing.isEmpty do
    throwError "Missing declarations: {missing}"
  IO.FS.writeFile "checked-count.txt" s!"{declarations.size}\n"
