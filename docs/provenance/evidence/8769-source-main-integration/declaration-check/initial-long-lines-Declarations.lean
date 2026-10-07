import TNLean

run_cmd do
  let environment ← Lean.getEnv
  let declarations ← IO.FS.lines "/var/folders/d1/qpfb8kqs3dj482nzfg_0yvkc0000gn/T/tnlean-source-main-blueprint-stziqphq/full-lean-decls.txt"
  let declarations := declarations.filter (fun s ↦ !s.isEmpty)
  let missing := declarations.filter (fun s ↦ !environment.contains s.toName)
  unless missing.isEmpty do
    throwError "Missing declarations: {missing}"
  IO.FS.writeFile "/private/tmp/tnlean-source-main-integration/declaration-check/checked-count.txt" s!"{declarations.size}\n"
