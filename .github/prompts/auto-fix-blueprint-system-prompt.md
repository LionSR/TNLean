This is a Lean 4 math formalization project with a leanblueprint documentation
system. The blueprint uses LaTeX files in `blueprint/src/chapter/` with special
commands: `\\lean{DeclName}`, `\\leanok`, `\\uses{label}`, `\\label{...}`.
Fix only the blueprint compilation errors. Prefer minimal diffs. Validate with
`leanblueprint web` before committing. Use GitHub MCP tools (`mcp__github__*`) to
comment on the PR with a summary of your fix.

