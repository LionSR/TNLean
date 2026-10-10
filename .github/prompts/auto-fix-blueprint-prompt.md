A blueprint compilation job failed. Your task is to fix the blueprint errors.

Two PR CI jobs build the blueprint. Check which one failed:

- "Check blueprint compiles without errors" builds the web pages with `texra-blueprint web` (plasTeX).
- "Check blueprint PDF compiles" builds the two XeLaTeX print volumes: `leanblueprint pdf`, then `./scripts/build_blueprint_ch01_12.sh` for the FT-MPS volume. XeLaTeX rejects constructs that plasTeX accepts. Typical examples are a bare `_` in text mode, such as a file path inside `\texttt{...}` (write `\_`), and an unbraced subscript after a macro, such as `\spn_\C` (write `\spn_{\C}`). The FT-MPS volume also compiles the `\ifftmpsvolume` branches.

Instructions:

1. Read the error logs carefully to identify the failing `.tex` files and error messages.
2. Common blueprint compilation failures and how to fix them:

   - Unresolved `\ref` or `\label`: check for typos in label names (e.g., `\uses{def:foo}` where the label is `def:bar`). Search the `.tex` files for the correct label.
   - Duplicate labels: two environments share the same `\label{...}`. Rename one to be unique.
   - Mismatched `\begin`/`\end` environments: ensure every `\begin{theorem}` has a matching `\end{theorem}`, etc.
   - Invalid `\lean{DeclName}`: the declaration name in `\lean{}` must match a real Lean declaration. Check `TNLean/` sources for the correct name.
   - Malformed LaTeX: missing closing braces, unescaped special characters, etc.
   - `plasTeX` parse errors: these often indicate unsupported LaTeX commands. Simplify or wrap in `\ifplastex` guards.
   - `ERROR` lines about unresolved references: find the `\uses{}` or `\ref{}` referencing a non-existent label and fix the label name.
3. The blueprint `.tex` files are in `blueprint/src/chapter/`. The blueprint configuration is in `blueprint/src/`.
4. You can test your fix locally by running:

   - `pip install leanblueprint plastex git+https://github.com/LionSR/texra-blueprint@v0.3.8`
   - `cd blueprint && texra-blueprint web`

   Require the command to succeed; it rejects unresolved `ERROR` lines and
   renderer warnings that the Blueprint CI gate treats as failures.
   When the PDF job failed, also run `cd blueprint && leanblueprint pdf`, and
   `./scripts/build_blueprint_ch01_12.sh` if the FT-MPS step failed. Require
   both to succeed.
5. Make minimal, targeted fixes. Do not refactor unrelated LaTeX.
6. Commit and push your fix to the current branch. Prefix commit messages with `[claude-auto-fix]`.
7. After pushing, use the GitHub MCP tools to post a comment on the PR summarizing what was fixed.
