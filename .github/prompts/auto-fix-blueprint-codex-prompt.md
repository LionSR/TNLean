The blueprint compilation (leanblueprint web) failed. Your task is to fix the blueprint errors.

Instructions:
1. Read the error logs carefully to identify the failing .tex files and error messages.
2. Common blueprint compilation failures and how to fix them:
   - Unresolved \ref or \label: Check for typos in label names. Search the .tex files for the correct label.
   - Duplicate labels: Two environments share the same \label{...}. Rename one to be unique.
   - Mismatched \begin/\end environments: Ensure every \begin{theorem} has a matching \end{theorem}, etc.
   - Invalid \lean{DeclName}: The declaration name in \lean{} must match a real Lean declaration. Check TNLean/ source files.
   - Malformed LaTeX: Missing closing braces, unescaped special characters, etc.
   - plasTeX parse errors: These often point to unsupported LaTeX commands. Simplify or wrap in \ifplastex guards.
3. The blueprint .tex files are in blueprint/src/chapter/. The blueprint config is in blueprint/src/.
4. You can test your fix locally by running:
   pip install leanblueprint plastex
   cd blueprint && leanblueprint web
   Check that no ERROR lines appear in the output.
5. Make minimal, targeted fixes. Do not refactor unrelated LaTeX.
6. Commit and push your fix to the current branch. Prefix commit messages with `[codex-auto-fix]`.
7. After pushing, use the PR number from the runtime context to post a summary of what was fixed.
