#!/usr/bin/env python3
"""Unit tests for Blueprint Lean-declaration source scanning."""

import json
import os
import subprocess
from unittest.mock import patch
from pathlib import Path
from tempfile import TemporaryDirectory

from blueprint_lean_sync import (
    AdditiveRules,
    _resolve_dependency_lean_root,
    _dependency_fetch_enabled,
    _fetch_dependency_sources,
    _verified_dependency,
    _native_additive_rules,
    collect_lean_decls,
    BlueprintEntry,
    collect_file_lean_decls,
    find_duplicate_lean_tags,
    run_sync,
    split_tex_lean_decls,
)


def commit_fixture(root: Path) -> str:
    subprocess.run(["git", "init", "-q", str(root)], check=True)
    subprocess.run(["git", "-C", str(root), "add", "."], check=True)
    subprocess.run(["git", "-C", str(root), "-c", "user.name=Test", "-c",
                    "user.email=test@example.invalid", "commit", "-qm", "fixture"], check=True)
    return subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()


def test_split_tex_lean_decls_handles_continuations_and_top_level_commas() -> None:
    assert split_tex_lean_decls(
        r"""
Foo.%
  bar (x, y), Baz.qux [a, b], Quux.{u}
"""
    ) == ["Foo.bar (x, y)", "Baz.qux [a, b]", "Quux.{u}"]


def test_structure_fields_are_declarations() -> None:
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        lean_root = root / "TNLean"
        lean_root.mkdir()
        source = lean_root / "Example.lean"
        source.write_text(
            """namespace Example

structure Witness where
  /-- A colon in prose: this is not a field. -/
  /- An outer comment
    /- with a nested comment -/
    fake : Nat
  -/
  value : Nat
  relation (x : Nat) : x = value
  withLocalBinder :
    ∀ (n : Nat),
      letI : NeZero (n + 1) := ⟨by omega⟩
      True

structure InlineDoc where
  /-- Documentation on the first field. -/ first : Nat
  second : Nat

 theorem after : True := by trivial

end Example
"""
        )
        decls = {decl.fqn: decl for decl in collect_file_lean_decls(source, lean_root)}
        assert "Example.Witness" in decls
        assert decls["Example.Witness.value"].kind == "field"
        assert decls["Example.Witness.relation"].kind == "field"
        assert decls["Example.Witness.withLocalBinder"].kind == "field"
        assert "Example.Witness.letI" not in decls
        assert "Example.Witness.this" not in decls
        assert "Example.Witness.fake" not in decls
        assert decls["Example.InlineDoc.first"].kind == "field"
        assert decls["Example.InlineDoc.second"].kind == "field"
        assert "Example.after" in decls


def test_root_prefixed_decls_escape_namespace() -> None:
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        lean_root = root / "TNLean"
        lean_root.mkdir()
        source = lean_root / "Example.lean"
        source.write_text(
            """namespace Owner

theorem _root_.Other.Thing.escaped : True := by trivial

theorem local_decl : True := by trivial

end Owner
"""
        )
        decls = {decl.fqn: decl for decl in collect_file_lean_decls(source, lean_root)}
        # `_root_.` re-qualifies the declaration away from the enclosing
        # namespace: the fully-qualified name is the remainder, not
        # `Owner._root_.…`.
        assert "Other.Thing.escaped" in decls
        assert "Owner._root_.Other.Thing.escaped" not in decls
        assert "Owner.local_decl" in decls


def test_duplicate_lean_tags_are_reported_once_per_declaration() -> None:
    def entry(file: str, line: int, decl: str) -> BlueprintEntry:
        return BlueprintEntry(
            file=file,
            line=line,
            env_type="lean-tag",
            label=None,
            lean_decl=decl,
            has_leanok=False,
            proof_has_leanok=False,
        )

    refs = [
        entry("src/chapter/ch01.tex", 3, "Owner.decl"),
        entry("src/chapter/ch02.tex", 7, "Owner.decl"),
        entry("src/chapter/ch01.tex", 9, "Unique.decl"),
    ]
    duplicates = find_duplicate_lean_tags(refs)
    assert [decl for decl, _ in duplicates] == ["Owner.decl"]
    assert [(e.file, e.line) for e in duplicates[0][1]] == [
        ("src/chapter/ch01.tex", 3),
        ("src/chapter/ch02.tex", 7),
    ]
    assert find_duplicate_lean_tags(refs[1:]) == []


def test_sync_resolves_mathlib_and_qiclean_without_local_wrappers() -> None:
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "TNLean").mkdir()
        (root / "TNLean" / "Example.lean").write_text(
            "theorem Owner.shared : True := by trivial\n"
        )
        blueprint_src = root / "blueprint" / "src"
        (blueprint_src / "chapter").mkdir(parents=True)
        chapter = blueprint_src / "chapter" / "example.tex"
        chapter.write_text(
            r"\begin{definition}" "\n"
            r"\lean{groupCohomology.IsMulCocycle₂}\leanok" "\n"
            r"\end{definition}" "\n"
            r"\begin{theorem}" "\n"
            r"\lean{QICLean.result}\leanok" "\n"
            r"\end{theorem}" "\n"
        )
        (root / "lake-manifest.json").write_text(json.dumps({
            "packagesDir": ".lake/packages",
            "packages": [{"name": "qiclean"}, {"name": "mathlib"}],
        }))
        # Mathlib uses a Lean lakefile and a capitalized library directory;
        # QICLean declares its library through lakefile.toml.
        mathlib = root / ".lake" / "packages" / "mathlib"
        (mathlib / "Mathlib").mkdir(parents=True)
        (mathlib / "lakefile.lean").write_text("lean_lib Mathlib\n")
        (mathlib / "Mathlib" / "LowDegree.lean").write_text(
            "namespace groupCohomology\n"
            "def IsMulCocycle₂ : Prop := True\n"
            "end groupCohomology\n"
            "def Owner.shared : Prop := True\n"
        )
        qiclean = root / ".lake" / "packages" / "qiclean"
        (qiclean / "QICLean").mkdir(parents=True)
        (qiclean / "lakefile.toml").write_text('[[lean_lib]]\nname = "QICLean"\n')
        (qiclean / "QICLean" / "Result.lean").write_text(
            "theorem QICLean.result : True := by trivial\n"
        )

        packages = [{"name": name, "type": "git", "rev": commit_fixture(directory)}
                    for name, directory in [("mathlib", mathlib), ("qiclean", qiclean)]]
        (root / "lake-manifest.json").write_text(json.dumps({"packages": packages}))
        report = run_sync(root)
        assert report.ok
        assert len(report.blueprint_entries) == 2
        assert report.lean_decls["groupCohomology.IsMulCocycle₂"].file == "Mathlib/LowDegree.lean"
        assert report.lean_decls["QICLean.result"].file == "QICLean/Result.lean"
        assert report.lean_decls["Owner.shared"].file == "TNLean/Example.lean"

        # An upstream namespace is not a blanket allowlist: misspelled names fail.
        chapter.write_text(chapter.read_text().replace("IsMulCocycle₂", "IsMulCocycleTypo"))
        report = run_sync(root)
        assert not report.ok
        assert len(report.leanok_but_missing) == 1
        assert [entry.lean_decl for entry in report.missing_in_lean] == [
            "groupCohomology.IsMulCocycleTypo"
        ]


def test_dependency_rejects_unverified_sources() -> None:
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        package = root / ".lake/packages/mathlib"
        lib = package / "Mathlib"
        lib.mkdir(parents=True)
        source = lib / "Example.lean"
        source.write_text("theorem Native.good : True := by trivial\n")
        rev = commit_fixture(package)
        manifest = {"packages": [{"name": "mathlib", "type": "git", "rev": rev}]}
        path = root / "lake-manifest.json"
        path.write_text(json.dumps(manifest))
        assert _resolve_dependency_lean_root(root, "mathlib") == lib
        assert _resolve_dependency_lean_root(root, "arbitrary") is None
        source.write_text("theorem Native.changed : True := by trivial\n")
        assert _resolve_dependency_lean_root(root, "mathlib") is None
        subprocess.run(["git", "-C", str(package), "checkout", "--", "."], check=True)
        extra = lib / "Untracked.lean"
        extra.write_text("theorem Native.extra : True := by trivial\n")
        assert _resolve_dependency_lean_root(root, "mathlib") is None
        extra.unlink()
        for bad in ["0" * 40, "main", "v4.36.0-rc1"]:
            manifest["packages"][0]["rev"] = bad
            path.write_text(json.dumps(manifest))
            assert _resolve_dependency_lean_root(root, "mathlib") is None
        manifest["packages"][0]["rev"] = rev
        path.write_text(json.dumps(manifest))
        # A directory nested inside another Git repo is not its own checkout.
        (package / ".git").rename(root / ".git")
        assert _resolve_dependency_lean_root(root, "mathlib") is None
        with patch.dict(os.environ, {"GITHUB_ACTIONS": "true", "BLUEPRINT_SYNC_FETCH_DEPS": "0"}):
            assert not _dependency_fetch_enabled()
        with patch.dict(os.environ, {"BLUEPRINT_SYNC_FETCH_DEPS": "1"}):
            assert _dependency_fetch_enabled()


def test_generated_names_are_attached_exact_and_conservative() -> None:
    with TemporaryDirectory() as tmp:
        root = Path(tmp) / "Mathlib"
        root.mkdir()
        source = root / "Example.lean"
        source.write_text('''namespace Finset
@[to_additive /-- Sum documentation with an embedded @[fake]. -/]
theorem prod_congr_set : True := by trivial
@[to_additive renamed_sum]
theorem prod_renamed : True := by trivial
@[to_additive _root_.Outside.explicit]
theorem prod_root : True := by trivial
@[to_additive Other.explicit]
theorem prod_other : True := by trivial
@[to_additive]
private theorem prod_private : True := by trivial
-- @[to_additive] theorem prod_commented : True := by trivial
/- outer /- @[to_additive] theorem prod_nested : True := by trivial -/ -/
def string := "
@[to_additive] theorem prod_string : True := by trivial
"
@[to_additive "invalid"] theorem prod_invalid : True := by trivial
theorem prod_unannotated : True := by trivial
@[to_additive self] theorem prod_self : True := by trivial
@[to_additive none] theorem prod_none : True := by trivial
@[to_additive existing sum_existing] theorem prod_existing : True := by trivial
@[to_additive (attr := simp)] theorem prod_option : True := by trivial
@[to_additive] theorem prodCamelCase : True := by trivial
end Finset
namespace Outer
@[to_additive] theorem _root_.Root.prod_escape : True := by trivial
end Outer
''')
        rules = AdditiveRules({"prod": ["Sum"], "mul": ["Add"]}, {"addsupport"})
        decls = collect_lean_decls(root, additive_rules=rules)
        for name in ["Finset.sum_congr_set", "Finset.renamed_sum", "Outside.explicit",
                     "Other.explicit", "Root.sum_escape"]:
            assert name in decls, name
        for name in ["sum_congr_set", "Wrong.sum_congr_set", "Finset.sum_congr_typo",
                     "Finset.sum_private", "Finset.prod_private", "Finset.sum_commented",
                     "Finset.prod_commented", "Finset.sum_nested", "Finset.sum_string",
                     "Finset.prod_string", "Finset.sum_invalid", "Finset.sum_unannotated",
                     "Finset.sum_self", "Finset.sum_none", "Finset.sum_existing",
                     "Finset.sum_option", "Finset.sumCamelCase", "Outer.Root.sum_escape"]:
            assert name not in decls, name
        # A registered namespace translation is unsupported, not guessed.
        source.write_text("insert_to_additive_translation Finset Other\n" + source.read_text())
        decls = collect_lean_decls(root, additive_rules=AdditiveRules({"prod": ["Sum"]}, set()))
        assert "Finset.sum_congr_set" not in decls
        assert "Outside.explicit" in decls


def test_tracked_only_and_exact_namespace() -> None:
    with TemporaryDirectory() as tmp:
        package = Path(tmp)
        root = package / "Mathlib"
        root.mkdir()
        (root / "Example.lean").write_text(
            "namespace Outer\ntheorem Inner.result : True := by trivial\nend Outer\n")
        (package / ".gitignore").write_text("Mathlib/Scratch.lean\n")
        commit_fixture(package)
        (root / "Scratch.lean").write_text("theorem Bogus.ignored : True := by trivial\n")
        (root / "Untracked.lean").write_text("theorem Bogus.result : True := by trivial\n")
        decls = collect_lean_decls(root, tracked_only=True)
        assert "Outer.Inner.result" in decls
        assert "Inner.result" not in decls
        assert "Bogus.result" not in decls
        assert "Bogus.ignored" not in decls


def test_native_dictionary_loading_and_ambiguous_forms() -> None:
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        target = root / "Tactic/Translate/ToAdditive.lean"
        target.parent.mkdir(parents=True)
        target.write_text('''def nameDict : Map := .ofList [
  ("prod", ["Sum"]), ("mul", ["Add"]), ("group", ["Add", "Group"])]
def abbreviationDict : Map := .ofList [("addSupport", "Support")]
initialize guessNameExt
''')
        rules = _native_additive_rules(root)
        assert rules is not None and rules.words["prod"] == ["Sum"]
        source = root / "Example.lean"
        source.write_text('''namespace Native
@[to_additive] theorem prod_congr_set : True := by trivial
@[to_additive] theorem mul_support : True := by trivial
@[to_additive] theorem group_result : True := by trivial
@[to_additive] private structure Hidden where
  field : Nat
end Native
''')
        decls = collect_lean_decls(root, additive_rules=rules)
        assert "Native.sum_congr_set" in decls
        assert "Native.add_support" not in decls
        assert "Native.add_group_result" not in decls
        assert "Native.Hidden.field" not in decls
        source.write_text("to_additive_name_hint Prod Unexpected\n" + source.read_text())
        decls = collect_lean_decls(root, additive_rules=_native_additive_rules(root))
        assert "Native.sum_congr_set" not in decls
        target.unlink()
        assert _native_additive_rules(root) is None


def test_exact_fetch_stages_without_branch_fallback() -> None:
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        source = root / "source"
        source.mkdir()
        (source / "fixture").write_text("original")
        rev = commit_fixture(source)
        destination = root / "packages/mathlib"
        assert _fetch_dependency_sources(destination, source.as_uri(), rev)
        assert subprocess.check_output(
            ["git", "-C", str(destination), "rev-parse", "HEAD"], text=True).strip() == rev
        (destination / "fixture").write_text("preserved local edit")
        assert not _fetch_dependency_sources(destination, source.as_uri(), rev)
        assert (destination / "fixture").read_text() == "preserved local edit"
        absent = root / "packages/missing"
        assert not _fetch_dependency_sources(absent, source.as_uri(), "0" * 40)
        assert not absent.exists()
        assert not _fetch_dependency_sources(absent, source.as_uri(), "main")


def test_dependency_rejects_unsupported_layouts() -> None:
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        package = root / ".lake/packages/mathlib"
        lib = package / "Mathlib"
        lib.mkdir(parents=True)
        (lib / "Example.lean").write_text("theorem Native.good : True := by trivial\n")
        rev = commit_fixture(package)
        entry = {"name": "mathlib", "type": "git", "rev": rev}
        manifest = {"packages": [entry]}
        path = root / "lake-manifest.json"
        # These first two layouts resolve to the real clean fixture, but must
        # still be rejected rather than silently accepting another layout.
        for directory in [str(package.parent), ".lake/../.lake/packages",
                          "../packages", "", None, [], 7]:
            manifest["packagesDir"] = directory
            path.write_text(json.dumps(manifest))
            assert _resolve_dependency_lean_root(root, "mathlib") is None
        manifest["packagesDir"] = ".lake/packages"
        for subdir in ["Mathlib", ".", "../other", [], 7]:
            entry["subDir"] = subdir
            path.write_text(json.dumps(manifest))
            assert _resolve_dependency_lean_root(root, "mathlib") is None
        for subdir in [None, ""]:
            entry["subDir"] = subdir
            path.write_text(json.dumps(manifest))
            assert _resolve_dependency_lean_root(root, "mathlib") == lib


def test_fetch_preserves_destination_appearing_during_verification() -> None:
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        source = root / "source"
        source.mkdir()
        (source / "fixture").write_text("original")
        rev = commit_fixture(source)
        for symlink in [False, True]:
            destination = root / "packages" / ("link" if symlink else "directory")
            appeared = []

            def verify_and_create_destination(staged: Path, commit: str) -> bool:
                assert _verified_dependency(staged, commit)
                if symlink:
                    destination.symlink_to(root / "missing-target", target_is_directory=True)
                else:
                    destination.mkdir()
                appeared.append(destination.lstat().st_ino)
                return True

            with patch("blueprint_lean_sync._verified_dependency",
                       side_effect=verify_and_create_destination):
                assert not _fetch_dependency_sources(destination, source.as_uri(), rev)
            assert appeared == [destination.lstat().st_ino]
            if symlink:
                assert destination.is_symlink()
                assert destination.readlink() == root / "missing-target"
            else:
                assert destination.is_dir() and not list(destination.iterdir())


if __name__ == "__main__":
    test_split_tex_lean_decls_handles_continuations_and_top_level_commas()
    test_structure_fields_are_declarations()
    test_duplicate_lean_tags_are_reported_once_per_declaration()
    test_root_prefixed_decls_escape_namespace()
    test_sync_resolves_mathlib_and_qiclean_without_local_wrappers()
    test_dependency_rejects_unverified_sources()
    test_generated_names_are_attached_exact_and_conservative()
    test_tracked_only_and_exact_namespace()
    test_native_dictionary_loading_and_ambiguous_forms()
    test_exact_fetch_stages_without_branch_fallback()
    test_dependency_rejects_unsupported_layouts()
    test_fetch_preserves_destination_appearing_during_verification()
    print("Blueprint declaration scanner tests passed (12 tests).")
