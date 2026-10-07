#!/usr/bin/env python3
"""Check provenance structure and recorded source evidence; never execute ledger commands."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

from jsonschema import Draft202012Validator

PIN = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
LICENSE_SHA256 = "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4"
REPO = "LionSR/TNLean"
ID_RE = re.compile(r"^Provenance-ID: ([a-z0-9][a-z0-9._-]*)$", re.M)


class Invalid(ValueError):
    """An actionable provenance error."""


def require(condition, message):
    if not condition:
        raise Invalid(message)


def read_json(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, f"duplicate JSON key: {key}")
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=unique)


def safe_file(root, relative):
    parts = PurePosixPath(relative).parts
    require(parts and not relative.startswith("/") and ".." not in parts
            and "\\" not in relative, f"unsafe path: {relative}")
    target = (root / relative).resolve()
    require(target.is_relative_to(root.resolve()), f"path escapes repository: {relative}")
    require(target.is_file(), f"missing file: {relative}")
    return target


def git_bytes(root, revision, path):
    result = subprocess.run(["git", "-C", str(root), "show", f"{revision}:{path}"],
                            capture_output=True, check=False)
    require(result.returncode == 0, f"cannot read {revision}:{path} in {root}")
    return result.stdout


def lean_parts(text):
    """Blank comments and strings, preserving line numbers; return comment blocks too."""
    code, comments = [], []
    i = 0
    while i < len(text):
        start = i
        if text.startswith("/-", i):
            depth, i = 1, i + 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            require(depth == 0, "unterminated Lean comment")
            comments.append(text[start:i])
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            code.append(text[i])
            i += 1
            continue
        code.extend("\n" if c == "\n" else " " for c in text[start:i])
    return "".join(code), comments


def declarations(text):
    """Conservative named command index, not a Lean elaborator or macro expander."""
    code, _ = lean_parts(text)
    stack, result = [], {}
    for number, line in enumerate(code.splitlines(), 1):
        line = re.sub(r"@\[[^]]*\]", "", line).strip()
        scope = re.match(r"(namespace|section)\b\s*([^\s]*)", line)
        if scope:
            stack.append(scope[2] if scope[1] == "namespace" else "")
            continue
        if re.match(r"end\b", line):
            if stack:
                stack.pop()
            continue
        match = re.match(r"(?:(?:noncomputable|protected|private|public)\s+)*"
                         r"(?:def|abbrev|theorem|lemma|structure|class|inductive|instance)\s+"
                         r"([^\s(:{\[]+)", line)
        if match:
            name = match[1]
            prefix = ".".join(s for s in stack if s)
            qualified = name.removeprefix("_root_.") if name.startswith("_root_.") else (
                f"{prefix}.{name}" if prefix else name)
            result[qualified] = number
    return result


def check_reference(ref, roots, required=False):
    start, end = ref["lines"]
    require(start <= end, "reversed source lines")
    expected = (f'https://github.com/{ref["repository"]}/blob/{ref["commit"]}/'
                f'{ref["path"]}#L{start}-L{end}')
    require(ref["url"] == expected, f"immutable source URL mismatch: {ref['url']}")
    root = roots.get(ref["repository"])
    require(root is not None or not required, f"repository root required: {ref['repository']}")
    if root is None:
        return None
    data = git_bytes(root, ref["commit"], ref["path"])
    source = data.decode()
    require(end <= len(source.splitlines()), "source lines exceed file length")
    require(start <= declarations(source).get(ref["declaration"], -1) <= end,
            f"missing source declaration in line range: {ref['declaration']}")
    return data


def notice_block(text, entry):
    _, blocks = lean_parts(text)
    matching = [b for b in blocks if entry["id"] in ID_RE.findall(b)]
    require(len(matching) == 1, f"expected one notice for {entry['id']}")
    block = matching[0]
    require(entry["downstream"]["declaration"] in block, "notice missing downstream declaration")
    kind = entry["reuse_kind"]
    if kind in ("copied", "adapted"):
        upstream = entry["upstream"]
        heading = f"{kind.capitalize()} from OpenAI's openai/math repository (Apache-2.0)."
        require(heading in block, "missing copied/adapted notice heading")
        for key in ("commit", "path", "declaration", "url"):
            require(upstream[key] in block, f"notice missing upstream {key}")
        for change in entry["changes"]:
            require(change in block, "notice missing concrete change description")
    elif kind == "original":
        require("no upstream Lean proof text reused" in block, "missing independence notice")
        for paper in entry["paper_sources"]:
            require(paper["version"] in block, "notice missing manuscript version")
            for label in paper["labels"]:
                require(label in block, "notice missing manuscript label")
    return block


def check_entry(entry, roots):
    active = entry["status"] in ("ported", "replaced")
    kind, upstream = entry["reuse_kind"], entry["upstream"]
    source_data = None
    if upstream is not None:
        require(upstream["repository"] == "openai/math" and upstream["commit"] == PIN,
                "upstream must match pinned source")
        source_data = check_reference(upstream, roots, required=active)
    if kind == "existing_library":
        library = entry["library"]
        check_reference(library, roots, required=active)
        for key in ("repository", "path", "declaration"):
            require(entry["downstream"][key] == library[key], "replacement/downstream mismatch")
        if active:
            require(entry["verification"]["revision"] == library["commit"],
                    "replacement verification must use exact library pin")
    for notice in entry["notices"]:
        if "openai/math" in roots:
            data = git_bytes(roots["openai/math"], PIN, notice["source_path"]).decode()
            require(notice["text"] in data, "retained notice absent from claimed source")
    if not active:
        return
    down, verification = entry["downstream"], entry["verification"]
    require(down["repository"] == verification["repository"], "verification repository mismatch")
    require(down["repository"] in roots, f"repository root required: {down['repository']}")
    root = roots[down["repository"]]
    data = git_bytes(root, verification["revision"], down["path"])
    require(safe_file(root, down["path"]).read_bytes() == data,
            "downstream differs from verified revision; rebuild and update evidence")
    text = data.decode()
    require(down["declaration"] in declarations(text), "missing downstream declaration")
    commands = verification["commands"]
    require({"build", "axioms"} <= {c["kind"] for c in commands},
            "completed entries require build and axiom evidence")
    for command in commands:
        log = safe_file(root, command["log"]).read_bytes()
        require(hashlib.sha256(log).hexdigest() == command["sha256"], "evidence log hash mismatch")
        if command["kind"] == "axioms":
            output = log.decode()
            declaration = re.escape(down["declaration"])
            axiom_list = re.search(r"['\"]?" + declaration +
                                   r"['\"]? depends on axioms:\s*\[([^]]*)\]", output)
            independent = re.search(r"['\"]?" + declaration +
                                    r"['\"]? does not depend on any axioms", output)
            require(axiom_list or independent, "axiom log missing downstream declaration output")
            if axiom_list:
                axioms = {x.strip() for x in axiom_list[1].split(",") if x.strip()}
                require(axioms <= {"propext", "Classical.choice", "Quot.sound"},
                        f"unapproved axiom dependencies: {sorted(axioms)}")
    if kind == "copied":
        require(data == source_data, "changed file marked copied; classify as adapted")
        notice_text = safe_file(root, down["path"] + ".provenance").read_text()
    else:
        notice_text = text
    if kind != "existing_library":
        notice_block(notice_text, entry)
    for notice in entry["notices"]:
        require(notice["text"] in text or notice["text"] in notice_text,
                "retained upstream notice missing downstream")


def validate(ledgers, schema, roots, scan=True):
    Draft202012Validator.check_schema(schema)
    validator = Draft202012Validator(schema)
    entries, ids, keys = [], set(), set()
    for ledger in ledgers:
        errors = list(validator.iter_errors(ledger))
        require(not errors, "schema: " + "; ".join(
            f"{list(e.absolute_path)}: {e.message}" for e in errors[:3]))
        for entry in ledger["entries"]:
            identifier = entry["id"]
            key = tuple(entry["downstream"][k] for k in ("repository", "path", "declaration"))
            require(identifier not in ids, f"duplicate entry id: {identifier}")
            require(key not in keys, f"duplicate downstream declaration: {key}")
            ids.add(identifier)
            keys.add(key)
            entries.append(entry)
            try:
                check_entry(entry, roots)
            except (Invalid, OSError, UnicodeError) as error:
                raise Invalid(f"{identifier}: {error}") from error
    if scan:
        by_id = {e["id"]: e for e in entries}
        for repository, root in roots.items():
            if repository not in (REPO, "LionSR/QICLean"):
                continue
            for path in (root / repository.split("/")[1]).rglob("*.lean"):
                _, blocks = lean_parts(path.read_text())
                for block in blocks:
                    found = ID_RE.findall(block)
                    if re.search(r"(?:Adapted|Copied) from OpenAI", block):
                        require(found, f"unmapped OpenAI notice in {path}")
                    for identifier in found:
                        require(identifier in by_id, f"orphan notice: {identifier} in {path}")
                        down = by_id[identifier]["downstream"]
                        require(down["repository"] == repository and
                                down["path"] == path.relative_to(root).as_posix(),
                                f"notice/ledger file mismatch: {identifier}")
                        require(by_id[identifier]["status"] in ("planned", "ported"),
                                f"notice for excluded/replaced entry: {identifier}")
                        notice_block(path.read_text(), by_id[identifier])
    return len(entries)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--upstream-root", type=Path)
    parser.add_argument("--repository-root", action="append", default=[], metavar="OWNER/REPO=PATH")
    args = parser.parse_args()
    try:
        root = args.root.resolve()
        roots = {REPO: root}
        if args.upstream_root:
            roots["openai/math"] = args.upstream_root.resolve()
        for item in args.repository_root:
            repository, path = item.split("=", 1)
            require(repository not in roots, f"duplicate repository root: {repository}")
            roots[repository] = Path(path).resolve()
        ledger_root = root / "docs/provenance"
        paths = [ledger_root / "openai-math.json"] + sorted(
            (ledger_root / "openai-math.d").glob("*.json"))
        count = validate([read_json(p) for p in paths],
                         read_json(ledger_root / "openai-math.schema.json"), roots)
        license_data = safe_file(root, "LICENSES/openai-math-Apache-2.0.txt").read_bytes()
        require(hashlib.sha256(license_data).hexdigest() == LICENSE_SHA256,
                "upstream Apache license changed or missing")
        if args.upstream_root:
            for path in ("LICENSE", "lean/LICENSE"):
                require(git_bytes(args.upstream_root, PIN, path) == license_data,
                        f"upstream license mismatch: {path}")
        print(f"Provenance valid: {count} entries. Recorded evidence checked; no Lean build performed.")
        if not args.upstream_root:
            print("Planned upstream content not re-audited (supply --upstream-root).")
        return 0
    except (Invalid, OSError, ValueError) as error:
        print(f"provenance: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
