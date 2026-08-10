#!/usr/bin/env python3
"""Regression checks for deterministic, transactional tenkz corpus rendering."""

from __future__ import annotations

import hashlib
import io
import os
import shutil
import subprocess
import sys
import tempfile
from contextlib import redirect_stderr
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
RENDERER = ROOT / "scripts" / "tenkz_render_corpus.py"
DRIVER = ROOT / "scripts" / "tenkz_corpus.sh"
sys.path.insert(0, str(ROOT / "scripts"))
import tenkz_render_corpus as render  # noqa: E402


def write_executable(path: Path, source: str) -> None:
    path.write_text(source, encoding="utf-8")
    path.chmod(0o755)


def run_renderer(
    input_dir: Path,
    output_dir: Path,
    bin_dir: Path,
    *,
    version: str = "v1",
    fail_render: str = "",
    protect: Path | None = None,
) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["PATH"] = f"{bin_dir}{os.pathsep}{env['PATH']}"
    env["FAKE_RENDER_VERSION"] = version
    env["FAKE_RENDER_FAIL"] = fail_render
    command = [
        sys.executable,
        str(RENDERER),
        "--input-dir",
        str(input_dir),
        "--output-dir",
        str(output_dir),
    ]
    if protect is not None:
        command.extend(["--protect", str(protect)])
    return subprocess.run(
        command,
        cwd=ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=30,
    )


def tree_bytes(root: Path) -> dict[str, bytes]:
    return {
        path.relative_to(root).as_posix(): path.read_bytes()
        for path in sorted(root.rglob("*"))
        if path.is_file()
    }


def expected_checksums(output: Path, relative_pngs: list[str]) -> str:
    return "".join(
        f"{hashlib.sha256((output / relative).read_bytes()).hexdigest()}  {relative}\n"
        for relative in relative_pngs
    )


def run_driver(*arguments: str) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["TENKZ_CORPUS_VALIDATE_ONLY"] = "1"
    return subprocess.run(
        ["bash", str(DRIVER), *arguments],
        cwd=ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=30,
    )


def check_repo_relative_render_dir(work: Path) -> None:
    bin_dir = work / "driver-bin"
    capture = work / "render-dir.txt"
    bin_dir.mkdir()
    write_executable(
        bin_dir / "python3",
        """#!/bin/sh
if [ "$1" = "-" ]; then
    cat >/dev/null
    exit 0
fi
case "$1" in
    */tenkz_render_corpus.py)
        shift
        while [ "$#" -gt 0 ]; do
            if [ "$1" = "--output-dir" ]; then
                printf '%s\n' "$2" > "$FAKE_RENDER_DIR_CAPTURE"
                exit 0
            fi
            shift
        done
        exit 9
        ;;
esac
exit 0
""",
    )
    write_executable(
        bin_dir / "xelatex",
        """#!/bin/sh
for source do :; done
stem=${source%.tex}
: > "$stem.pdf"
printf 'picture|id=fake\n' > "$stem.tnlog"
""",
    )
    for command in ("pdfinfo", "pdftocairo"):
        write_executable(bin_dir / command, "#!/bin/sh\nexit 0\n")

    env = os.environ.copy()
    env["PATH"] = f"{bin_dir}{os.pathsep}{env['PATH']}"
    env["FAKE_RENDER_DIR_CAPTURE"] = str(capture)
    result = subprocess.run(
        [
            "bash",
            str(DRIVER),
            "--render",
            "--render-dir",
            "build/tenkz-relative-probe",
        ],
        cwd=ROOT / "tests" / "tenkz",
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=120,
    )
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    expected = ROOT / "build" / "tenkz-relative-probe"
    if capture.read_text(encoding="utf-8").strip() != str(expected):
        raise AssertionError("relative --render-dir was not anchored to the repository root")


def main() -> int:
    bad_cli = [
        (("--unknown",), "unknown argument"),
        (("--render-dir", "baseline"), "requires --render"),
        (("--render-dir", "--render"), "requires a non-empty directory"),
        (("--render",), "cannot be combined"),
    ]
    for arguments, diagnostic in bad_cli:
        result = run_driver(*arguments)
        if result.returncode == 0 or diagnostic not in result.stderr:
            raise AssertionError(f"bad driver CLI was accepted: {arguments!r}")

    with tempfile.TemporaryDirectory(prefix="tenkz-render-test-") as tmp:
        work = Path(tmp)
        input_dir = work / "compiled"
        output_dir = work / "baseline"
        bin_dir = work / "bin"
        input_dir.mkdir()
        output_dir.mkdir()
        bin_dir.mkdir()

        for stem in ("alpha", "beta"):
            (input_dir / f"{stem}.tex").write_text("fixture\n", encoding="utf-8")
            (input_dir / f"{stem}.pdf").write_bytes(b"synthetic pdf")

        write_executable(
            bin_dir / "pdfinfo",
            """#!/usr/bin/env python3
import sys
from pathlib import Path
print(f"Pages: {2 if Path(sys.argv[-1]).stem == 'alpha' else 1}")
""",
        )
        write_executable(
            bin_dir / "pdftocairo",
            """#!/usr/bin/env python3
import os
import sys
from pathlib import Path
page = sys.argv[sys.argv.index('-f') + 1]
pdf = Path(sys.argv[-2])
identity = f"{pdf.stem}:{page}"
if os.environ.get('FAKE_RENDER_FAIL') == identity:
    print('injected render failure', file=sys.stderr)
    raise SystemExit(9)
Path(sys.argv[-1] + '.png').write_bytes(
    f"{os.environ['FAKE_RENDER_VERSION']}:{identity}".encode()
)
""",
        )

        first = run_renderer(input_dir, output_dir, bin_dir)
        if first.returncode:
            raise AssertionError(first.stdout + first.stderr)
        relative_pngs = [
            "alpha/page-001.png",
            "alpha/page-002.png",
            "beta/page-001.png",
        ]
        if (output_dir / "CENSUS.tsv").read_text(encoding="utf-8") != (
            "source_file\tpages\nalpha.tex\t2\nbeta.tex\t1\n"
        ):
            raise AssertionError("render census was not deterministic")
        if (output_dir / "SHA256SUMS").read_text(encoding="utf-8") != (
            expected_checksums(output_dir, relative_pngs)
        ):
            raise AssertionError("render checksum manifest was not deterministic")

        (output_dir / "stale.png").write_bytes(b"stale")
        before_failure = tree_bytes(output_dir)
        failed = run_renderer(
            input_dir,
            output_dir,
            bin_dir,
            version="v2",
            fail_render="beta:1",
        )
        if failed.returncode == 0 or "injected render failure" not in failed.stderr:
            raise AssertionError("injected renderer failure was not reported")
        if tree_bytes(output_dir) != before_failure:
            raise AssertionError("failed render changed the last complete baseline")

        second = run_renderer(input_dir, output_dir, bin_dir, version="v2")
        if second.returncode:
            raise AssertionError(second.stdout + second.stderr)
        if tree_bytes(output_dir) == before_failure:
            raise AssertionError("successful rerender did not replace the baseline")
        if (output_dir / "stale.png").exists():
            raise AssertionError("successful rerender retained a stale file")

        protected = run_renderer(
            input_dir,
            output_dir,
            bin_dir,
            protect=output_dir,
        )
        if protected.returncode == 0 or "protected directory" not in protected.stderr:
            raise AssertionError("protected output directory was accepted")

        unowned = work / "unowned"
        unowned.mkdir()
        (unowned / "keep.txt").write_text("user data\n", encoding="utf-8")
        rejected = run_renderer(input_dir, unowned, bin_dir)
        if rejected.returncode == 0 or "without a valid" not in rejected.stderr:
            raise AssertionError("nonempty unowned output directory was accepted")
        if (unowned / "keep.txt").read_text(encoding="utf-8") != "user data\n":
            raise AssertionError("rejected output directory was changed")

        symlinked_marker = work / "symlinked-marker"
        symlinked_marker.mkdir()
        (symlinked_marker / "keep.txt").write_text("user data\n", encoding="utf-8")
        (symlinked_marker / render.MARKER_NAME).symlink_to(
            output_dir / render.MARKER_NAME
        )
        rejected_symlink = run_renderer(input_dir, symlinked_marker, bin_dir)
        if rejected_symlink.returncode == 0 or "valid regular" not in rejected_symlink.stderr:
            raise AssertionError("symlinked ownership marker was accepted")
        if (symlinked_marker / "keep.txt").read_text(encoding="utf-8") != "user data\n":
            raise AssertionError("symlink-marker output directory was changed")

        nonregular_marker = work / "nonregular-marker"
        nonregular_marker.mkdir()
        (nonregular_marker / "keep.txt").write_text("user data\n", encoding="utf-8")
        (nonregular_marker / render.MARKER_NAME).mkdir()
        rejected_nonregular = run_renderer(input_dir, nonregular_marker, bin_dir)
        if (
            rejected_nonregular.returncode == 0
            or "valid regular" not in rejected_nonregular.stderr
        ):
            raise AssertionError("non-regular ownership marker was accepted")
        if (nonregular_marker / "keep.txt").read_text(encoding="utf-8") != "user data\n":
            raise AssertionError("non-regular-marker output directory was changed")

        malformed_marker = work / "malformed-marker"
        malformed_marker.mkdir()
        (malformed_marker / "keep.txt").write_text("user data\n", encoding="utf-8")
        (malformed_marker / render.MARKER_NAME).write_bytes(b"\xff\xfe")
        rejected_malformed = run_renderer(input_dir, malformed_marker, bin_dir)
        if rejected_malformed.returncode == 0 or "valid regular" not in rejected_malformed.stderr:
            raise AssertionError("malformed UTF-8 ownership marker was accepted")
        if "Traceback" in rejected_malformed.stderr:
            raise AssertionError("malformed UTF-8 ownership marker escaped as a traceback")
        if (malformed_marker / "keep.txt").read_text(encoding="utf-8") != "user data\n":
            raise AssertionError("malformed-marker output directory was changed")

        raced_output = work / "raced-output"
        raced_output.mkdir()
        original_write_manifests = render.write_manifests

        def populate_destination_during_render(
            stage: Path,
            census: list[tuple[str, int]],
            pngs: list[Path],
        ) -> None:
            original_write_manifests(stage, census, pngs)
            (raced_output / "keep.txt").write_text("concurrent user data\n", encoding="utf-8")

        with mock.patch.dict(
            os.environ, {"FAKE_RENDER_VERSION": "race", "FAKE_RENDER_FAIL": ""}
        ), mock.patch.object(
            render, "require_tool", side_effect=lambda name: str(bin_dir / name)
        ), mock.patch.object(
            render, "write_manifests", side_effect=populate_destination_during_render
        ):
            try:
                render.render_corpus(input_dir, raced_output, [])
            except render.RenderError as exc:
                if "changed while rendering" not in str(exc):
                    raise AssertionError(f"race refusal was not explicit: {exc}") from exc
            else:
                raise AssertionError("destination populated during rendering was replaced")
        if (raced_output / "keep.txt").read_text(encoding="utf-8") != (
            "concurrent user data\n"
        ):
            raise AssertionError("concurrent user data was changed or deleted")

        restore_output = work / "restore-output"
        missing_stage = work / "missing-stage"
        restore_output.mkdir()
        (restore_output / render.MARKER_NAME).write_text(
            render.MARKER_CONTENT, encoding="utf-8"
        )
        (restore_output / "old.png").write_bytes(b"old")
        try:
            render.install_stage(missing_stage, restore_output)
        except render.RenderError:
            pass
        else:
            raise AssertionError("missing render stage was accepted")
        if (restore_output / "old.png").read_bytes() != b"old":
            raise AssertionError("pre-commit install failure did not restore the prior baseline")

        cleanup_output = work / "cleanup-output"
        cleanup_stage = work / "cleanup-stage"
        cleanup_output.mkdir()
        cleanup_stage.mkdir()
        (cleanup_output / render.MARKER_NAME).write_text(
            render.MARKER_CONTENT, encoding="utf-8"
        )
        (cleanup_output / "old.png").write_bytes(b"old")
        (cleanup_stage / "new.png").write_bytes(b"new")
        cleanup_backup = cleanup_output.parent / (
            f".{cleanup_output.name}.previous.{os.getpid()}"
        )

        def partially_delete_backup(path: Path) -> None:
            (path / "old.png").unlink()
            raise OSError("injected partial cleanup failure")

        warning = io.StringIO()
        with mock.patch.object(
            render.shutil, "rmtree", side_effect=partially_delete_backup
        ), redirect_stderr(warning):
            render.install_stage(cleanup_stage, cleanup_output)
        if (cleanup_output / "new.png").read_bytes() != b"new":
            raise AssertionError("cleanup failure displaced the committed new baseline")
        if cleanup_stage.exists():
            raise AssertionError("committed render remained at the staging path")
        if not cleanup_backup.is_dir():
            raise AssertionError("remaining prior baseline backup was not retained")
        if str(cleanup_backup) not in warning.getvalue():
            raise AssertionError("cleanup warning omitted the exact backup path")
        if "installed complete render baseline" not in warning.getvalue():
            raise AssertionError(
                "cleanup warning did not identify the new baseline as authoritative"
            )
        shutil.rmtree(cleanup_backup)

        (input_dir / "beta.pdf").unlink()
        before_missing = tree_bytes(output_dir)
        missing = run_renderer(input_dir, output_dir, bin_dir)
        if missing.returncode == 0 or "compiled corpus PDFs are missing" not in missing.stderr:
            raise AssertionError("missing compiled PDF was accepted")
        if tree_bytes(output_dir) != before_missing:
            raise AssertionError("preflight failure changed the last complete baseline")

        check_repo_relative_render_dir(work)

    print("PASS: tenkz corpus render baseline replacement")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
