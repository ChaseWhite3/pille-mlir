#!/usr/bin/env python3
"""Reproduce in a fresh directory; never install or modify the source checkout."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile


def run(args, **kwargs):
    subprocess.run([str(arg) for arg in args], check=True, **kwargs)


def main():
    artifact = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=["tests", "baseline", "transpose", "public-api", "candidate16", "candidate64"], default="tests")
    parser.add_argument("--source", type=Path, default=artifact.parents[1])
    parser.add_argument("--work", type=Path, help="new directory; omitted creates a temporary directory")
    parser.add_argument("--racket", default=shutil.which("racket") or "/opt/homebrew/bin/racket")
    parser.add_argument("--llvm", default=os.environ.get("PILLE_LLVM_PREFIX", "/opt/homebrew/opt/llvm"))
    parser.add_argument("--model", default=os.environ.get("CLOSER_PARSER_MODEL", str(Path.home() / ".cache/closer/parser")))
    args = parser.parse_args()
    if args.work:
        work = args.work.resolve()
        work.mkdir(parents=True, exist_ok=False)
    else:
        work = Path(tempfile.mkdtemp(prefix="pille-perf-reproduce-"))
    print("Isolated work directory:", work, flush=True)
    baseline = json.loads((artifact / "baseline.json").read_text())
    run(["git", "clone", "--quiet", "--no-hardlinks", "--no-checkout", args.source.resolve(), work / "pille"])
    run(["git", "checkout", "--quiet", "--detach", baseline["pille_commit"]], cwd=work / "pille")
    run(["git", "apply", artifact / "pille.patch"], cwd=work / "pille")
    with tarfile.open(artifact / "closer-source-snapshot.tar.gz") as archive:
        # This bundle contains only regular source files and directories.
        for member in archive.getmembers():
            if Path(member.name).is_absolute() or ".." in Path(member.name).parts or not (member.isfile() or member.isdir()):
                raise ValueError("Unsafe snapshot entry: " + member.name)
        archive.extractall(work)
    for relative, expected in json.loads((artifact / "source-manifest.json").read_text()).items():
        actual = hashlib.sha256((work / "closer" / relative).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError("Source snapshot digest differs: " + relative)
    for name in ["parser-baseline", "parser-candidate", "parser-candidate64"]:
        shutil.copytree(artifact / name, work / "artifacts" / name)
    shutil.copy2(artifact / "transpose-api-bench.rhm", work / "artifacts")
    for path in (work / "artifacts").rglob("*"):
        if path.is_file() and path.suffix in {".rhm", ".rkt", ".sh"}:
            path.write_text(path.read_text().replace(baseline["original_isolated_root"], str(work)))

    closer = work / "closer"
    if args.mode == "public-api":
        closer = work / "closer-public-api"
        shutil.copytree(work / "closer", closer)
        with (artifact / "closer-public-math.patch").open("rb") as patch:
            run(["patch", "-p1"], cwd=closer, stdin=patch)
    elif args.mode in {"candidate16", "candidate64"}:
        name = "closer-candidate" if args.mode == "candidate16" else "closer-candidate64"
        closer = work / name
        shutil.copytree(work / "closer", closer)
        with (artifact / (name + "-REJECTED.patch")).open("rb") as patch:
            run(["patch", "-p1"], cwd=closer, stdin=patch)

    env = dict(os.environ)
    packages = ["pille-lib", "pille-llvm-lib", "pille-spmd-lib", "pille-mlir-lib", "pille"]
    env["PLTCOLLECTS"] = os.pathsep.join([str(closer / "closer-exports")] + [str(work / "pille" / p) for p in packages]) + os.pathsep
    env["PLTCOMPILEDROOTS"] = str(work / "compiled") + os.pathsep
    env["PILLE_LLVM_PREFIX"] = args.llvm
    env["PILLE_MLIR_PREFIX"] = args.llvm
    env["CLOSER_PARSER_MODEL"] = args.model
    if args.mode in {"baseline", "public-api", "candidate16", "candidate64"} and not (Path(args.model) / "supertagger.safetensors").is_file():
        raise ValueError("Parser model is required for this mode; use --model")
    command = [args.racket, "-y"]
    if args.mode == "tests":
        tests = ["float.rhm", "simd.rhm", "interop.rhm", "pointer.rhm", "public_math.rhm", "buffer.rhm", "spmd/basics.rhm", "spmd/checked-integers.rhm"]
        command += ["-l", "raco", "--", "test", "--process", "--jobs", "1", "--make"]
        command += [work / "pille/pille/pille/tests" / t for t in tests]
    elif args.mode == "public-api":
        command += ["-l", "raco", "--", "test", closer / "closer-exports/closer_exports/reader/parser_check.rhm"]
    elif args.mode == "transpose":
        command += [work / "artifacts/transpose-api-bench.rhm"]
    else:
        name = {"baseline": "parser-baseline", "candidate16": "parser-candidate", "candidate64": "parser-candidate64"}[args.mode]
        command += [work / "artifacts" / name / "run.rkt"]
    run(command, cwd=work, env=env)


if __name__ == "__main__":
    main()
