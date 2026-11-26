"""Clean-build the source modules and check the finite-basis undecidability theorem."""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from graphlib import TopologicalSorter
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parent
MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"


def command(args, *, cwd=None, env=None):
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(result.stdout or f"Command failed: {args[0]}")
    return result.stdout.strip()


def check_mathlib(path):
    lock = (ROOT / "mathlib-lake-manifest.json").read_bytes()
    if command(["git", "-C", path, "rev-parse", "HEAD"]) != MATHLIB:
        raise SystemExit("Wrong mathlib Git revision")
    if (path / "lake-manifest.json").read_bytes() != lock:
        raise SystemExit("The mathlib Lake manifest differs from the pinned manifest")
    libdirs = [path / ".lake/build/lib/lean"]
    for package in json.loads(lock)["packages"]:
        checkout = path / ".lake/packages" / package["name"]
        if command(["git", "-C", checkout, "rev-parse", "HEAD"]) != package["rev"]:
            raise SystemExit(f"Unexpected revision of {package['name']}")
        libdirs.append(checkout / ".lake/build/lib/lean")
    return libdirs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", required=True, type=Path, help="Built checkout of pinned mathlib4")
    parser.add_argument("--jobs", type=int, default=4, help="Concurrent Lean processes")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    for row in (ROOT / "SHA256SUMS").read_text().splitlines():
        expected, name = row.split("  ", 1)
        if sha256((ROOT / name).read_bytes()).hexdigest() != expected:
            raise SystemExit(f"SHA-256 mismatch: {name}")
    lean = os.environ.get("LEAN", "lean")
    version = command([lean, "--version"])
    if "version 4.19.0," not in version:
        raise SystemExit(f"Lean 4.19.0 required. Found {version}")
    print("Lean 4.19.0; mathlib " + MATHLIB, flush=True)
    libs = check_mathlib(args.mathlib.resolve())
    sources = {p.stem: p for p in sorted((ROOT / "Proof").glob("*.lean"))}
    if len(sources) != 235:
        raise SystemExit("Expected 235 project source modules")
    graph = TopologicalSorter()
    for name, path in sources.items():
        imports = re.findall(r"^import (Problem455\w+)\s*$", path.read_text(), re.MULTILINE)
        if set(imports) - sources.keys():
            raise SystemExit(f"Missing local import for {name}")
        graph.add(name, *imports)
    graph.prepare()
    with TemporaryDirectory(prefix="semigroup-proof-") as directory:
        obj = Path(directory).resolve()
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [obj, *libs])))
        def compile_one(name):
            path = sources[name]
            output = command([lean, "-DwarningAsError=true", "-o", obj / (name + ".olean"), path.name],
                             cwd=path.parent, env=env)
            if output:
                print(output, flush=True)
        pending = {}
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            while graph.is_active():
                for name in sorted(graph.get_ready()):
                    pending[pool.submit(compile_one, name)] = name
                done, _ = wait(pending, return_when=FIRST_COMPLETED)
                for task in done:
                    task.result()
                    name = pending.pop(task)
                    graph.done(name)
                    print(f"Built {name}", flush=True)
        for filename in ("Audit.lean", "ExpandedStatement.lean", "MonoidPromise.lean", "Examples.lean"):
            print(f"Checking {filename}", flush=True)
            print(command([lean, "--trust=0", "-DwarningAsError=true", filename],
                          cwd=ROOT/"checks", env=env), flush=True)
    print("All source and kernel checks passed.", flush=True)


if __name__ == "__main__":
    main()
