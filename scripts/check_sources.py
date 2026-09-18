"""Record or check pinned upstream provenance for the actual import closure.

Normal mode is offline and checks local SHA-256 hashes and closure coverage.
--record downloads original pinned bytes to an ignored cache and records both
original and local hashes. It never replaces proof source. --archive-unused
moves bootstrap downloads outside the source directories, preserving the bytes.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
PLBY = "8822f7ddef30fadbd92e1c6ab4ed897af356af5e"
PANTHEON = "ffbb65c21afc8a36ace67720f1b0df1c63d26bd1"
EXCERPTS = {
    "ErdosProblems/Erdos444/SquarePart.lean":
        "ErdosProblems/Erdos387/RoughDivisorBound.lean",
    "ErdosProblems/Erdos444/SymmetricMass.lean":
        "ErdosProblems/Erdos851/BetaSieveFailureCombinatorics.lean",
}
PREFIXES = ("ErdosProblems", "UnitFractions", "BoundedGaps", "Util")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def closure():
    todo = ["ErdosProblems.Erdos444"]
    found = set()
    while todo:
        module = todo.pop()
        path = module.replace(".", "/") + ".lean"
        if path in found:
            continue
        if not module.startswith(tuple(p + "." for p in PREFIXES)):
            raise SystemExit(f"Unexpected dependency: {module}")
        found.add(path)
        source = (ROOT / path).read_text()
        for imports in re.findall(r"^import\s+([^\n]+)", source, re.M):
            for dependency in imports.split():
                if dependency == "Mathlib" or dependency.startswith(
                    ("Mathlib.", "Lean.", "Std.", "Batteries.")
                ):
                    continue
                todo.append(dependency)
    return sorted(found)


def record(path):
    original_path = EXCERPTS.get(path, path)
    if path.startswith("BoundedGaps/"):
        repo, commit, subdir = "frenzymath/FormalPantheon", PANTHEON, "BoundedGaps/"
    else:
        repo, commit, subdir = "plby/lean-proofs", PLBY, "src/latest/"
    url = f"https://raw.githubusercontent.com/{repo}/{commit}/{subdir}{original_path}"
    cache = ROOT / ".upstream-cache" / repo / original_path
    if not cache.exists():
        data = subprocess.run(
            ["curl", "--http1.1", "--retry", "3", "--max-time", "90", "-fLsS", url],
            check=True, capture_output=True,
        ).stdout
        cache.parent.mkdir(parents=True, exist_ok=True)
        cache.write_bytes(data)
    original = cache.read_bytes()
    local = (ROOT / path).read_bytes()
    kind = "excerpt" if path in EXCERPTS else (
        "unchanged" if local == original else "adapted"
    )
    return {"path": path, "source_url": url, "kind": kind,
            "upstream_sha256": digest(original), "local_sha256": digest(local)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    parser.add_argument("--archive-unused", action="store_true")
    args = parser.parse_args()
    paths = closure()
    manifest = ROOT / "upstream-manifest.json"
    if args.record:
        with ThreadPoolExecutor(max_workers=6) as pool:
            records = list(pool.map(record, paths))
        manifest.write_text(json.dumps({"files": records}, indent=2) + "\n")
        for entry in records:
            if entry["kind"] != "unchanged":
                print(entry["kind"], entry["path"])
    else:
        records = json.loads(manifest.read_text())["files"]
        if paths != sorted(entry["path"] for entry in records):
            raise SystemExit("Manifest does not match the proof's dependency closure")
        for entry in records:
            if digest((ROOT / entry["path"]).read_bytes()) != entry["local_sha256"]:
                raise SystemExit(f"Source hash mismatch: {entry['path']}")
    if args.archive_unused:
        count = 0
        for prefix in PREFIXES:
            for source in (ROOT / prefix).rglob("*.lean"):
                relative = source.relative_to(ROOT)
                if relative.as_posix() not in paths:
                    target = ROOT / ".unused-upstream" / relative
                    if target.exists():
                        raise SystemExit(f"Archive already exists: {relative}")
                    target.parent.mkdir(parents=True, exist_ok=True)
                    source.rename(target)
                    count += 1
        print(f"Archived {count} unused bootstrap downloads in .unused-upstream/")
    print(f"PASS: provenance covers {len(paths)} imported source files.")


if __name__ == "__main__":
    main()
