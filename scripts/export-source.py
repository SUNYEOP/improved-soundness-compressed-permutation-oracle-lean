"""Create an allowlisted source release as a directory and ZIP archive.

Run from the Lean source repository. Existing destinations are never replaced.
The release contains source, configuration, documentation, and license files.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import zipfile

ROOT = Path(__file__).resolve().parent.parent
VENDOR = Path("vendor/etingof-representation-theory")
TOP_FILES = [
    ".gitignore", ".gitattributes", "LICENSE", "README.md", "THIRD_PARTY_NOTICES.md",
    "lean-toolchain", "lakefile.toml", "lake-manifest.json", "QuantumOracle.lean",
    "AxiomAudit.lean", "lake-local.ps1", "setup.ps1", "toolchain-windows.json",
    ".github/workflows/lean.yml", "docs/THEOREM_STATEMENT.md", "docs/DEPENDENCIES.md",
    "docs/REPRODUCIBILITY.md", "docs/PUBLISHING.md", "docs/PROOF_MAP.md",
    "scripts/check-proof.py", "scripts/audit-source-closure.py", "scripts/audit-layers.py",
    "scripts/export-source.py",
    "review/README.md", "review/Statement.lean", "review/CORE_DEFINITIONS.md",
    "review/DEFINITIONS.md", "review/semantic-dependencies.json",
    "review/SOURCE_MANIFEST.json", "review/LICENSE", "review/tools/README.md",
    "review/tools/reading-order.json", "review/tools/build-review.py",
    "review/tools/ExtractDependencies.lean",
]


def relative_file(name):
    path = ROOT / name
    resolved = path.resolve()
    if not resolved.is_relative_to(ROOT.resolve()) or not resolved.is_file():
        raise ValueError(f"Missing or unsafe source path: {name}")
    return path.relative_to(ROOT)


def collect_sources():
    files = {relative_file(name) for name in TOP_FILES}
    files.update(relative_file(p.relative_to(ROOT)) for p in (ROOT / "QuantumOracle").rglob("*.lean"))
    # Include new review entry points/tools without admitting build products,
    # archives, or arbitrary files from the working tree.
    review_extensions = {".lean", ".md", ".json", ".py"}
    files.update(relative_file(p.relative_to(ROOT)) for p in (ROOT / "review").rglob("*")
                 if p.is_file() and p.suffix in review_extensions)
    provenance = VENDOR / "_provenance/source-manifest.json"
    manifest = json.loads((ROOT / provenance).read_text(encoding="utf-8-sig"))
    files.add(relative_file(provenance))
    for entry in manifest["files"]:
        path = relative_file(VENDOR / entry["path"])
        digest = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        if digest != entry["sha256"]:
            raise ValueError(f"Pinned vendor source changed: {path}")
        files.add(path)
    atlas = Path("vendor/proofatlas/hook-length-formula")
    files.update(relative_file(atlas / name) for name in
                 ("Basic.lean", "LICENSE", "NOTICE", "README.md", "evidence.json"))
    original = ROOT / atlas / "Basic.lean"
    if hashlib.sha256(original.read_bytes()).hexdigest() != (
            "bfcd609759bb37494f274922f11b212beaae2dce56da4e197912ced7915089a6"):
        raise ValueError("Original ProofAtlas source changed")
    forbidden_parts = {".git", ".lake", ".tools", ".cache", "_scratch", "logs",
                       "migration", "reference-notes", "__pycache__"}
    for path in files:
        if forbidden_parts.intersection(path.parts):
            raise ValueError(f"Generated or private material in export: {path}")
    return sorted(files, key=lambda p: p.as_posix()), manifest["commit"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--name", default="quantum-oracle-lean",
                        help="New directory name under this project's ignored release/ directory")
    args = parser.parse_args()
    if not args.name or Path(args.name).name != args.name or args.name in {".", ".."}:
        parser.error("--name must be a single directory name")
    release = ROOT / "release"
    destination = release / args.name
    archive = release / f"{args.name}.zip"
    if destination.exists() or archive.exists():
        parser.error("Destination already exists; choose a new --name (nothing was replaced)")
    files, vendor_commit = collect_sources()
    records = []
    destination.mkdir(parents=True)
    for relative in files:
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, target)
        contents = target.read_bytes()
        records.append({"path": relative.as_posix(), "bytes": len(contents),
                        "sha256": hashlib.sha256(contents).hexdigest()})
    report = {
        "createdUtc": datetime.now(timezone.utc).isoformat(),
        "kind": "Source-only export; see the proof checker for kernel verification",
        "fileCount": len(records), "sourceBytes": sum(f["bytes"] for f in records),
        "vendorCommit": vendor_commit,
        "license": "MIT for original project code; third-party exceptions retained",
        "files": records,
    }
    manifest_path = destination / "SOURCE_MANIFEST.json"
    manifest_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    with zipfile.ZipFile(archive, "x", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as bundle:
        for relative in files + [Path("SOURCE_MANIFEST.json")]:
            bundle.write(destination / relative, (Path(args.name) / relative).as_posix())
    print(json.dumps({"directory": str(destination), "archive": str(archive),
                      "sourceFiles": len(records), "sourceBytes": report["sourceBytes"],
                      "archiveBytes": archive.stat().st_size,
                      "archiveSha256": hashlib.sha256(archive.read_bytes()).hexdigest()}, indent=2))


if __name__ == "__main__":
    main()
