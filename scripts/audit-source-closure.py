"""Record the aggregate's actual first-party closure and pinned source integrity.

This static check supplements, and does not replace, Lean's axiom audit.
It reads the project import graph and checks the preserved vendor hashes.
"""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
VENDOR = ROOT / "vendor/etingof-representation-theory"


def code_only(text):
    """Blank nested comments and strings, preserving line numbers."""
    out = list(text)
    i, depth = 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                j = len(text)
            out[i:j] = " " * (j - i)
            i = j
        elif text[i] == '"':
            out[i] = " "
            i += 1
            while i < len(text):
                c = text[i]
                if c != "\n":
                    out[i] = " "
                i += 1
                if c == "\\" and i < len(text):
                    if text[i] != "\n":
                        out[i] = " "
                    i += 1
                elif c == '"':
                    break
        else:
            i += 1
    return "".join(out)


def resolve(module):
    if module == "QuantumOracle" or module.startswith("QuantumOracle."):
        return ROOT.joinpath(*module.split(".")).with_suffix(".lean")
    if module == "RepresentationTheory" or module.startswith("RepresentationTheory."):
        return VENDOR.joinpath(*module.split(".")).with_suffix(".lean")
    return None


token_re = re.compile(
    r"\b(?:sorry|admit|sorryAx|axiom|constant|unsafe|proof_wanted|theorem_wanted|"
    r"def_wanted|instance_wanted|native_decide|implemented_by|extern|run_elab|run_tac)\b|#eval"
)
pending, seen, external, missing, findings = ["QuantumOracle"], {}, set(), [], []
while pending:
    module = pending.pop()
    if module in seen:
        continue
    path = resolve(module)
    if path is None:
        external.add(module)
        continue
    if not path.is_file():
        missing.append(module)
        continue
    raw = path.read_text(encoding="utf-8-sig")
    code = code_only(raw)
    seen[module] = {"path": path.relative_to(ROOT).as_posix(),
                    "lines": len(raw.splitlines()),
                    "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    for line in re.findall(r"^\s*(?:public\s+|private\s+|meta\s+)?import\s+([^\n]+)", code, re.M):
        pending.extend(line.split())
    for match in token_re.finditer(code):
        findings.append({"module": module, "token": match.group(),
                         "line": code.count("\n", 0, match.start()) + 1})

manifest = json.loads((VENDOR / "_provenance/source-manifest.json").read_text(encoding="utf-8-sig"))
changed = []
for entry in manifest["files"]:
    path = VENDOR / entry["path"]
    actual = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
    if actual != entry["sha256"]:
        changed.append({"path": entry["path"], "expected": entry["sha256"], "actual": actual})
report = {
    "checkedUtc": datetime.now(timezone.utc).isoformat(),
    "scope": "Current aggregate first-party import closure; static scan, not kernel verification",
    "projectModules": sum(m == "QuantumOracle" or m.startswith("QuantumOracle.") for m in seen),
    "vendorModules": sum(m.startswith("RepresentationTheory.") for m in seen),
    "modules": dict(sorted(seen.items())), "externalImports": sorted(external),
    "missingModules": sorted(set(missing)), "prohibitedTokens": findings,
    "vendorCommit": manifest["commit"], "checkedVendorFiles": len(manifest["files"]),
    "changedVendorFiles": changed,
}
report["status"] = "passed" if not (missing or findings or changed) else "failed"
outpath = ROOT / "logs/import-closure-audit.json"
outpath.parent.mkdir(exist_ok=True)
outpath.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: v for k, v in report.items() if k not in ("modules", "externalImports")}, indent=2))
raise SystemExit(0 if report["status"] == "passed" else 1)
