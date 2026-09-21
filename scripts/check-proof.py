#!/usr/bin/env python3
"""Build and audit the standalone Lean source checkout (Python 3.10+).

Detailed subprocess output remains in ignored local logs. The JSON summary uses
repository-relative paths for the build inputs and audit results.
"""

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import traceback


ROOT = Path(__file__).resolve().parent.parent
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
SUMMARY = "logs/proof-check.json"
ANSI_ESCAPE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
AXIOM_OUTPUT = re.compile(
    r"^'([^\r\n]+)' (?:depends on axioms:[ \t]*\[([^\]]*)\]"
    r"|does not depend on any axioms)[ \t]*$",
    re.MULTILINE,
)


class CheckFailure(Exception):
    """A short, path-free explanation safe to include in the public summary."""


def code_only(text):
    """Blank nested Lean comments and strings, preserving line numbers."""
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
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            out[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            out[i] = " "
            i += 1
            while i < len(text):
                char = text[i]
                if char != "\n":
                    out[i] = " "
                i += 1
                if char == "\\" and i < len(text):
                    if text[i] != "\n":
                        out[i] = " "
                    i += 1
                elif char == '"':
                    break
        else:
            i += 1
    return "".join(out)


def expected_declarations(source):
    """Read the explicit, one-command-per-line audit list; fail if ambiguous."""
    code = code_only(source)
    names = re.findall(r"^\s*#print[ \t]+axioms[ \t]+(\S+)[ \t]*$", code, re.M)
    commands = re.findall(r"#print\s+axioms\b", code)
    if not names or len(names) != len(commands):
        raise CheckFailure("AxiomAudit.lean has an empty or unsupported audit list.")
    if len(names) != len(set(names)):
        raise CheckFailure("AxiomAudit.lean repeats an audited declaration.")
    return set(names)


def audit_output(expected, output):
    """Match names as well as counts, including names ending in apostrophes."""
    output = ANSI_ESCAPE.sub("", output).replace("\r\n", "\n")
    records = AXIOM_OUTPUT.findall(output)
    counts = Counter(name for name, _ in records)
    seen_axioms, unexpected = set(), {}
    for name, axiom_list in records:
        axioms = {axiom.strip() for axiom in axiom_list.split(",") if axiom.strip()}
        seen_axioms.update(axioms)
        forbidden = axioms - ALLOWED_AXIOMS
        if forbidden:
            unexpected.setdefault(name, set()).update(forbidden)
    result = {
        "expectedUniqueDeclarations": len(expected),
        "observedOutputs": len(records),
        "observedUniqueDeclarations": len(counts),
        "missingDeclarations": sorted(expected - counts.keys()),
        "unlistedDeclarations": sorted(counts.keys() - expected),
        "duplicateDeclarations": sorted(name for name, count in counts.items() if count != 1),
        "allowedAxioms": sorted(ALLOWED_AXIOMS),
        "observedAxioms": sorted(seen_axioms),
        "unexpectedAxioms": {name: sorted(axioms) for name, axioms in sorted(unexpected.items())},
        "sorryAxDetected": "sorryAx" in output,
    }
    result["status"] = "failed" if any(result[key] for key in (
        "missingDeclarations", "unlistedDeclarations", "duplicateDeclarations",
        "unexpectedAxioms", "sorryAxDetected",
    )) else "passed"
    return result


def lake_command(wrapper):
    if wrapper is None:
        return ["lake", "--no-cache"]
    path = Path(wrapper)
    if not path.is_absolute():
        path = ROOT / path
    if not path.is_file():
        raise CheckFailure("The requested Lake wrapper was not found.")
    if path.suffix.lower() == ".ps1":
        powershell = shutil.which("pwsh") or shutil.which("powershell")
        if not powershell:
            raise CheckFailure("A PowerShell executable is required for the Lake wrapper.")
        return [powershell, "-NoProfile", "-NonInteractive", "-File", str(path)]
    return [str(path)]


def run_stage(report, name, command):
    log_path = f"logs/proof-check-{name}.log"
    record = {"name": name, "status": "running", "log": log_path}
    report["stages"].append(record)
    print(f"Running {name}; output: {log_path}", flush=True)
    started = time.monotonic()
    env = os.environ.copy()
    env["NO_COLOR"] = "1"
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    try:
        with (ROOT / log_path).open("wb") as log:
            completed = subprocess.run(
                command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
                check=False,
            )
        record["exitCode"] = completed.returncode
        record["status"] = "passed" if completed.returncode == 0 else "failed"
        if completed.returncode:
            raise CheckFailure(f"The {name} command failed; see its local log.")
    except (OSError, KeyboardInterrupt):
        record["status"] = "failed"
        raise
    finally:
        record["elapsedSeconds"] = round(time.monotonic() - started, 3)
    return ROOT / log_path


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--lake-wrapper", metavar="PATH",
        help="invoke a Lake wrapper, e.g. ./lake-local.ps1 (relative to the source root)",
    )
    args = parser.parse_args(argv)
    report = {
        "schemaVersion": 1,
        "startedUtc": datetime.now(timezone.utc).isoformat(),
        "status": "running",
        "stages": [],
    }
    exit_code = 1
    try:
        (ROOT / "logs").mkdir(exist_ok=True)
        pins = {name: sha256(ROOT / name) for name in (
            "lean-toolchain", "lake-manifest.json", "lakefile.toml", "AxiomAudit.lean",
        )}
        report["inputSha256"] = pins
        toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8-sig").strip()
        if not re.fullmatch(r"leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(?:-[\w.-]+)?", toolchain):
            raise CheckFailure("The Lean toolchain is not an explicit supported release pin.")
        report["toolchain"] = toolchain
        expected = expected_declarations((ROOT / "AxiomAudit.lean").read_text(encoding="utf-8-sig"))
        report["expectedUniqueDeclarations"] = len(expected)
        lake = lake_command(args.lake_wrapper)
        layer_script = ROOT / "scripts/audit-layers.py"
        if not layer_script.is_file():
            raise CheckFailure("The source-layer checker is missing.")
        run_stage(report, "layers", [sys.executable, str(layer_script)])
        layers = json.loads((ROOT / "logs/layer-audit.json").read_text(encoding="utf-8-sig"))
        report["sourceLayers"] = {key: layers[key] for key in (
            "status", "projectModules", "layerModules", "statementRoot",
            "statementFirstPartyModules", "statementLayerModules",
        )}
        report["sourceLayers"]["report"] = "logs/layer-audit.json"
        if layers["status"] != "passed":
            raise CheckFailure("The Model/Statement/Proof import boundary check failed.")
        run_stage(report, "statement-build", lake + ["build", "QuantumOracle.Statement.Soundness"])
        run_stage(report, "build", lake + ["build"])
        # Lake 4.32 may keep dependency .oleans in its artifact store instead of
        # the package build tree. `lake lean` supplies their import setup; raw
        # `lake env lean` only supplies search paths and can miss those artifacts.
        audit_log = run_stage(report, "axioms", lake + ["lean", "AxiomAudit.lean"])
        report["axiomAudit"] = audit_output(expected, audit_log.read_text(encoding="utf-8", errors="replace"))
        if report["axiomAudit"]["status"] != "passed":
            raise CheckFailure("The axiom audit failed its declaration or dependency checks.")
        run_stage(report, "statement-review", lake + ["lean", "review/Statement.lean"])
        run_stage(report, "statement-verification", lake + ["lean", "review/VerifyStatement.lean"])

        closure_script = ROOT / "scripts/audit-source-closure.py"
        if not closure_script.is_file():
            raise CheckFailure("The source-closure checker is missing.")
        run_stage(report, "source", [sys.executable, str(closure_script)])
        closure = json.loads((ROOT / "logs/import-closure-audit.json").read_text(encoding="utf-8-sig"))
        report["sourceClosure"] = {key: closure[key] for key in (
            "status", "projectModules", "vendorModules", "checkedVendorFiles", "vendorCommit",
        )}
        report["sourceClosure"]["report"] = "logs/import-closure-audit.json"
        if closure["status"] != "passed":
            raise CheckFailure("The source-closure or vendored-source integrity check failed.")
        if any(sha256(ROOT / name) != digest for name, digest in pins.items()):
            raise CheckFailure("A pinned build input or the audit list changed during verification.")
        report["status"] = "passed"
        exit_code = 0
    except CheckFailure as exc:
        report.update(status="failed", failure=str(exc))
    except KeyboardInterrupt:
        report.update(status="interrupted", failure="Verification was interrupted.")
        exit_code = 130
    except Exception:
        report.update(status="failed", failure="Verification could not complete; see the local checker log.")
        try:
            (ROOT / "logs/proof-check-checker.log").write_text(traceback.format_exc(), encoding="utf-8")
        except OSError:
            pass
    report["finishedUtc"] = datetime.now(timezone.utc).isoformat()
    try:
        (ROOT / SUMMARY).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    except OSError:
        print("FAILED: Could not write the local verification summary.", file=sys.stderr)
        return 1
    if exit_code == 0:
        print(f"PASSED: {len(expected)} unique declarations; only allowed axioms; source layers and integrity verified.")
    else:
        print(f"{report['status'].upper()}: {report['failure']}", file=sys.stderr)
    print(f"Summary: {SUMMARY}")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
