#!/usr/bin/env python3
"""Check the first-party import boundary between Model, Statement, and Proof.

This is a source-architecture audit, not a Lean parser or a kernel verifier.
All first-party module references must resolve to source files in this checkout.
Mathlib, its pinned Aesop tactic dependency, and Lean's own libraries are terminal
boundaries; Lake separately
checks external module availability during the build. No definition or proof
body is classified by this script.
"""

import argparse
from collections import Counter, deque
from datetime import datetime, timezone
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent.parent
STATEMENT = "QuantumOracle.Statement.Soundness"
LAYERS = ("Model", "Statement", "Proof")
TRUSTED_ROOTS = {"Mathlib", "Lean", "Std", "Init", "Aesop"}
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def code_only(text):
    """Blank nested comments and strings while preserving source offsets."""
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


def imports(text):
    """Read Lean 4.32's module header, including public/meta/import all.

    Each import takes one module name. Whitespace, including newlines, can
    separate header tokens. Unusual module identifiers fail explicitly instead
    of silently disappearing from the graph. Body commands are left to Lean.
    """
    code = code_only(text)
    pos = 0

    def skip_space():
        nonlocal pos
        while pos < len(code) and code[pos].isspace():
            pos += 1

    def take_word(wanted):
        nonlocal pos
        skip_space()
        match = WORD.match(code, pos)
        if match and match.group() == wanted:
            pos = match.end()
            return True
        return False

    take_word("module")
    take_word("prelude")
    result = []
    while True:
        skip_space()
        start = pos
        take_word("public")
        take_word("meta")
        if not take_word("import"):
            break
        take_word("all")
        skip_space()
        match = MODULE_NAME.match(code, pos)
        if not match or (match.end() < len(code) and not code[match.end()].isspace()):
            raise ValueError(f"Unsupported module identifier on line {code.count(chr(10), 0, pos) + 1}")
        result.append({"module": match.group(), "line": code.count("\n", 0, start) + 1})
        pos = match.end()
    return result


def layer(module):
    parts = module.split(".")
    return parts[1] if len(parts) > 2 and parts[1] in LAYERS else "Compatibility/Public"


def is_local(module):
    return module == "QuantumOracle" or module.startswith("QuantumOracle.")


def audit(root):
    root = root.resolve()
    files = sorted((root / "QuantumOracle").rglob("*.lean"))
    if (root / "QuantumOracle.lean").is_file():
        files.append(root / "QuantumOracle.lean")
    graph, paths, violations = {}, {}, []
    for path in files:
        relative = path.relative_to(root).as_posix()
        module = ".".join(path.relative_to(root).with_suffix("").parts)
        if not path.resolve().is_relative_to(root):
            violations.append({"kind": "unsafeSourcePath", "path": relative})
            continue
        if module in paths:
            violations.append({"kind": "duplicateModule", "module": module, "path": relative})
            continue
        paths[module] = relative
        try:
            graph[module] = imports(path.read_text(encoding="utf-8-sig"))
        except (OSError, UnicodeError, ValueError) as exc:
            violations.append({"kind": "unreadableImports", "module": module,
                               "path": relative, "detail": str(exc)})
            graph[module] = []

    for module, edges in sorted(graph.items()):
        source_layer = layer(module)
        for edge in edges:
            target = edge["module"]
            details = {"module": module, "path": paths[module], "line": edge["line"],
                       "import": target}
            if is_local(target) and target not in graph:
                violations.append({"kind": "missingFirstPartyModule", **details})
            if source_layer == "Compatibility/Public":
                continue
            allowed_layers = {"Model"}
            if source_layer in {"Statement", "Proof"}:
                allowed_layers.add("Statement")
            if source_layer == "Proof":
                allowed_layers.add("Proof")
            if is_local(target):
                allowed = layer(target) in allowed_layers
            else:
                allowed = source_layer == "Proof" or target.split(".")[0] in TRUSTED_ROOTS
            if not allowed:
                violations.append({"kind": "forbiddenLayerImport", **details,
                                   "sourceLayer": source_layer,
                                   "allowedFirstPartyLayers": sorted(allowed_layers)})

    counts = Counter(layer(module) for module in graph)
    for required in LAYERS:
        if not counts[required]:
            violations.append({"kind": "missingLayer", "layer": required})
    if STATEMENT not in graph:
        violations.append({"kind": "missingStatement", "module": STATEMENT})

    # Record complete paths from the public proposition so a leak through an
    # otherwise harmless-looking intermediate import is easy to diagnose.
    pending = deque([(STATEMENT, [STATEMENT])]) if STATEMENT in graph else deque()
    closure, external = set(), set()
    while pending:
        module, chain = pending.popleft()
        if module in closure:
            continue
        closure.add(module)
        if layer(module) not in {"Model", "Statement"}:
            violations.append({"kind": "statementProofLeak", "importPath": chain})
        for edge in graph.get(module, []):
            target = edge["module"]
            if is_local(target):
                if target in graph:
                    pending.append((target, chain + [target]))
            else:
                external.add(target)
                if target.split(".")[0] not in TRUSTED_ROOTS:
                    violations.append({"kind": "statementExternalLeak",
                                       "importPath": chain + [target]})

    report = {
        "schemaVersion": 1,
        "checkedUtc": datetime.now(timezone.utc).isoformat(),
        "scope": "All first-party source imports; Mathlib/Lean/Std/Init and pinned Aesop are terminal boundaries",
        "status": "failed" if violations else "passed",
        "projectModules": len(graph),
        "layerModules": {name: counts[name] for name in (*LAYERS, "Compatibility/Public")},
        "statementRoot": STATEMENT,
        "statementFirstPartyModules": len(closure),
        "statementLayerModules": dict(sorted(Counter(layer(module) for module in closure).items())),
        "statementModules": sorted(closure),
        "statementExternalImports": sorted(external),
        "violations": violations,
    }
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    report = audit(ROOT)
    output = ROOT / "logs/layer-audit.json"
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in {"statementModules", "statementExternalImports"}}, indent=2))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
