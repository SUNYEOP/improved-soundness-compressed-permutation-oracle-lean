"""Render exact source excerpts for the theorem's declaration dependency slice.

Run in the original Lean checkout after ExtractDependencies.lean. This renders
reading material, not a new independently compilable implementation.
"""

import hashlib
import json
from pathlib import Path

REVIEW = Path(__file__).resolve().parent.parent
ROOT = REVIEW.parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


def bounds(node):
    r = node["sourceRange"]
    return ((r["startLine"], r["startColumn"]), (r["endLine"], r["endColumn"]))


def contains(outer, inner):
    return outer[0] <= inner[0] and inner[1] <= outer[1]


def main():
    report = json.loads((REVIEW / "semantic-dependencies.json").read_text(encoding="utf-8"))
    if report["missingDeclarations"]:
        raise ValueError("Dependency extractor reported missing declarations")
    declarations = report["declarations"]
    by_name = {d["name"]: d for d in declarations}
    if len(by_name) != len(declarations):
        raise ValueError("Repeated declaration in extraction")
    sources = {}
    for node in declarations:
        if not node["sourceRange"]:
            raise ValueError(f"No source range: {node['name']}")
        rel = node["source"]
        path = (ROOT / rel).resolve()
        if not path.is_relative_to(ROOT.resolve()):
            raise ValueError(f"Source outside checkout: {rel}")
        raw = path.read_bytes()
        sources[rel] = {"bytes": raw, "lines": raw.decode("utf-8-sig").splitlines(keepends=True)}

    def excerpt(node):
        lines = sources[node["source"]]["lines"]
        (sl, sc), (el, ec) = bounds(node)
        if not (1 <= sl <= el <= len(lines)):
            raise ValueError(f"Invalid source range: {node['name']}")
        if sc > len(lines[sl - 1].rstrip("\r\n")) or ec > len(lines[el - 1].rstrip("\r\n")):
            raise ValueError(f"Invalid source column: {node['name']}")
        if sl == el:
            return lines[sl - 1][sc:ec]
        return "".join([lines[sl - 1][sc:], *lines[sl:el - 1], lines[el - 1][:ec]])

    # Structure projections/constructors and compiler helpers may point inside
    # or inherit the same source command. Display its largest original range once.
    nonproof = [d for d in declarations if not d["isProof"]]
    unique = {}
    for node in nonproof:
        key = (node["source"], bounds(node))
        current = unique.get(key)
        if current is None or (node["name"] == node["sourceOwner"] and current["name"] != current["sourceOwner"]):
            unique[key] = node
    maximal = [n for key, n in unique.items() if not any(
        key[0] == other[0] and key[1] != other[1] and contains(other[1], key[1])
        for other in unique)]
    maximal.sort(key=lambda n: (n["source"], bounds(n)))
    owner = {}
    groups = []
    for i, node in enumerate(maximal, 1):
        members = sorted(n["name"] for n in nonproof if n["source"] == node["source"] and contains(bounds(node), bounds(n)))
        for name in members:
            if name in owner:
                raise ValueError(f"Overlapping source commands: {name}")
            owner[name] = i
        code = excerpt(node)
        groups.append({"id": i, "node": node, "members": members, "code": code})
    if set(owner) != {n["name"] for n in nonproof}:
        raise ValueError("Not every non-proof declaration has a source excerpt")

    def render_group(group, title_level=3):
        n, code = group["node"], group["code"]
        start, end = bounds(n)
        result = [f'<a id="source-{group["id"]}"></a>',
                  f'{"#" * title_level} `{n["sourceOwner"] or n["name"]}`', "",
                  f'Source: `{n["source"]}:{start[0]}–{end[0]}`. Classification: `{n["classification"]}`.', "",
                  "```lean", code, "```", ""]
        if len(group["members"]) > 1:
            result += ["<details>", "<summary>Corresponding declarations, including generated declarations and fields</summary>", "",
                       *[f"- `{name}`" for name in group["members"]], "", "</details>", ""]
        return result

    external_modules = sorted({n["module"] for n in report["externalBoundary"]})
    stats = {
        "localDeclarations": len(declarations),
        "proofObligationsIncludingEndpoint": sum(n["isProof"] for n in declarations),
        "nonProofDeclarations": len(nonproof),
        "sourceCommands": len(groups),
        "sourceFiles": len(sources),
        "sourceExcerptLines": sum(len(g["code"].splitlines()) for g in groups),
        "externalBoundaryDeclarations": len(report["externalBoundary"]),
        "externalModuleRoots": sorted({m.split(".")[0] for m in external_modules}),
    }
    output = ["# Complete definition dependencies", "",
              "This report starts from the final theorem's **type** and follows the types and data definitions of project declarations.",
              "For named proof declarations, it records the propositions without traversing the proof bodies.",
              "Proof fields and inline proof references within data definitions are included conservatively; the result is not a mathematically minimal dependency set.", "",
              f"Of the {len(declarations)} project declarations, {len(nonproof)} non-proof declarations are collected into the {len(groups)} source excerpts below.",
              f"The excerpts come from {len(sources)} source files. The propositions for {stats['proofObligationsIncludingEndpoint']} proof obligations appear separately below.",
              "Each excerpt depends on the namespace, variable, and instance context of its source file and is not a standalone compilation unit.",
              "Generated fields, constructors, and recursive auxiliary declarations are grouped with their source structure or definition.", "",
              "## Source definitions", ""]
    last_source = None
    for group in groups:
        if group["node"]["source"] != last_source:
            last_source = group["node"]["source"]
            output += [f"## `{last_source}`", ""]
        output += render_group(group)
    output += ["## Propositions of proof obligations", "",
               "The following are printed types from the extraction, with proof bodies omitted. They are reading material, not Lean declarations introducing new assumptions.",
               "The compiled implementation supplies proofs of these propositions. The final theorem is also included in this list.", ""]
    for node in sorted((d for d in declarations if d["isProof"]), key=lambda d: d["name"]):
        output += [f'### `{node["name"]}`', "", "```text", node["type"], "```", ""]
    output += ["## Library boundary", "",
               "The library implementations of the following declarations are not reproduced in this bundle.",
               "This boundary includes complex numbers, Euclidean norms, finite sums, orthogonal projections, and positive matrix square roots.",
               "Choice functions, coordinate enumerations, and instances remain recorded as their actual dependencies, without substituting other definitions.", "",
               "| Declaration | Module |", "| --- | --- |"]
    output += [f'| `{n["name"]}` | `{n["module"]}` |' for n in sorted(report["externalBoundary"], key=lambda n: n["name"])]
    (REVIEW / "DEFINITIONS.md").write_text("\n".join(output) + "\n", encoding="utf-8")

    core = ["# Core definitions: suggested reading order", "",
            "The following selection provides a reading order through the theorem's definitions. Each code block is an exact source excerpt.",
            "Additional auxiliary definitions appear in the [complete definition list](DEFINITIONS.md).",
            "The canonical theorem statement is defined in [Statement/Soundness.lean](../QuantumOracle/Statement/Soundness.lean).", ""]
    selected_names = []
    for section in json.loads((REVIEW / "tools/reading-order.json").read_text(encoding="utf-8")):
        core += [f'## {section["title"]}', "", section["description"], ""]
        for name in section["names"]:
            if name not in owner:
                raise ValueError(f"Core selection is not a non-proof semantic dependency: {name}")
            selected_names.append(name)
            group = groups[owner[name] - 1]
            core += render_group(group)
            core += [f'[Continue in the complete list](DEFINITIONS.md#source-{group["id"]})', ""]
    (REVIEW / "CORE_DEFINITIONS.md").write_text("\n".join(core) + "\n", encoding="utf-8")

    manifest = {
        "scope": report["scope"], "root": report["root"], "statistics": stats,
        "coreSelections": selected_names,
        "sources": [{"path": path, "sha256": sha(data["bytes"]), "bytes": len(data["bytes"])} for path, data in sorted(sources.items())],
        "excerpts": [{"source": g["node"]["source"], "range": g["node"]["sourceRange"],
                      "sourceOwner": g["node"]["sourceOwner"], "declarations": g["members"],
                      "sha256": sha(g["code"].encode("utf-8"))} for g in groups],
        "coveredDeclarations": sorted(by_name),
        "statementFileSha256": sha((REVIEW / "Statement.lean").read_bytes()),
        "canonicalStatement": {
            "path": "QuantumOracle/Statement/Soundness.lean",
            "sha256": sha((ROOT / "QuantumOracle/Statement/Soundness.lean").read_bytes()),
        },
        "verificationFileSha256": sha((REVIEW / "VerifyStatement.lean").read_bytes()),
        "semanticExtractionSha256": sha((REVIEW / "semantic-dependencies.json").read_bytes()),
    }
    (REVIEW / "SOURCE_MANIFEST.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(stats, indent=2))


if __name__ == "__main__":
    main()
