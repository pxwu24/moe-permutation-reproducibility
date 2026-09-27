#!/usr/bin/env python3
"""Plan a source-only proof build and generate its exhaustive axiom audit."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


EXTERNAL_PREFIXES = {
    "Aesop", "Batteries", "Init", "Lean", "LeanSearchClient", "Mathlib",
    "Physlib", "PhyslibAlpha", "Plausible", "ProofWidgets", "Qq", "QuantumInfo",
    "Std", "ImportGraph",
}


def without_comments(text: str) -> str:
    """Remove nested Lean comments while retaining line positions and strings."""
    out: list[str] = []
    index = 0
    depth = 0
    quoted = False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1
                out.extend("  ")
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif quoted:
            char = text[index]
            out.append(char)
            index += 1
            if char == "\\" and index < len(text):
                out.append(text[index])
                index += 1
            elif char == '"':
                quoted = False
        elif text.startswith("/-", index):
            depth = 1
            out.extend("  ")
            index += 2
        elif text.startswith("--", index):
            stop = text.find("\n", index)
            if stop == -1:
                stop = len(text)
            out.extend(" " * (stop - index))
            index = stop
        else:
            char = text[index]
            out.append(char)
            quoted = char == '"'
            index += 1
    if depth:
        raise ValueError("Unclosed Lean block comment")
    return "".join(out)


def imports(path: Path) -> list[str]:
    code = without_comments(path.read_text(encoding="utf-8"))
    result = []
    for match in re.finditer(r"^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)", code, re.M):
        for module in match.group(1).split():
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", module):
                raise ValueError(f"Unsupported import syntax in {path}: {module!r}")
            result.append(module)
    return result


def proof_plan(project: Path) -> tuple[list[str], dict[str, list[str]]]:
    sources = {p.stem: p for p in project.glob("*.lean")}
    if not sources:
        raise ValueError(f"No proof sources in {project}")
    dependencies = {name: imports(path) for name, path in sources.items()}
    for name, imported in dependencies.items():
        for module in imported:
            if module not in sources and module.split(".")[0] not in EXTERNAL_PREFIXES:
                raise ValueError(f"{name}.lean imports missing local proof module {module}")
    visiting: set[str] = set()
    finished: set[str] = set()
    ordered: list[str] = []

    def visit(name: str) -> None:
        if name in finished:
            return
        if name in visiting:
            raise ValueError(f"Cyclic proof imports involving {name}")
        visiting.add(name)
        for dependency in sorted(dependencies[name]):
            if dependency in sources:
                visit(dependency)
        visiting.remove(name)
        finished.add(name)
        ordered.append(name)

    for name in sorted(sources):
        visit(name)
    return ordered, dependencies


def generate(project: Path, output: Path) -> None:
    modules, dependencies = proof_plan(project)
    output.mkdir(parents=True, exist_ok=True)
    (output / "proof_modules.txt").write_text("\n".join(modules) + "\n", encoding="utf-8")
    external = sorted({module for deps in dependencies.values() for module in deps
                       if module not in dependencies})
    targets = [module for module in external
               if module.split(".")[0] in {"QuantumInfo", "Physlib", "PhyslibAlpha"}]
    (output / "physlib_targets.txt").write_text("\n".join(targets) + "\n", encoding="utf-8")
    template = (project / "scripts/axiom_audit.lean.in").read_text(encoding="utf-8")
    audit = template.replace("@@IMPORTS@@", "\n".join(f"import {name}" for name in modules))
    audit = audit.replace("@@MODULE_NAMES@@", ", ".join(f'Name.mkSimple "{name}"' for name in modules))
    (output / "SupplementAxiomAudit.lean").write_text(audit, encoding="utf-8")
    metadata = {
        "modules": modules,
        "imports": dependencies,
        "sha256": {f"{module}.lean": hashlib.sha256((project / f"{module}.lean").read_bytes()).hexdigest()
                   for module in modules},
    }
    (output / "source_manifest.json").write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")


def cache_modules(project: Path, physlib: Path) -> list[str]:
    _, dependencies = proof_plan(project)
    pending = [module for deps in dependencies.values() for module in deps if module not in dependencies]
    visited: set[str] = set()
    cache: set[str] = set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        prefix = module.split(".")[0]
        if prefix in {"QuantumInfo", "Physlib", "PhyslibAlpha"}:
            path = physlib / (module.replace(".", "/") + ".lean")
            if not path.is_file():
                raise ValueError(f"Missing pinned Physlib source {path}")
            pending.extend(imports(path))
        elif prefix not in {"Init", "Lean", "Std"}:
            cache.add(module)
    return sorted(cache)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["plan", "cache"])
    parser.add_argument("project", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    if args.command == "plan":
        generate(args.project.resolve(), args.destination.resolve())
    else:
        print("\n".join(cache_modules(args.project.resolve(), args.destination.resolve())))


if __name__ == "__main__":
    main()
