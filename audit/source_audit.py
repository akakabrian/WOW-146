#!/usr/bin/env python3
"""Audit the local transitive Lean proof surface for forbidden placeholders."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ENTRY = ROOT / "WOW146.lean"
FORBIDDEN = re.compile(r"\b(sorry|admit|native_decide|axiom)\b")
IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", re.MULTILINE)


def strip_comments_and_strings(text: str) -> str:
    """Remove nested Lean comments, line comments, chars, and strings."""
    output: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    in_char = False
    while i < len(text):
        pair = text[i:i + 2]
        char = text[i]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                i += 2
            elif pair == "-/":
                block_depth -= 1
                i += 2
            else:
                i += 1
            continue
        if in_string:
            if char == "\\":
                i += 2
            elif char == '"':
                in_string = False
                i += 1
            else:
                i += 1
            continue
        if in_char:
            if char == "\\":
                i += 2
            elif char == "'":
                in_char = False
                i += 1
            else:
                i += 1
            continue
        if pair == "/-":
            block_depth = 1
            i += 2
        elif pair == "--":
            newline = text.find("\n", i + 2)
            i = len(text) if newline == -1 else newline + 1
            output.append("\n")
        elif char == '"':
            in_string = True
            i += 1
        elif char == "'":
            in_char = True
            i += 1
        else:
            output.append(char)
            i += 1
    if block_depth or in_string or in_char:
        raise ValueError("unterminated comment or literal while scanning Lean source")
    return "".join(output)


def module_path(module: str) -> Path | None:
    if not module.startswith("WOW146"):
        return None
    if module == "WOW146":
        return ROOT / "WOW146.lean"
    return ROOT / (module.replace(".", "/") + ".lean")


def reachable_local_files(entry: Path) -> list[Path]:
    pending = [entry]
    visited: set[Path] = set()
    while pending:
        path = pending.pop()
        path = path.resolve()
        if path in visited:
            continue
        if not path.exists():
            raise FileNotFoundError(path)
        visited.add(path)
        source = strip_comments_and_strings(path.read_text())
        for module in IMPORT.findall(source):
            imported = module_path(module)
            if imported is not None:
                pending.append(imported)
    return sorted(visited)


def main() -> int:
    files = reachable_local_files(ENTRY)
    findings: list[dict[str, object]] = []
    for path in files:
        clean = strip_comments_and_strings(path.read_text())
        for match in FORBIDDEN.finditer(clean):
            line = clean.count("\n", 0, match.start()) + 1
            findings.append({
                "file": str(path.relative_to(ROOT)),
                "line": line,
                "token": match.group(1),
            })

    report = {
        "entry": str(ENTRY.relative_to(ROOT)),
        "reachable_local_files": [str(path.relative_to(ROOT)) for path in files],
        "reachable_local_file_count": len(files),
        "forbidden_tokens": ["sorry", "admit", "native_decide", "axiom"],
        "findings": findings,
        "result": "PASS" if not findings else "FAIL",
        "note": (
            "External Formal Conjectures imports may contain unrelated open problems. "
            "Kernel dependency is checked separately with #print axioms on WOW146.conjecture146."
        ),
    }
    report_path = ROOT / "audit" / "source_audit_report.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if not findings else 1


if __name__ == "__main__":
    sys.exit(main())
