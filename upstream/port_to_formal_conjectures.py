#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path

UPSTREAM_REV = "b8b5208aa5d01f5f91c49ca516bf09cae8d93693"
W142_REV = "46bf39015f5c3c3ba3bfcf9f752b4b1e49b584ac"
PROOF_URL = "https://github.com/akakabrian/WOW-146/commit/0b750ac1ac987d7085fff796b4ea91a0cf4ecd70"
W142_REL = Path("FormalConjecturesForMathlib/WrittenOnTheWallII/GraphConjecture142Proof.lean")
INDEX_REL = Path("FormalConjecturesForMathlib.lean")
PREFIX = "FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146"
DEST_REL = Path("FormalConjecturesForMathlib/WrittenOnTheWallII/GraphConjecture146")
SOURCE_MODULES = [
    "GraphSquareMetric", "GraphSquareRadius", "GlobalBounds", "Metric",
    "Exceptional", "ExceptionalTheorem", "Reduction",
    "GraphConjecture146Proof", "Regression",
]
COPYRIGHT = '''/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
'''


def moduleize(text: str) -> str:
    if re.search(r"(?m)^module\s*$", text):
        return text
    lines = text.splitlines()
    import_indices = [i for i, line in enumerate(lines) if line.startswith("import ")]
    if not import_indices:
        raise RuntimeError("file has no import block")
    first_import = import_indices[0]
    lines.insert(first_import, "module")
    for i in range(first_import + 1, len(lines)):
        if lines[i].startswith("import "):
            lines[i] = "public " + lines[i]
    doc_index = next(
        (i for i in range(first_import + 1, len(lines)) if lines[i].startswith("/-!")),
        None,
    )
    if doc_index is None:
        raise RuntimeError("file has no module docstring")
    lines[doc_index:doc_index] = ["@[expose] public section", ""]
    return "\n".join(lines) + "\n"


def common_transform(text: str) -> str:
    text = text.replace("Copyright 2026 The WOW-146 Authors.",
                        "Copyright 2026 The Formal Conjectures Authors.")
    text = text.replace("http://www.apache.org/licenses/LICENSE-2.0",
                        "https://www.apache.org/licenses/LICENSE-2.0")
    for module in SOURCE_MODULES:
        text = text.replace(f"import WOW146.{module}", f"import {PREFIX}.{module}")
    text = text.replace("WOW146", "WrittenOnTheWallII.GraphConjecture146.Proof")
    text = re.sub(r"(?m)^#print axioms .*\n", "", text)
    text = re.sub(r"(?m)^#check .*\n", "", text)
    return text


def transform_graph_square_radius(text: str) -> str:
    text = text.replace("import FormalConjectures.WrittenOnTheWallII.GraphConjecture146\n", "")
    text = text.replace("open WrittenOnTheWallII.GraphConjecture146\n", "")
    text = re.sub(
        r"\n/-- The project invariant `graphSquareRadius`.*?\n"
        r"theorem graphSquareRadius_eq \(hG : G\.Connected\) :\n"
        r"    graphSquareRadius G = \(G\.radius\.toNat \+ 1\) / 2 := by\n"
        r"  unfold graphSquareRadius\n"
        r"  exact graphSquare_radius_toNat hG\n",
        "\n", text, flags=re.DOTALL)
    return text


def transform_metric(text: str) -> str:
    return text.replace("open WrittenOnTheWallII.GraphConjecture146\n", "").replace(
        "graphSquareRadius G", "(graphSquare G).radius.toNat")


def transform_exceptional(text: str) -> str:
    return text.replace("open WrittenOnTheWallII.GraphConjecture146\n", "")


def transform_exceptional_theorem(text: str) -> str:
    text = text.replace("open WrittenOnTheWallII.GraphConjecture146\n", "")
    text = text.replace("graphSquareRadius_eq hG", "graphSquare_radius_toNat hG")
    return text.replace("graphSquareRadius G", "(graphSquare G).radius.toNat")


def transform_reduction(text: str) -> str:
    text = text.replace("open WrittenOnTheWallII.GraphConjecture146\n", "")
    text = text.replace("graphSquareRadius_eq hG", "graphSquare_radius_toNat hG")
    return text.replace("graphSquareRadius G", "(graphSquare G).radius.toNat")


def transform_proof(text: str) -> str:
    text = text.replace("open WrittenOnTheWallII.GraphConjecture146\n", "")
    return text.replace("graphSquareRadius G", "(graphSquare G).radius.toNat")


def transform_module(name: str, text: str) -> str:
    text = common_transform(text)
    transforms = {
        "GraphSquareRadius": transform_graph_square_radius,
        "Metric": transform_metric,
        "Exceptional": transform_exceptional,
        "ExceptionalTheorem": transform_exceptional_theorem,
        "Reduction": transform_reduction,
        "GraphConjecture146Proof": transform_proof,
    }
    if name in transforms:
        text = transforms[name](text)
    if "import WOW146." in text or "graphSquareRadius G" in text:
        raise RuntimeError(f"unported reference in {name}")
    return moduleize(text)


def restore_w142(upstream: Path) -> None:
    destination = upstream / W142_REL
    if destination.exists():
        return
    content = subprocess.check_output(
        ["git", "show", f"{W142_REV}:{W142_REL.as_posix()}"], cwd=upstream,
        text=True)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(moduleize(content))


def patch_index(index: Path) -> None:
    text = index.read_text()
    imports = [
        "public import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture142Proof",
        f"public import {PREFIX}.GraphConjecture146Proof",
        f"public import {PREFIX}.Regression",
    ]
    missing = [line for line in imports if line not in text]
    if missing:
        index.write_text(text.rstrip() + "\n" + "\n".join(missing) + "\n")


def patch_target(target: Path) -> None:
    text = target.read_text()
    proof_import = f"import {PREFIX}.GraphConjecture146Proof"
    if proof_import not in text:
        text = text.replace("import FormalConjecturesUtil\n",
                            f"import FormalConjecturesUtil\n{proof_import}\n", 1)
    attribute = (
        "@[category research solved, AMS 5, formal_proof using lean4 at "
        f'"{PROOF_URL}"]')
    text = text.replace("@[category research open, AMS 5]", attribute, 1)
    old = "    largestInducedTreeSize G * graphSquareRadius G := by\n  sorry\n"
    new = (
        "    largestInducedTreeSize G * graphSquareRadius G := by\n"
        "  unfold graphSquareRadius at hrad ⊢\n"
        "  exact Proof.conjecture146 G h hrad\n")
    if old not in text:
        raise RuntimeError("unexpected upstream theorem body")
    target.write_text(text.replace(old, new, 1))


def write_audit(destination: Path) -> None:
    destination.write_text(COPYRIGHT + f'''
import FormalConjectures.WrittenOnTheWallII.GraphConjecture146
import {PREFIX}.Regression

/-!
# Axiom audit for Written on the Wall II Conjecture 146

Checks the exact upstream theorem, its raw proof theorem, the exceptional lemma,
and the explicit regression witness.
-/

#check WrittenOnTheWallII.GraphConjecture146.conjecture146
#check WrittenOnTheWallII.GraphConjecture146.Proof.conjecture146
#print axioms WrittenOnTheWallII.GraphConjecture146.conjecture146
#print axioms WrittenOnTheWallII.GraphConjecture146.Proof.conjecture146
#print axioms WrittenOnTheWallII.GraphConjecture146.Proof.exceptional_case
#print axioms WrittenOnTheWallII.GraphConjecture146.Proof.Regression.reg_exceptional
''')


def write_patch(upstream: Path, destination: Path) -> None:
    subprocess.run(["git", "add", "-N", W142_REL.as_posix(), DEST_REL.as_posix()],
                   cwd=upstream, check=True)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(subprocess.check_output(
        ["git", "diff", "--binary", "--full-index"], cwd=upstream))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--patch", type=Path)
    parser.add_argument("--expect-rev", default=UPSTREAM_REV)
    args = parser.parse_args()
    source, upstream = args.source.resolve(), args.upstream.resolve()
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"],
                                     cwd=upstream, text=True).strip()
    if actual != args.expect_rev:
        raise RuntimeError(f"expected {args.expect_rev}, found {actual}")
    restore_w142(upstream)
    destination = upstream / DEST_REL
    destination.mkdir(parents=True, exist_ok=True)
    for name in SOURCE_MODULES:
        original = (source / "WOW146" / f"{name}.lean").read_text()
        (destination / f"{name}.lean").write_text(transform_module(name, original))
    write_audit(destination / "Audit.lean")
    patch_index(upstream / INDEX_REL)
    patch_target(upstream / "FormalConjectures/WrittenOnTheWallII/GraphConjecture146.lean")
    if args.patch:
        write_patch(upstream, args.patch.resolve())
    print(f"Ported {len(SOURCE_MODULES)} modules; upstream base {actual}")
    print(f"W142 prerequisite source {W142_REV}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
