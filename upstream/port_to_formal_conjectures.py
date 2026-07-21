#!/usr/bin/env python3
"""Port the verified standalone WOWII 146 proof into a Formal Conjectures checkout.

The standalone project imports the conjecture statement to reuse its
`graphSquareRadius` definition. Importing the finished proof back into that same
statement would create a cycle. The upstream port therefore proves an equivalent
raw theorem using `(graphSquare G).radius.toNat`; the conjecture file unfolds its
local abbreviation before applying the proof.

The audited proof also uses general induced-tree and periphery lemmas developed
in the verified W142 proof branch. Those lemmas are not present on current
upstream `main`, so the port carries that already kernel-checked prerequisite
module from its immutable source commit.
"""

from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path

UPSTREAM_REV = "b8b5208aa5d01f5f91c49ca516bf09cae8d93693"
W142_REV = "46bf39015f5c3c3ba3bfcf9f752b4b1e49b584ac"
W142_REL = Path(
    "FormalConjecturesForMathlib/WrittenOnTheWallII/GraphConjecture142Proof.lean"
)
PREFIX = "FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146"
DEST_REL = Path("FormalConjecturesForMathlib/WrittenOnTheWallII/GraphConjecture146")
SOURCE_MODULES = [
    "GraphSquareMetric",
    "GraphSquareRadius",
    "GlobalBounds",
    "Metric",
    "Exceptional",
    "ExceptionalTheorem",
    "Reduction",
    "GraphConjecture146Proof",
    "Regression",
]


def common_transform(text: str) -> str:
    text = text.replace(
        "Copyright 2026 The WOW-146 Authors.",
        "Copyright 2026 The Formal Conjectures Authors.",
    )
    text = text.replace(
        "http://www.apache.org/licenses/LICENSE-2.0",
        "https://www.apache.org/licenses/LICENSE-2.0",
    )
    for module in SOURCE_MODULES:
        text = text.replace(f"import WOW146.{module}", f"import {PREFIX}.{module}")
    text = text.replace("WOW146", "WrittenOnTheWallII.GraphConjecture146.Proof")
    return text


def transform_graph_square_radius(text: str) -> str:
    text = text.replace(
        "import FormalConjectures.WrittenOnTheWallII.GraphConjecture146\n", ""
    )
    text = text.replace("open WrittenOnTheWallII.GraphConjecture146\n", "")
    text = re.sub(
        r"\n/-- The project invariant `graphSquareRadius`.*?\n"
        r"theorem graphSquareRadius_eq \(hG : G\.Connected\) :\n"
        r"    graphSquareRadius G = \(G\.radius\.toNat \+ 1\) / 2 := by\n"
        r"  unfold graphSquareRadius\n"
        r"  exact graphSquare_radius_toNat hG\n",
        "\n",
        text,
        flags=re.DOTALL,
    )
    text = text.replace(
        "#print axioms graphSquareRadius_eq", "#print axioms graphSquare_radius_toNat"
    )
    return text


def transform_metric(text: str) -> str:
    text = text.replace("open WrittenOnTheWallII.GraphConjecture146\n", "")
    return text.replace("graphSquareRadius G", "(graphSquare G).radius.toNat")


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
    text = text.replace("graphSquareRadius G", "(graphSquare G).radius.toNat")
    text = re.sub(
        r"\n#check WrittenOnTheWallII\.GraphConjecture146\.conjecture146\n", "\n", text
    )
    return text


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
        raise RuntimeError(f"unported standalone reference remains in {name}")
    return text


def restore_w142_prerequisite(upstream: Path) -> None:
    destination = upstream / W142_REL
    if destination.exists():
        return
    content = subprocess.check_output(
        ["git", "show", f"{W142_REV}:{W142_REL.as_posix()}"],
        cwd=upstream,
    )
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(content)


def patch_target(target: Path) -> None:
    text = target.read_text()
    import_line = f"import {PREFIX}.GraphConjecture146Proof"
    if import_line not in text:
        text = text.replace(
            "import FormalConjecturesUtil\n",
            f"import FormalConjecturesUtil\n{import_line}\n",
            1,
        )
    text = text.replace(
        "@[category research open, AMS 5]", "@[category research solved, AMS 5]", 1
    )
    old = """    largestInducedTreeSize G * graphSquareRadius G := by
  sorry
"""
    new = """    largestInducedTreeSize G * graphSquareRadius G := by
  unfold graphSquareRadius at hrad ⊢
  exact Proof.conjecture146 G h hrad
"""
    if old not in text:
        raise RuntimeError("upstream conjecture body no longer matches expected open statement")
    target.write_text(text.replace(old, new, 1))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True, help="WOW-146 checkout")
    parser.add_argument("--upstream", type=Path, required=True, help="Formal Conjectures checkout")
    parser.add_argument("--patch", type=Path, help="write git diff here after porting")
    parser.add_argument("--expect-rev", default=UPSTREAM_REV)
    args = parser.parse_args()

    source = args.source.resolve()
    upstream = args.upstream.resolve()
    actual_rev = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=upstream, text=True
    ).strip()
    if actual_rev != args.expect_rev:
        raise RuntimeError(f"expected upstream {args.expect_rev}, found {actual_rev}")

    restore_w142_prerequisite(upstream)

    destination = upstream / DEST_REL
    destination.mkdir(parents=True, exist_ok=True)
    for name in SOURCE_MODULES:
        original = (source / "WOW146" / f"{name}.lean").read_text()
        (destination / f"{name}.lean").write_text(transform_module(name, original))

    target = upstream / "FormalConjectures/WrittenOnTheWallII/GraphConjecture146.lean"
    patch_target(target)

    if args.patch:
        args.patch.parent.mkdir(parents=True, exist_ok=True)
        diff = subprocess.check_output(["git", "diff", "--binary"], cwd=upstream)
        args.patch.write_bytes(diff)

    print(f"Ported {len(SOURCE_MODULES)} WOWII 146 modules into {upstream}")
    print(f"Restored W142 prerequisite from {W142_REV}")
    print(f"Upstream base: {actual_rev}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
