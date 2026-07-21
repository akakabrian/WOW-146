#!/usr/bin/env python3
"""Independent finite regression for WOWII Conjecture 146.

Enumerates every connected unlabeled graph with 2 through 7 vertices from
NetworkX's Graph Atlas, computes the conjecture invariants from first
principles, and checks both the full inequality and the exceptional case.
"""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter
from pathlib import Path
from typing import Any

import networkx as nx

EXPECTED_CONNECTED_COUNTS = {2: 1, 3: 2, 4: 6, 5: 21, 6: 112, 7: 853}


def largest_induced_tree_size(graph: nx.Graph) -> int:
    """Return the maximum order of an induced subtree, by exhaustive search."""
    vertices = tuple(graph.nodes())
    for size in range(len(vertices), 0, -1):
        for subset in itertools.combinations(vertices, size):
            if nx.is_tree(graph.subgraph(subset)):
                return size
    raise AssertionError("A nonempty graph must contain a one-vertex induced tree")


def graph_invariants(graph: nx.Graph) -> dict[str, Any]:
    distances = dict(nx.all_pairs_shortest_path_length(graph))
    eccentricities = {
        vertex: max(distances[vertex].values()) for vertex in graph.nodes()
    }
    diameter = max(eccentricities.values())
    radius = min(eccentricities.values())
    periphery = tuple(
        vertex for vertex, eccentricity in eccentricities.items()
        if eccentricity == diameter
    )
    periphery_eccentricity = max(
        min(distances[vertex][boundary] for boundary in periphery)
        for vertex in graph.nodes()
    )

    square = nx.Graph()
    square.add_nodes_from(graph.nodes())
    for u, v in itertools.combinations(graph.nodes(), 2):
        if distances[u][v] <= 2:
            square.add_edge(u, v)
    square_radius = nx.radius(square)
    induced_tree_size = largest_induced_tree_size(graph)

    return {
        "radius": radius,
        "diameter": diameter,
        "periphery": list(periphery),
        "periphery_eccentricity": periphery_eccentricity,
        "square_radius": square_radius,
        "largest_induced_tree_size": induced_tree_size,
        "lhs": 2 * periphery_eccentricity,
        "rhs": induced_tree_size * square_radius,
    }


def spider_witness() -> nx.Graph:
    graph = nx.Graph()
    graph.add_nodes_from(range(6))
    graph.add_edges_from([(0, 1), (1, 2), (2, 3), (3, 4), (2, 5)])
    return graph


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", type=Path, required=True)
    args = parser.parse_args()

    connected_by_order: Counter[int] = Counter()
    checked = 0
    exceptional_count = 0
    failures: list[dict[str, Any]] = []
    exceptional_failures: list[dict[str, Any]] = []
    minimum_slack: int | None = None
    minimum_slack_examples: list[dict[str, Any]] = []
    spider_found = False
    spider = spider_witness()

    for atlas_index, graph in enumerate(nx.graph_atlas_g()):
        order = graph.number_of_nodes()
        if order < 2 or order > 7 or not nx.is_connected(graph):
            continue

        connected_by_order[order] += 1
        checked += 1
        invariants = graph_invariants(graph)
        graph6 = nx.to_graph6_bytes(graph, header=False).decode("ascii").strip()
        record = {
            "atlas_index": atlas_index,
            "order": order,
            "graph6": graph6,
            **invariants,
        }

        if invariants["square_radius"] <= 0:
            failures.append({**record, "reason": "nonpositive square radius"})

        slack = invariants["rhs"] - invariants["lhs"]
        if minimum_slack is None or slack < minimum_slack:
            minimum_slack = slack
            minimum_slack_examples = [record]
        elif slack == minimum_slack and len(minimum_slack_examples) < 20:
            minimum_slack_examples.append(record)

        if invariants["lhs"] > invariants["rhs"]:
            failures.append({**record, "reason": "conjecture inequality failed"})

        exceptional = (
            invariants["radius"] == 2
            and invariants["diameter"] == 4
            and invariants["periphery_eccentricity"] == 3
        )
        if exceptional:
            exceptional_count += 1
            if invariants["largest_induced_tree_size"] < 6:
                exceptional_failures.append(record)

        if order == 6 and nx.is_isomorphic(graph, spider):
            spider_found = True
            expected = {
                "radius": 2,
                "diameter": 4,
                "periphery_eccentricity": 3,
                "largest_induced_tree_size": 6,
            }
            for key, value in expected.items():
                if invariants[key] != value:
                    failures.append({
                        **record,
                        "reason": f"spider witness has {key}={invariants[key]}, expected {value}",
                    })

    counts = {order: connected_by_order[order] for order in range(2, 8)}
    completeness_failures = {
        order: {"observed": counts[order], "expected": expected}
        for order, expected in EXPECTED_CONNECTED_COUNTS.items()
        if counts[order] != expected
    }
    if checked != sum(EXPECTED_CONNECTED_COUNTS.values()):
        completeness_failures["total"] = {
            "observed": checked,
            "expected": sum(EXPECTED_CONNECTED_COUNTS.values()),
        }
    if not spider_found:
        failures.append({"reason": "six-vertex spider witness missing from atlas"})

    report = {
        "source": "NetworkX graph_atlas_g: one representative of every unlabeled graph with at most seven vertices",
        "orders_checked": [2, 3, 4, 5, 6, 7],
        "connected_graph_counts": counts,
        "expected_connected_graph_counts": EXPECTED_CONNECTED_COUNTS,
        "total_connected_nontrivial_graphs_checked": checked,
        "exceptional_graph_count": exceptional_count,
        "minimum_inequality_slack": minimum_slack,
        "minimum_slack_examples": minimum_slack_examples,
        "spider_witness_found": spider_found,
        "completeness_failures": completeness_failures,
        "inequality_failures": failures,
        "exceptional_failures": exceptional_failures,
        "result": "PASS" if not (completeness_failures or failures or exceptional_failures) else "FAIL",
    }

    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["result"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
