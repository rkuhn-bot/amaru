#!/usr/bin/env python3
# Copyright 2026 PRAGMA
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Discharge checker for a blocking-edge wait graph.

Reads a wait-graph JSON (an ``edges`` list of ``from``, ``to``, ``message``,
``blocking``) and an edge-discharge table next to it. The table is a JSON
object whose ``rows`` have:

* ``from``, ``to``, ``message`` — the edge
* ``edge`` — display name
* ``lemma`` — L1 credit/occupancy, L2 superseding cell, L3 ingress teardown,
  or L4 state-indexed
* ``w`` — occupancy bound
* ``capacity`` — mailbox the bound is compared with
* ``location`` — code location
* ``now`` and ``after`` — ``discharged`` or ``blocking``

``--mode now`` is the code as it is. ``--mode after`` is the same graph with
the proposed fixes applied only where a row says ``discharged``. The default
``both`` runs the two modes.

An edge is deleted for a mode only when its row says ``discharged``. The
checker then recomputes strongly connected components and exits 0 only when
every component is a single stage and no blocking self-loop remains. A
self-loop is its own cycle even though its component has size one. Exit 1
means a residual cycle. Exit 2 means the table does not cover a blocking edge
or a status is not one of the two words above.

Usage:
  scripts/wait-graph-sccs.py [--graph wait-graph-v4.json] [--discharge wait-graph-v4-discharge.json] [--mode now|after|both]
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path

MODES = ("now", "after")
STATUSES = {"discharged", "blocking"}


def tarjan(nodes: set[str], adj: dict[str, set[str]]) -> list[list[str]]:
    index = 0
    stack: list[str] = []
    on_stack: set[str] = set()
    indices: dict[str, int] = {}
    low: dict[str, int] = {}
    components: list[list[str]] = []

    def strong(node: str) -> None:
        nonlocal index
        indices[node] = index
        low[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)
        for nxt in sorted(adj.get(node, ())):
            if nxt not in indices:
                strong(nxt)
                low[node] = min(low[node], low[nxt])
            elif nxt in on_stack:
                low[node] = min(low[node], indices[nxt])
        if low[node] == indices[node]:
            component: list[str] = []
            while True:
                top = stack.pop()
                on_stack.remove(top)
                component.append(top)
                if top == node:
                    break
            components.append(sorted(component))

    for node in sorted(nodes):
        if node not in indices:
            strong(node)
    return components


def load(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def row_index(rows: list[dict]) -> dict[tuple[str, str, str], dict]:
    index: dict[tuple[str, str, str], dict] = {}
    for row in rows:
        for field in ("from", "to", "message", "edge", "lemma", "w", "capacity", "location", "now", "after"):
            if field not in row:
                raise SystemExit(f"discharge row missing {field}: {row.get('edge', row)}")
        for mode in MODES:
            if row[mode] not in STATUSES:
                raise SystemExit(f"{row['edge']}: {mode} status {row[mode]!r} is not discharged or blocking")
        key = (row["from"], row["to"], row["message"])
        if key in index:
            raise SystemExit(f"duplicate discharge row for {row['edge']}")
        index[key] = row
    return index


def select(edges: list[dict], index: dict[tuple[str, str, str], dict], mode: str) -> tuple[list[dict], list[dict]]:
    kept: list[dict] = []
    dropped: list[dict] = []
    for edge in edges:
        if not edge["blocking"]:
            continue
        key = (edge["from"], edge["to"], edge["message"])
        row = index.get(key)
        if row is None:
            raise SystemExit(
                f"blocking edge {edge['from']} -> {edge['to']} [{edge['message']}] has no discharge row"
            )
        if row[mode] == "discharged":
            dropped.append(edge)
        else:
            kept.append(edge)
    return kept, dropped


def components_of(kept: list[dict]) -> tuple[list[list[str]], list[dict]]:
    nodes: set[str] = set()
    adj: dict[str, set[str]] = defaultdict(set)
    loops: list[dict] = []
    for edge in kept:
        nodes.add(edge["from"])
        nodes.add(edge["to"])
        adj[edge["from"]].add(edge["to"])
        if edge["from"] == edge["to"]:
            loops.append(edge)
    large = [component for component in tarjan(nodes, adj) if len(component) > 1]
    large.sort(key=lambda component: (-len(component), component))
    return large, loops


def label(edge: dict) -> str:
    return f"{edge['from']} -> {edge['to']} [{edge['message']}]"


def report(mode: str, edges: list[dict], index: dict[tuple[str, str, str], dict]) -> bool:
    kept, dropped = select(edges, index, mode)
    large, loops = components_of(kept)
    print(f"mode {mode}")
    print(f"  blocking edges kept {len(kept)}")
    print(f"  blocking edges discharged {len(dropped)}")
    for edge in sorted(dropped, key=label):
        row = index[(edge["from"], edge["to"], edge["message"])]
        print(f"    drop {label(edge)} ({row['lemma']})")
    if not large and not loops:
        print("  every SCC is a single stage and no blocking self-loop remains")
        return True
    for component in large:
        members = set(component)
        inside = sorted({label(edge) for edge in kept if edge["from"] in members and edge["to"] in members})
        print(f"  residual SCC size {len(component)}: {', '.join(component)}")
        for line in inside:
            print(f"    {line}")
    for edge in sorted(loops, key=label):
        print(f"  residual self-loop: {label(edge)}")
    return False


def main() -> None:
    parser = argparse.ArgumentParser(description="Delete discharged wait-graph edges and recompute SCCs.")
    parser.add_argument("--graph", type=Path, default=Path("scripts/wait-graph-v5.json"))
    parser.add_argument("--discharge", type=Path, default=None)
    parser.add_argument("--mode", choices=("now", "after", "both"), default="both")
    args = parser.parse_args()
    discharge = args.discharge
    if discharge is None:
        discharge = args.graph.with_name(args.graph.stem + "-discharge.json")
    graph = load(args.graph)
    table = load(discharge)
    edges = graph["edges"]
    rows = table["rows"] if isinstance(table, dict) else table
    index = row_index(rows)
    print(f"commit {graph.get('commit', '')}")
    print(f"graph {args.graph}")
    print(f"discharge {discharge}")
    modes = MODES if args.mode == "both" else (args.mode,)
    ok = True
    for mode in modes:
        ok = report(mode, edges, index) and ok
        print()
    if not ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
