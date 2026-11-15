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

"""Strongly connected components of a blocking-edge wait graph.

Reads a JSON object with an ``edges`` list. Each edge has ``from``, ``to``,
``blocking``, and optionally ``discharged``. Prints every component of more
than one stage, first over every blocking edge, then again after dropping
edges marked discharged.

Usage: scripts/wait-graph-sccs.py wait-graph-v3.json
"""

from __future__ import annotations

import json
import sys
from collections import defaultdict


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


def graph(edges: list[dict], drop_discharged: bool) -> tuple[set[str], dict[str, set[str]]]:
    nodes: set[str] = set()
    adj: dict[str, set[str]] = defaultdict(set)
    for edge in edges:
        if not edge["blocking"]:
            continue
        if drop_discharged and edge.get("discharged"):
            nodes.add(edge["from"])
            nodes.add(edge["to"])
            continue
        adj[edge["from"]].add(edge["to"])
        nodes.add(edge["from"])
        nodes.add(edge["to"])
    return nodes, adj


def report(title: str, edges: list[dict], drop_discharged: bool) -> None:
    nodes, adj = graph(edges, drop_discharged)
    components = [component for component in tarjan(nodes, adj) if len(component) > 1]
    components.sort(key=lambda component: (-len(component), component))
    print(title)
    if not components:
        print("  (no component larger than one stage)")
        return
    for component in components:
        inside = []
        members = set(component)
        for edge in edges:
            if not edge["blocking"]:
                continue
            if drop_discharged and edge.get("discharged"):
                continue
            if edge["from"] in members and edge["to"] in members and edge["from"] != edge["to"]:
                inside.append(f"{edge['from']} -> {edge['to']} [{edge.get('message', '')}]")
        print(f"  size {len(component)}: {', '.join(component)}")
        for line in sorted(set(inside)):
            print(f"    {line}")


def main() -> None:
    path = sys.argv[1] if len(sys.argv) > 1 else "/opt/cursor/artifacts/wait-graph-v3.json"
    with open(path, encoding="utf-8") as handle:
        document = json.load(handle)
    edges = document["edges"]
    commit = document.get("commit", "")
    print(f"commit {commit}")
    print(f"blocking edges {sum(1 for edge in edges if edge['blocking'])}")
    report("sccs blocking", edges, drop_discharged=False)
    report("sccs blocking, discharged edges removed", edges, drop_discharged=True)


if __name__ == "__main__":
    main()
