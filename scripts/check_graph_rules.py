#!/usr/bin/env python3
"""Check the mechanical rules of the ATLAS graph (docs/BLUEPRINT.md, "Graph rules").

    python scripts/check_graph_rules.py                 report every finding on the committed tree
    python scripts/check_graph_rules.py --base BASE     fail on findings BASE doesn't have, and on PR size

It reads the committed tree only, so it runs before `sync_wiki.py lean-facts`
adds the Lean's facts to the checkout. `autoform check` and the site checks
still judge the graph as a whole; this script checks what they leave to the
wiki's own conventions:

- rule 5: every annotation names one existing page under blueprint/roadmap/,
  in the links file of that page's subject, and at most one annotation names
  a page; an annotation names at most one Lean declaration; an `id`, where a
  row has one, is well formed and unique (a missing one is not a finding
  until the one-off fill, #5524);
- rule 1: every subject folder is a subject in scripts/taxonomy.json, and a
  subject with fields has only field folders;
- rule 2: every page and folder is listed on its parent folder page
  (`sync_wiki.py lean-facts` already stops on a page with no annotation row);
- no page tied to a Lean declaration commits `## Depends on` or `## Proof
  depends on`, which lean-facts writes at build time; a planned page, whose
  annotation has no Lean link, may (rules 9 and 10);
- `## Informally uses` links existing pages, never the page itself, and closes
  no cycle (rule 11). `autoform check` only warns on these, so a passing check
  does not show that an expansion repointed every informal link (rule 13).
  Edges are read with Autoform's own parser;
- a node still to be broken down (`"org.autoform": {"not_ready": true}`, rule
  12) names no declaration and is an article, not a folder page, and the flag
  is a JSON boolean (Autoform silently drops any other value);
- rule 8: no build output is committed;
- rule 15, with --base: the PR changes fewer than 3,000 files.

With --base, a PR fails only on findings the base commit doesn't already have:
a finding already on main is printed as a warning, so the check blocks new
breakage without blocking every PR on old breakage. Findings are compared
without their line numbers, so a row inserted above an old finding does not
make it new. Without --base (the daily build of main, a manual run), every
finding is reported and the exit status is 0.
"""

from __future__ import annotations

import argparse
import io
import json
import re
import subprocess
import sys
import tarfile
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OWN = "org.atlas-wiki"
AUTOFORM = "org.autoform"
NOT_READY = "not_ready"
ARTICLE_ID = re.compile(r"af_[0-9a-f]{24}\Z")
# A folder that `sync_wiki.py declarations` creates for modules the taxonomy has not placed yet.
UNCLASSIFIED = "not-yet-classified"
# The most files GitHub lists in one pull request's diff.
MAX_CHANGED_FILES = 3000
# Build outputs (docs/BLUEPRINT.md) that must never be committed.
DERIVED = ("site/", "site-src/", "build/", "v2-dependencies.jsonl", "v2-dependencies.jsonl.gz", "v2-modules.txt")
LINK = re.compile(r"\]\(\s*<?([^)\s#>]+)")
# The line number in a finding about a links file, left out when comparing findings with the base's.
LINE_NUMBER = re.compile(r"(\.jsonl):\d+")


@dataclass
class Report:
    errors: list[str] = field(default_factory=list)

    def add(self, message: str) -> None:
        self.errors.append(message)


def rel(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return path.as_posix()


def local_links(text: str) -> list[str]:
    return [target for target in LINK.findall(text) if "://" not in target and not target.startswith("mailto:")]


def resolve(page: Path, target: str) -> Path:
    return (page.parent / target).resolve()


def load_annotations(vault: Path, report: Report) -> dict[Path, dict]:
    roadmap = (vault / "roadmap").resolve()
    links = vault / "links"
    seen: dict[Path, str] = {}
    ids: dict[str, str] = {}
    annotations: dict[Path, dict] = {}
    for source in sorted(links.rglob("*.jsonl")):
        where = rel(source, vault.parent)
        for number, line in enumerate(source.read_text(encoding="utf-8").splitlines(), 1):
            if not line.strip():
                continue
            at = f"{where}:{number}"
            try:
                annotation = json.loads(line)
            except json.JSONDecodeError as error:
                report.add(f"{at}: not JSON ({error.msg})")
                continue
            subjects = annotation.get("subject") if isinstance(annotation, dict) else None
            if not isinstance(subjects, list) or len(subjects) != 1 or not isinstance(subjects[0], dict):
                report.add(f"{at}: an annotation names exactly one subject page")
                continue
            uri = subjects[0].get("uri", "")
            page = (source.parent / uri).resolve()
            if page.suffix != ".md" or roadmap not in page.parents:
                report.add(f"{at}: subject {uri!r} is not a page under blueprint/roadmap/")
                continue
            if not page.is_file():
                report.add(f"{at}: subject {uri!r} does not exist")
                continue
            parts = page.relative_to(roadmap).parts
            expected = "roadmap" if len(parts) == 1 else parts[0]
            if source.relative_to(links).as_posix() != f"{expected}.jsonl":
                report.add(f"{at}: {rel(page, roadmap)} belongs in blueprint/links/{expected}.jsonl")
            if page in seen:
                report.add(f"{at}: {rel(page, roadmap)} is already annotated at {seen[page]}")
                continue
            seen[page] = at
            objects = annotation.get("object", [])
            if not isinstance(objects, list) or len(objects) > 1:
                report.add(f"{at}: an annotation names at most one Lean declaration")
            article_id = annotation.get("id")
            if article_id is not None:
                if not isinstance(article_id, str) or not ARTICLE_ID.fullmatch(article_id):
                    report.add(f"{at}: malformed article id {article_id!r}")
                elif article_id in ids:
                    report.add(f"{at}: article id {article_id} is already used at {ids[article_id]}")
                else:
                    ids[article_id] = at
            annotation["_at"] = at
            annotations[page] = annotation
    return annotations


def linked(annotation: dict) -> bool:
    """Whether a row ties its page to Lean, as `sync_wiki.py lean-facts` reads it: a declaration under
    `object`, or the module and name an earlier sync wrote."""
    extensions = annotation.get("extensions")
    own = extensions.get(OWN) if isinstance(extensions, dict) else None
    objects = annotation.get("object")
    named = isinstance(objects, list) and any(
        isinstance(end, dict) and isinstance(end.get("location"), dict) and end["location"].get("declaration")
        for end in objects
    )
    return bool(named or (isinstance(own, dict) and "module" in own and "name" in own))


def check_not_ready(annotations: dict[Path, dict], report: Report) -> None:
    """Rule 12: a node still to be broken down is a planned article marked with Autoform's `not_ready`."""
    for page, annotation in annotations.items():
        extensions = annotation.get("extensions", {})
        ours = extensions.get(AUTOFORM, {}) if isinstance(extensions, dict) else {}
        if not isinstance(ours, dict) or NOT_READY not in ours:
            continue
        at = annotation["_at"]
        if not isinstance(ours[NOT_READY], bool):
            report.add(f"{at}: {AUTOFORM} {NOT_READY} takes true or false; Autoform drops any other value")
            continue
        if not ours[NOT_READY]:
            continue
        if linked(annotation):
            report.add(f"{at}: a node still to be broken down ({NOT_READY}) names no Lean declaration")
        if page.name == "README.md":
            report.add(f"{at}: a folder page is not a node to break down; mark an article {NOT_READY}")


def check_taxonomy(vault: Path, taxonomy_path: Path, report: Report) -> None:
    roadmap = vault / "roadmap"
    try:
        subjects = json.loads(taxonomy_path.read_text(encoding="utf-8"))["subjects"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as error:
        report.add(f"{rel(taxonomy_path, vault.parent)}: unreadable taxonomy ({error})")
        return
    for folder in sorted(path for path in roadmap.iterdir() if path.is_dir()):
        if folder.name == UNCLASSIFIED:
            continue
        subject = subjects.get(folder.name)
        if subject is None:
            report.add(f"blueprint/roadmap/{folder.name}/: not a subject of scripts/taxonomy.json")
            continue
        fields = {entry["slug"] for entry in subject.get("fields", [])}
        if not fields:
            continue
        for child in sorted(folder.iterdir()):
            if child.is_dir() and child.name not in fields:
                report.add(f"blueprint/roadmap/{folder.name}/{child.name}/: not a field of {folder.name} in scripts/taxonomy.json")
            elif child.is_file() and child.suffix == ".md" and child.name != "README.md":
                report.add(f"blueprint/roadmap/{folder.name}/{child.name}: a page of a subject with fields goes in a field folder")


def check_listings(vault: Path, report: Report) -> None:
    """Every page and folder is listed on its folder page."""
    roadmap = (vault / "roadmap").resolve()
    pages = sorted(roadmap.rglob("*.md"))
    for folder in sorted({page.parent for page in pages}):
        readme = folder / "README.md"
        if not readme.is_file():
            report.add(f"blueprint/roadmap/{rel(folder, roadmap)}/: has no README.md folder page")
            continue
        listed = set()
        for target in local_links(readme.read_text(encoding="utf-8")):
            linked = resolve(readme, target)
            listed.add(linked / "README.md" if linked.is_dir() else linked)
        for child in sorted(folder.iterdir()):
            entry = child / "README.md" if child.is_dir() else child
            if (child.is_dir() and entry.is_file()) or (child.suffix == ".md" and child.name != "README.md"):
                if entry.resolve() not in listed:
                    report.add(f"blueprint/roadmap/{rel(child, roadmap)}: not listed on {rel(readme, roadmap)}")


def check_edges(vault: Path, report: Report, declared: set[Path] = frozenset()) -> None:
    """Edges as Autoform reads them: no committed Lean-owned edge on a page tied to a declaration (`declared`),
    and informal edges that resolve and close no cycle. A planned page may write its own `## Depends on`.

    Autoform's own loader parses the pages (case-folded headings, repeated sections, reference links, code
    masking), so this check and `autoform check` read the same graph.
    """
    try:
        from autoform_cli.graph import GraphValidationError, load_graph
    except ImportError:
        report.add("Autoform is not installed: install it at .github/autoform-ref, as docs/BLUEPRINT.md shows")
        return
    roadmap = (vault / "roadmap").resolve()
    try:
        graph = load_graph(vault)
    except GraphValidationError as error:
        for issue in error.issues:
            report.add(f"autoform cannot load the graph: {issue}")
        return
    for node_id, node in sorted(graph.nodes.items()):
        if Path(node.path).resolve() in declared and (node.statement_dependencies or node.proof_dependencies):
            report.add(
                f"blueprint/roadmap/{rel(Path(node.path).resolve(), roadmap)}: commits `## Depends on` or "
                "`## Proof depends on`, which lean-facts writes at build time"
            )
    for warning in graph.warnings:
        if "informal target" in warning or "informally uses itself" in warning:
            report.add(f"`## Informally uses`: {warning}")
    edges = {node_id: list(node.informal_dependencies) for node_id, node in graph.nodes.items()}
    for cycle in informal_cycles(edges):
        report.add("`## Informally uses` closes a cycle: " + " -> ".join(cycle))
    try:
        from autoform_cli.graph import informal_cycle_warnings
    except ImportError:  # an older Autoform: the cycles among informal links above still count
        informal_cycle_warnings = None
    for warning in informal_cycle_warnings(graph) if informal_cycle_warnings else ():
        report.add(f"`## Informally uses`: {warning}")


def informal_cycles(edges: dict) -> list[list]:
    """One cycle per strongly connected group of pages that link each other informally."""
    index: dict[Path, int] = {}
    low: dict[Path, int] = {}
    stack: list[Path] = []
    on_stack: set[Path] = set()
    cycles: list[list[Path]] = []
    counter = 0
    for root in sorted(edges):
        if root in index:
            continue
        work = [(root, iter(edges.get(root, [])))]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on_stack.add(root)
        while work:
            node, children = work[-1]
            advanced = False
            for child in children:
                if child not in index:
                    index[child] = low[child] = counter
                    counter += 1
                    stack.append(child)
                    on_stack.add(child)
                    work.append((child, iter(edges.get(child, []))))
                    advanced = True
                    break
                if child in on_stack:
                    low[node] = min(low[node], index[child])
            if advanced:
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[node])
            if low[node] == index[node]:
                group = []
                while True:
                    member = stack.pop()
                    on_stack.discard(member)
                    group.append(member)
                    if member == node:
                        break
                if len(group) > 1:
                    cycles.append(sorted(group) + [sorted(group)[0]])
    return cycles


def git_files(root: Path, *args: str) -> list[str]:
    output = subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True, text=True).stdout
    return [line for line in output.splitlines() if line]


def check_derived(root: Path, report: Report) -> None:
    for path in git_files(root, "ls-files", "--", *(entry.rstrip("/") for entry in DERIVED)):
        report.add(f"{path}: a build output is committed")


def check_size(root: Path, base: str, report: Report) -> None:
    changed = git_files(root, "diff", "--name-only", base, "HEAD")
    if len(changed) >= MAX_CHANGED_FILES:
        report.add(f"the PR changes {len(changed)} files; split it below {MAX_CHANGED_FILES}, the most GitHub shows in one diff")


def check(root: Path = ROOT, base: str | None = None) -> list[str]:
    report = Report()
    vault = root / "blueprint"
    annotations = load_annotations(vault, report)
    check_not_ready(annotations, report)
    check_taxonomy(vault, root / "scripts" / "taxonomy.json", report)
    check_listings(vault, report)
    check_edges(vault, report, {page for page, annotation in annotations.items() if linked(annotation)})
    if (root / ".git").exists():
        check_derived(root, report)
        if base:
            check_size(root, base, report)
    return report.errors


def comparable(error: str) -> str:
    """A finding without the line number of the links-file row it names."""
    return LINE_NUMBER.sub(r"\1", error)


def base_findings(root: Path, base: str) -> list[str]:
    """The findings the base commit already has: its vault and taxonomy, exported from git and checked alone."""
    with tempfile.TemporaryDirectory() as directory:
        archive = subprocess.run(
            ["git", "-C", str(root), "archive", "--format=tar", base, "blueprint", "scripts/taxonomy.json"],
            check=True, capture_output=True,
        ).stdout
        with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
            try:
                tar.extractall(directory, filter="data")
            except TypeError:  # Python before 3.11.4 has no extraction filters; the archive is our own commit
                tar.extractall(directory)
        return check(Path(directory))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--base", help="the commit the PR merges into: fail only on findings it doesn't have")
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    errors = check(root, args.base)
    if not args.base:
        # Nothing to compare with (a push to main, a manual run): report, and leave blocking to PRs.
        for error in errors:
            print(f"warning: {error}", file=sys.stderr)
        print(f"graph rules: {len(errors)} finding(s), reported only" if errors else "graph rules: OK")
        return 0
    if not errors:
        print("graph rules: OK")
        return 0
    known = {comparable(error) for error in base_findings(root, args.base)}
    new = [error for error in errors if comparable(error) not in known]
    for error in errors:
        if comparable(error) in known:
            print(f"warning (already on the base branch): {error}", file=sys.stderr)
    for error in new:
        print(error, file=sys.stderr)
    if new:
        print(f"{len(new)} new graph rule finding(s); see Graph rules in docs/BLUEPRINT.md", file=sys.stderr)
        return 1
    print(f"graph rules: no new findings ({len(errors)} already on the base branch)" if errors else "graph rules: OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
