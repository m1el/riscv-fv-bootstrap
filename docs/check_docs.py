#!/usr/bin/env python3
"""Validate the docs/ markdown corpus.

Checks:
  1. every relative markdown link resolves to an existing file
  2. every link with a #fragment points at a real heading (GitHub slug rules)
  3. no absolute-path links (non-portable)
  4. every doc is reachable from README.md following only "down" links
     (a link counts as an edge only if the target lives in the linking
     file's own directory or below — e.g. archive/* -> ../* is a valid
     link but not a reachability edge)
  5. every archived doc is listed in archive/README.md
  6. every active doc (outside archive/) is linked directly from README.md
     (the index must be complete, per the project doc rule)

Exit code 0 = all green, 1 = at least one error. Run from anywhere:
    ./docs/check_docs.py
"""

from __future__ import annotations

import re
import sys
import urllib.parse
from pathlib import Path

DOCS = Path(__file__).resolve().parent
README = DOCS / "README.md"
ARCHIVE_DIR = DOCS / "archive"
ARCHIVE_INDEX = ARCHIVE_DIR / "README.md"

LINK_RE = re.compile(r'!?\[[^\]]*\]\(\s*([^)\s]+)(?:\s+"[^"]*")?\s*\)')
HEADING_RE = re.compile(r"(#{1,6})\s+(.*)")
SCHEME_RE = re.compile(r"[a-zA-Z][a-zA-Z0-9+.-]*:")


def slugify(heading: str) -> str:
    """GitHub-style anchor slug for a heading line."""
    text = re.sub(r"`([^`]+)`", r"\1", heading)          # inline code
    text = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", text)  # links -> text
    text = text.strip().lower()
    text = re.sub(r"[^\w\- ]", "", text)
    return text.replace(" ", "-")


def parse(path: Path) -> tuple[list[tuple[int, str]], set[str]]:
    """Return ([(lineno, link_target)], {anchor slugs}) for a markdown file."""
    links: list[tuple[int, str]] = []
    slugs: set[str] = set()
    seen: dict[str, int] = {}
    in_fence = False
    for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if line.lstrip().startswith(("```", "~~~")):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        m = HEADING_RE.match(line)
        if m:
            slug = slugify(m.group(2))
            n = seen.get(slug, 0)
            seen[slug] = n + 1
            slugs.add(slug if n == 0 else f"{slug}-{n}")
            continue
        scrubbed = re.sub(r"`[^`]*`", "", line)  # ignore links inside inline code
        for lm in LINK_RE.finditer(scrubbed):
            links.append((lineno, lm.group(1)))
    return links, slugs


def main() -> int:
    errors: list[str] = []

    def err(path: Path, lineno: int | None, msg: str) -> None:
        loc = f"{path.relative_to(DOCS)}:{lineno}" if lineno else str(path.relative_to(DOCS))
        errors.append(f"{loc}: {msg}")

    corpus = sorted(DOCS.rglob("*.md"))
    parsed = {p: parse(p) for p in corpus}
    outside_slugs: dict[Path, set[str]] = {}  # lazily parsed files outside docs/

    # -- checks 1-3: link validity, anchors, no absolute paths ---------------
    down_edges: dict[Path, set[Path]] = {p: set() for p in corpus}
    resolved_links: dict[Path, set[Path]] = {p: set() for p in corpus}
    for path, (links, own_slugs) in parsed.items():
        for lineno, target in links:
            if SCHEME_RE.match(target):
                continue  # http(s):, mailto:, ...
            frag_path, _, frag = target.partition("#")
            frag_path = urllib.parse.unquote(frag_path)
            if not frag_path:  # same-file anchor
                if frag not in own_slugs:
                    err(path, lineno, f"broken anchor '#{frag}' (no such heading here)")
                continue
            if frag_path.startswith("/"):
                err(path, lineno, f"absolute-path link '{target}' (use a relative path)")
                continue
            dest = (path.parent / frag_path).resolve()
            if not dest.exists():
                err(path, lineno, f"broken link '{target}' (no such file)")
                continue
            if frag and dest.suffix == ".md":
                if dest in parsed:
                    dest_slugs = parsed[dest][1]
                else:
                    if dest not in outside_slugs:
                        outside_slugs[dest] = parse(dest)[1]
                    dest_slugs = outside_slugs[dest]
                if frag not in dest_slugs:
                    err(path, lineno, f"broken anchor '{target}' (no heading '#{frag}' in target)")
            if dest in down_edges and dest != path:
                resolved_links[path].add(dest)
                if dest.is_relative_to(path.parent):
                    down_edges[path].add(dest)

    # -- check 4: reachability from README.md via down links only ------------
    if README not in parsed:
        err(DOCS, None, "README.md missing")
    else:
        reached = {README}
        queue = [README]
        while queue:
            for nxt in down_edges[queue.pop()]:
                if nxt not in reached:
                    reached.add(nxt)
                    queue.append(nxt)
        for p in corpus:
            if p not in reached:
                err(p, None, "not reachable from README.md via down-links "
                             "(add an index entry along the directory path)")

    # -- check 5: archive index completeness ----------------------------------
    if ARCHIVE_DIR.is_dir():
        if ARCHIVE_INDEX not in parsed:
            err(ARCHIVE_DIR, None, "archive/README.md missing")
        else:
            listed = resolved_links[ARCHIVE_INDEX]
            for p in sorted(ARCHIVE_DIR.glob("*.md")):
                if p != ARCHIVE_INDEX and p not in listed:
                    err(p, None, "archived doc not listed in archive/README.md")

    # -- check 6: root index lists every active doc ---------------------------
    if README in parsed:
        indexed = resolved_links[README]
        for p in corpus:
            if p == README or ARCHIVE_DIR in p.parents:
                continue
            if p not in indexed:
                err(p, None, "active doc not linked from README.md (index it)")

    if errors:
        print(f"FAIL — {len(errors)} problem(s):")
        for e in errors:
            print(f"  {e}")
        return 1
    print(f"OK — {len(corpus)} markdown files checked, all constraints hold.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
