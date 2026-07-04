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
  5. every doc is indexed by the README.md of its own directory (each
     directory with docs must have a README.md linking every sibling —
     this is what makes archive/README.md the archive index, docs/README.md
     the root index, etc.; no per-directory special cases)
  6. every inline-code file reference resolves — not just markdown links but
     backticked paths like `lean/RawAsm/Rv64i.lean` or `tools/gen_image.py`.
     A backticked token is treated as a repo file reference only when it is
     ANCHORED at a real top-level repo entry (its first path segment names an
     existing entry of the repo root) and is placeholder-free; that anchor
     deliberately skips third-party-relative paths (`cfrontend/Clight.v`),
     implicit-`lean/` paths (`LowIR/Compile.lean`) and templates (`<file>.lean`,
     `{a,b}.lean`, `work-*/`), which cannot be resolved unambiguously. Frozen
     archive/ and vendored third-party/ docs are exempt from this check.

Exit code 0 = all green, 1 = at least one error. Run from anywhere:
    ./docs/check_docs.py
"""

from __future__ import annotations

import re
import sys
import urllib.parse
from pathlib import Path

DOCS = Path(__file__).resolve().parent
ROOT = DOCS.parent  # repo root — file references anchor here
README = DOCS / "README.md"

LINK_RE = re.compile(r'!?\[[^\]]*\]\(\s*([^)\s]+)(?:\s+"[^"]*")?\s*\)')
HEADING_RE = re.compile(r"(#{1,6})\s+(.*)")
SCHEME_RE = re.compile(r"[a-zA-Z][a-zA-Z0-9+.-]*:")
CODE_RE = re.compile(r"`([^`]+)`")            # inline-code span
PLACEHOLDER_RE = re.compile(r"[<>{}*\s]")     # template markers / not a literal path


def slugify(heading: str) -> str:
    """GitHub-style anchor slug for a heading line."""
    text = re.sub(r"`([^`]+)`", r"\1", heading)          # inline code
    text = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", text)  # links -> text
    text = text.strip().lower()
    text = re.sub(r"[^\w\- ]", "", text)
    return text.replace(" ", "-")


def code_spans(path: Path) -> list[tuple[int, str]]:
    """Return [(lineno, inline-code-token)] outside fenced code blocks."""
    spans: list[tuple[int, str]] = []
    in_fence = False
    for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if line.lstrip().startswith(("```", "~~~")):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        for m in CODE_RE.finditer(line):
            spans.append((lineno, m.group(1)))
    return spans


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

    # -- check 5: every doc is indexed by its own directory's README.md ------
    by_dir: dict[Path, list[Path]] = {}
    for p in corpus:
        by_dir.setdefault(p.parent, []).append(p)
    for directory, files in sorted(by_dir.items()):
        index = directory / "README.md"
        if index not in parsed:
            err(directory, None, "directory has docs but no README.md index")
            continue
        listed = resolved_links[index]
        for p in files:
            if p != index and p not in listed:
                err(p, None, f"not indexed in {index.relative_to(DOCS)}")

    # -- check 6: inline-code file references resolve ------------------------
    toplevel = {p.name for p in ROOT.iterdir()}  # anchors: lean, docs, bare, ...
    for path in corpus:
        rel_parts = path.relative_to(DOCS).parts
        if "archive" in rel_parts or "third-party" in rel_parts:
            continue  # frozen snapshots / vendored — exempt
        for lineno, tok in code_spans(path):
            if PLACEHOLDER_RE.search(tok):
                continue  # `<file>.lean`, `{a,b}.lean`, `work-*/`, prose
            ref = tok.split("#", 1)[0].rstrip("/")
            if "/" not in ref:
                continue  # bare names / plain identifiers — not a path reference
            if ref.split("/", 1)[0] not in toplevel:
                continue  # not anchored at the repo root (e.g. third-party-relative)
            if not (ROOT / ref).exists():
                err(path, lineno, f"broken file reference `{tok}` (no such path '{ref}')")

    if errors:
        print(f"FAIL — {len(errors)} problem(s):")
        for e in errors:
            print(f"  {e}")
        return 1
    print(f"OK — {len(corpus)} markdown files checked, all constraints hold.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
