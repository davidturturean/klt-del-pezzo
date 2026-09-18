#!/usr/bin/env python3
"""Verify that every project-local Lean import resolves to a checked-in file.

Also checks that the root module imports every library module exactly once.
The audit tooling module `KltDP/Audit/Trust.lean` is not part of the library
target; it is imported only by `audit/CompiledTrust.lean`.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

IMPORT_RE = re.compile(r"(?m)^import\s+([^\s]+)")
SKIP_DIRS = {".lake", "build", ".git"}
ROOT_EXEMPT = {"KltDP/Audit/Trust.lean"}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("repo", type=Path)
    parser.add_argument("namespace")
    parser.add_argument("--root", default=None, help="root module file (default <namespace>.lean)")
    args = parser.parse_args()
    repo = args.repo.resolve()
    root_file = repo / (args.root or f"{args.namespace}.lean")

    files = sorted(p for p in repo.rglob("*.lean") if not (set(p.relative_to(repo).parts) & SKIP_DIRS))
    prefix = args.namespace + "."
    missing: list[tuple[Path, str, Path]] = []
    for file in files:
        text = file.read_text(encoding="utf-8")
        for module in IMPORT_RE.findall(text):
            if module == args.namespace or module.startswith(prefix):
                expected = repo / (module.replace(".", "/") + ".lean")
                if not expected.is_file():
                    missing.append((file, module, expected))
    status = 0
    if missing:
        for file, module, expected in missing:
            print(f"{file}: unresolved local import {module} (expected {expected})")
        status = 1

    library_dir = repo / args.namespace
    modules = set()
    for file in library_dir.rglob("*.lean"):
        rel = file.relative_to(repo).as_posix()
        if rel in ROOT_EXEMPT:
            continue
        modules.add(rel[:-5].replace("/", "."))
    root_imports = IMPORT_RE.findall(root_file.read_text(encoding="utf-8"))
    duplicates = sorted({m for m in root_imports if root_imports.count(m) > 1})
    not_imported = sorted(modules - set(root_imports))
    extra = sorted(set(root_imports) - modules)
    if duplicates or not_imported or extra:
        for module in not_imported:
            print(f"{root_file}: library module not imported by the root: {module}")
        for module in extra:
            print(f"{root_file}: root import is not a library module: {module}")
        for module in duplicates:
            print(f"{root_file}: duplicate root import: {module}")
        status = 1
    if status == 0:
        print(f"OK: {len(files)} Lean files; all {args.namespace} imports resolve locally; "
              f"the root imports all {len(modules)} library modules.")
    return status


if __name__ == "__main__":
    sys.exit(main())
