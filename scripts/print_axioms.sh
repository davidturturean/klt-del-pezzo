#!/usr/bin/env bash
# Re-elaborate the main-theorem module and the examples module; their trailing
# `#print axioms` commands print the dependency reports checked by
# scripts/check_axioms.py (the main theorem and the two examples).
set -euo pipefail
lake env lean KltDP/Manuscript/Main/Final.lean
lake env lean KltDP/Manuscript/S01/Examples.lean
