.PHONY: build audit imports axioms verify check

imports:
	python3 scripts/check_local_imports.py . KltDP

audit:
	python3 scripts/check_no_placeholders.py KltDP KltDP.lean --json audit/source-audit.json

verify:
	python3 scripts/verify_package.py

build:
	lake build KltDP

axioms:
	./scripts/print_axioms.sh 2>&1 | tee axiom-report.txt
	python3 scripts/check_axioms.py axiom-report.txt

check: imports audit verify build axioms
