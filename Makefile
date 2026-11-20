.PHONY: pins test smoke benchmark audit formal-tests formal acceptance

pins:
	python3 tools/run.py pins --output conformance/evidence/pins

test:
	python3 tools/run.py check --definitions 128 --output conformance/evidence/check $(CHECK_ARGS)

smoke:
	python3 tools/run.py bench --samples 1 --definitions 8 --workers 1 --min-sample-seconds 0.05 --output conformance/evidence/smoke

benchmark:
	python3 tools/run.py bench --output conformance/evidence/benchmark $(BENCHMARK_ARGS)

audit:
	sh tools/estate-audit.sh $(if $(ESTATE_AUDITOR),"$(ESTATE_AUDITOR)")

formal-tests:
	python3 -m unittest discover -s tests -v

formal:
	python3 tools/check_formal.py

acceptance:
	python3 tools/acceptance.py
