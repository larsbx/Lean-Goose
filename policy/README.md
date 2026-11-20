# Scaffold policy

The repository follows the canonical
[estate repository template v2](https://github.com/larsbx/estate-governance/blob/bd731398b567cfe523667fc8e23a96d299067141/docs/architecture/estate-repository-template-v2.md).
`ESTATE.toml` carries its identity, default research position, authority planes
and the pinned external audit. The canonical `tools/pin_estate.py` sets the
governance revision and auditor digest; the CI gate verifies those bytes before
executing the auditor.

The scaffold has no authoritative kernel. Its reference reports observations;
finite agreement and performance measurements remain evidence. No successful
comparison can grant theorem, declaration, authorization or deployment rights.

Changes enter through reviewed PRs against `main` under the user's instructions
and the repository's actual branch protections. Merge evidence identifies the
checked revision and distinguishes local execution from hosted CI. Publication
does not promote the candidate stage or alter the authority boundary.
