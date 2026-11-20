# Repository policy

The repository adopts
[estate-repository-v3](https://github.com/larsbx/estate-governance/blob/b851c92fceb88c8e6f4604664cf975b567ade161/docs/architecture/estate-repository-template-v3.md)
at governance revision `b851c92fceb88c8e6f4604664cf975b567ade161`.
[DR-0006](https://github.com/larsbx/estate-governance/blob/b851c92fceb88c8e6f4604664cf975b567ade161/docs/decisions/DR-0006-language-independent-formalization.md)
removes implementation-language mandates and requires both Lean and Quint
formalization with explicit scope and execution evidence.

`ESTATE.toml` carries repository identity, position, authority, implementation
inventory, formal declarations, and the external auditor pin. The governance
pinning tool establishes the revision and digest; the CI gate verifies those
bytes before executing the auditor. Static manifest conformance and completed
formal execution are separately reported checks.

This repository has no accepting boundary. Its reference reports observations;
its local proofs establish the stated transaction, stored-binding,
expression-DAG/scope, and lifting/substitution model properties.
Finite comparison and performance measurements remain evidence. The formal scope
document records the implementation correspondence that remains unproved.

Changes enter through reviewed PRs against `main` under the user's instructions
and the repository's actual branch protections. Merge evidence identifies the
checked revision and distinguishes local execution from hosted CI. Publication
does not promote the candidate stage or alter the authority boundary.
