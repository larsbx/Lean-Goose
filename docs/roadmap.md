# Next concrete obligations

Estate v3 adoption establishes local Lean and Quint formalization of ordered
definition transactions. The complete proof scope, bounded checks, and runtime
comparison limits are recorded in [formalization.md](formalization.md). The
following obligations remain distinct from that completed implementation work;
execution results belong to the actual receipts for each revision.

1. **Stored-binding correspondence:** extend the ordered-name transaction model
   to typed bindings and show preservation of existing type/value/inferred fields
   across refusals and successful extension. The current runtime interface
   exposes outcomes and counts, so additional observable probes or a reviewed
   trace interface are needed before claiming direct representation agreement.
2. **Expression-level formalization:** formalize capture-avoiding substitution,
   scope preservation, and the selected typing/reduction rules, then connect them
   to concrete Goose evaluation. The current action model abstracts those checks;
   finite expression comparison does not prove their general correctness.
3. **Fresh unshared syntax:** profile arena import, metadata construction, and
   inference on `unshared_trees`. Retain all current positive/refusal comparisons
   and formal transaction checks when changing representation or caches.
4. **Broader conversion coverage:** expose and compare additional beta/zeta,
   substitution, and normalization observations from the independent corpora.
   Keep eta and proof irrelevance explicitly outside the implemented relation
   until separately implemented and validated.
5. **Resource behavior:** specify and test work, height, intermediate-node, and
   context boundaries. Model failure priority when resource limits interact with
   duplicate or semantic checks. Current limits are implementation-specific;
   matching another engine's fuel is not established.
6. **Module separation:** split reference semantics from observation and timing
   adapters under source-bound replay, preserving every current case and the
   formal implementation mapping.
7. **Accepting-boundary proposal:** before adding an authoritative entrypoint,
   name its exact contract and implementation files, trusted base, supported
   semantics, rejection evidence, and formal obligations. Review the manifest
   authority change explicitly. Any implementation language combination may be
   used; performance results do not promote authority.

General universes, inductives, recursors, quotients, `.olean` ingestion, and full
Lean theorem admission remain outside the current reference. A fresh full
benchmark can measure the current revision; it cannot close those semantic or
formal correspondence obligations.
