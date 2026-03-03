# ProtoKuhn Essentials (Shadow Experiments)

This folder is intentionally "shadow-only": it is not imported by the main development.

Goal of this first pass: test whether small, interface-level lemmas are useful before
doing larger refactors.

Current artifacts:

1. `00-Workflow.md`
   - iterative analysis protocol with explicit backtracking policy.

2. `01-AbstractVocabulary.md`
   - de-gamified terminology and theorem schemas.

3. `10-KuhnStyle-Decomposition.md`
   - abstract decomposition for factorization-equivalence / realizability.

4. `11-ZermeloStyle-Decomposition.md`
   - abstract decomposition for well-founded extremization/determinacy.

5. `20-ExecutionChecklist.md`
   - session-by-session execution template.

6. `CoreSmallLemmas.lean` (minimal, non-domain-specific)
   - `curry_update`
   - `foldl_update_invariant`
   - `pushforward_comp'`

7. `31-DefinitionFreeSchemas.md`
   - reusable statement patterns without introducing new definitions
   - plus cross-field naming map

If these prove useful, the next step is to promote selected lemmas into main files
(or a new interfaces file) and re-point larger proofs to them.
