## Checks

- [ ] Changed Lean modules compile locally or pass the focused PR build.
- [ ] `python scripts/check_lean_placeholders.py`
- [ ] I ran the full build/audit when changing build configuration, repository
      structure, or axiom policy.

## Notes

- Add new compilation-test modules under `GameTheoryTest.lean`, not the public `GameTheory.lean` umbrella.
- Update README or module docs when moving public imports or changing the repository map.
