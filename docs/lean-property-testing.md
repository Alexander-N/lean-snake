# Property Testing in the Verification Workflow

Use [Plausible](https://github.com/leanprover-community/plausible) for cheap
counterexample search before attempting a formal proof. A property test
increases confidence but is not a substitute for a checked theorem.

## Workflow

For each proposed requirement:

1. Express the requirement as a Lean proposition.
2. Decide which values the property quantifies over:
   - all representable values;
   - values satisfying the domain invariants; or
   - states reachable from an initial state.
3. Build a generator for that exact population. Prefer direct generation of
   valid values over heavily filtering arbitrary values.
4. For transition systems, generate input sequences and fold them through the
   transition function so tests cover reachable traces rather than isolated
   states.
5. Use Plausible to search for counterexamples before proof work begins.
6. If a counterexample is found, distinguish an implementation defect from an
   incorrect assumption or specification and correct the relevant layer.
7. Prove the property after counterexample search no longer finds failures.
8. Retain focused property tests as regression checks, especially around
   boundary conditions and previously found counterexamples.

## Correctness boundary

Keep the tested quantifiers aligned with the proof's quantifiers. A property
about arbitrary states and a property about invariant-preserving or reachable
states answer different questions.

A generator that is too narrow can hide failures, while an unrestricted
generator can produce states that the domain excludes. Document the generated
population next to each test and keep shrinking inside that same population.

## Library reference

Use the Plausible documentation for installation, API details, derived
instances, custom generators, and test configuration. This document only defines
how property testing fits into the verification workflow.
