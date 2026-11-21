---
name: lean-property-testing
description: 'Use for executable Lean requirements when performing property-based testing, Plausible counterexample search, generator design, or deciding whether a property is testable before proof.'
---

# Lean Property Testing

Use property-based testing as a mandatory assessment step before proving an
agreed Lean requirement. Counterexample search increases confidence but does
not replace a checked theorem.

## Procedure

1. Start from the agreed named proposition in `Spec.lean`; do not invent a
   separate test-only formulation of the requirement.
2. Determine whether the proposition is executable and sampleable with a
   useful population.
   - If it is not, state the concrete reason and proceed to proof without a
     property test. Do not silently skip the assessment.
   - If it is executable and sampleable, use the following steps before proof.
3. Identify the exact quantified population: all representable values, values
   satisfying domain invariants, or states reachable from an initial state.
4. Build generators for that population. Prefer direct generation of valid
   values over filtering arbitrary values.
5. For transition systems, generate input sequences and fold them through the
   transition function so tests cover reachable traces rather than isolated
   states.
6. Run Plausible to search for counterexamples.
7. If a counterexample is found, determine whether it exposes an implementation
   defect, a missing domain constraint, or an incorrect specification. Fix the
   implementation directly when appropriate. Ask the developer before changing
   the agreed domain model or requirement.
8. After the search no longer finds failures, retain focused property tests as
   regression checks when practical, especially for boundaries and previously
   found counterexamples.
9. Continue to the formal proof and verify that its quantifiers and assumptions
   match the tested population.

## Correctness Boundary

A property about arbitrary states differs from one about invariant-preserving
or reachable states. A narrow generator can hide failures, while an unrestricted
generator can produce values the domain excludes. Document the generated
population next to the test and keep shrinking within that population.

Use the [property-testing guide](../../../docs/lean-property-testing.md) for
Plausible-specific setup, instances, implication handling, and runner options.
