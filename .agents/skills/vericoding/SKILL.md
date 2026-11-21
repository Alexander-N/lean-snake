---
name: vericoding
description: 'Use by default for all changes in this project; develop one requirement at a time and verify it before proceeding.'
---

# Vericoding

Develop the system one requirement at a time:

1. **Developer:** Describe the desired behavior.
2. **Developer and agent:** Discuss and clarify the domain concepts needed to
   express the behavior. Encode the agreed domain model in `Spec.lean` and
   agree that it captures the intended domain. Then, for each requirement,
   agree on its plain-language description before encoding its named
   proposition in `Spec.lean`. Don't specify implementation details.
3. **Agent:** Implement the behavior without changing `Spec.lean`. If
   implementation reveals an ambiguity or gap, ask the developer to clarify
   or approve a spec change before proceeding.
4. **Agent:** Load and apply the
   [Lean property-testing skill](../lean-property-testing/SKILL.md). Before
   proof, assess every agreed requirement for an executable, sampleable
   property. If suitable, search for counterexamples first; if not, state why.
5. **Agent:** Prove in `Proofs.lean` that the concrete implementation satisfies
   the requirement in `Spec.lean`.

The Lean proof verifies the implementation represented by the formal model.
If runtime behavior is implemented separately from that model, establish its
connection to the verified implementation as well. After proving a requirement,
repeat the process for the next one, evolving the domain model as needed while
keeping earlier proofs valid.
