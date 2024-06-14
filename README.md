# pcf-lean

`pcf-lean` is a formalization of the denotational semantics of [PCF](https://en.wikipedia.org/wiki/Programming_Computable_Functions) in [Lean](https://lean-lang.org/), following the notes of the 2023-2024 [Denotational Semantics](https://www.cl.cam.ac.uk/teaching/2324/DenotSem/notes.pdf) course at Cambridge (as written by Andrew Pitts, Glynn Winskel, Marcelo Fiore, and Meven Lennon-Bertrand).
This presentation encodes the denotations of PCF terms as ω-cocontinuous monotone maps taking *environments* to *semantic values*.

This formalization adopts an intrinsically-typed and intrinsically-scoped representation of PCF syntax, based on the technique described in [PLFA](https://plfa.inf.ed.ac.uk/22.08/) (Philip Wadler, Wen Kokke, and Jeremy G. Siek).
The approach taken to proving the undefinability of parallel OR is described by Kurt Sieber in ["Reasoning about sequential functions via logical relations"](https://doi.org/10.1017/CBO9780511525902.015).

## Variations

While this project intends to faithfully follow the proofs written in the course, some aspects have been changed for ease of formalization.
Most notably, rather than prove an extensionality principle for the contextual preorder in terms of syntactic functions, we prove one in terms of evaluation contexts, requiring the extension of the formal approximation relation to evaluation contexts.
This also affects the proof of full abstraction failure, which has been reworked to use this new extensionality principle instead.

## Contents

The contents of this formalization are best viewed interactively through a Lean installation, such as the [official VSCode extension for Lean 4](https://github.com/leanprover/vscode-lean4), which allows users to step through proofs and jump between definitions.
Nevertheless, some effort has been made to document or otherwise structure the code to be as readable as possible without the interactivity of a theorem prover (except where it hasn't; contributions welcome!).

### Prelude

File | Description
---|---
[Utility.lean](/PCF/Utility.lean) | Basic vocabulary for the formalization.

### Syntax

File | Description
---|---
[Syntax.lean](/PCF/Syntax.lean) | The core syntax of PCF: types, contexts, variables, and terms.
[Substitution.lean](/PCF/Substitution.lean) | Renamings and substitutions for variables and terms.

### Operational Semantics

File | Description
---|---
[Evaluation.lean](/PCF/Evaluation.lean) | Characterizing PCF terms with unique evaluations.
[Context.lean](/PCF/Context.lean) | Term contexts and contextual equivalence.

### Domain Theory

File | Description
---|---
[Order.lean](/PCF/Order.lean) | Partial orders and monotonicity.
[Domain.lean](/PCF/Domain.lean) | Domains (pointed ω-CPOs), continuity, and fixed points.
[Flat.lean](/PCF/Flat.lean) | Flat domains.

### Denotational Semantics

File | Description
---|---
[Denotation.lean](/PCF/Denotation.lean) | Denotations of syntactic objects.
[Approximation.lean](/PCF/Approximation.lean) | Formal approximation between semantics and syntax.
[Soundness.lean](/PCF/Soundness.lean) | Soundness, compositionality, and adequacy of denotations.
[Extensionality.lean](/PCF/Extensionality.lean) | Extensionality principles for contextual equivalence.
[Undefinability.lean](/PCF/Undefinability.lean) | Undefinable denotations and full abstraction failure.
