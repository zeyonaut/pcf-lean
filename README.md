# opcf-lean

`opcf-lean` is a formalization of the denotational semantics of [PCF](https://en.wikipedia.org/wiki/Programming_Computable_Functions) in [Lean](https://lean-lang.org/), following the notes of the 2023-2024 [Denotational Semantics](https://www.cl.cam.ac.uk/teaching/2324/DenotSem/notes.pdf) course at Cambridge (as written by Andrew Pitts, Glynn Winskel, Marcelo Fiore, and Meven Lennon-Bertrand). This presentation encodes the denotations of PCF terms as ω-cocontinuous monotone maps taking *environments* to *semantic values*.

This formalization adopts an intrinsically-typed and intrinsically-scoped representation of PCF syntax, based on the technique described in [PLFA](https://plfa.inf.ed.ac.uk/22.08/) (Philip Wadler, Wen Kokke, and Jeremy G. Siek).

## Contents

### Prelude

File | Description
---|---
[Utility.lean](/oPCF/Utility.lean) | Basic vocabulary for the formalization.

### Syntax

File | Description
---|---
[Syntax.lean](/oPCF/Syntax.lean) | The core syntax of PCF: types, contexts, variables, and terms.
[Substitution.lean](/oPCF/Substitution.lean) | Renamings and substitutions for variables and terms.

### Operational Semantics

File | Description
---|---
[Evaluation.lean](/oPCF/Evaluation.lean) | Characterizing PCF terms with unique evaluations.
[Context.lean](/oPCF/Context.lean) | Term contexts and contextual equivalence.

### Domain Theory

File | Description
---|---
[Order.lean](/oPCF/Order.lean) | Partial orders and monotonicity.
[Domain.lean](/oPCF/Domain.lean) | Domains (pointed ω-CPOs), continuity, and fixed points.
[Flat.lean](/oPCF/Flat.lean) | Flat domains.

### Denotational Semantics

File | Description
---|---
[Denotation.lean](/oPCF/Denotation.lean) | Denotations of syntactic objects.
[Approximation.lean](/oPCF/Approximation.lean) | Formal approximation between semantics and syntax.
[Soundness.lean](/oPCF/Soundness.lean) | Soundness, compositionality, and adequacy of denotations.
[Extensionality.lean](/oPCF/Extensionality.lean) | Extensionality principles for contextual equivalence.
