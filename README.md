# opcf-lean

`opcf-lean` is a formalization of the denotational semantics of PCF in [Lean](https://lean-lang.org/), following the presentation in the 2023-2024 [Denotational Semantics](https://www.cl.cam.ac.uk/teaching/2324/DenotSem/notes.pdf) course at Cambridge as written by Meven Lennon-Bertrand (based on previous notes by Marcelo Fiore, Glynn Winskel, and Andrew Pitts). This presentation encodes the denotations of PCF terms as ω-cocontinuous monotone maps taking *environments* to *semantic values*.

This formalization adopts an intrinsically-typed and intrinsically-scoped representation of PCF syntax, similar in spirit to Lennon-Bertrand's notes and based on the technique described in [PLFA](https://plfa.inf.ed.ac.uk/22.08/) (Philip Wadler, Wen Kokke, and Jeremy G. Siek).
