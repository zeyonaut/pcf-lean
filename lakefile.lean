import Lake
open Lake DSL

package «oPCF» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

@[default_target]
lean_lib «oPCF» where
