import Lake
open Lake DSL

package «PCF» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs, true⟩ -- shows full proofs in infoview
  ]

@[default_target]
lean_lib «PCF» where
