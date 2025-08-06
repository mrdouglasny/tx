import Lake
open Lake DSL

package «TxGraffitiBench» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here
require Hammer from git
  "https://github.com/JOSHCLUNE/LeanHammer.git"@"v4.21.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.21.0"

@[default_target]
lean_lib «TxGraffitiBench» where
  -- add any library configuration options here
