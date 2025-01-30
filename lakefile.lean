import Lake

open Lake DSL

package SyV where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "stable"

@[default_target]
lean_lib SyV {
  roots := #[`SyV]
  globs := #[Glob.submodules `SyV]
}
