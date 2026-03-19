import Lake
open Lake DSL

package optlib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Optlib where

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"8f9d9cff6bd728b17a24e163c9402775d9e6a365"

meta if get_config? env = some "CI_BUILD" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "a41d5ebebfa77afe737fec8de8ad03fc8b08fdff"
