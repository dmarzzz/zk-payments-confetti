import Lake
open Lake DSL

package Zkpc where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

/-
VCV-io pinned to main as of 2026-07-06. Brings mathlib v4.30.0 transitively
(VCV-io pins it); we also require mathlib explicitly at the same tag so
`lake exe cache get` resolves against the root manifest.
-/
require VCVio from git
  "https://github.com/Verified-zkEVM/VCV-io" @
  "8f5dc4f2923cc47e39bc6ce21f71563cf7d19193"

require "leanprover-community" / "mathlib" @ git "v4.30.0"

@[default_target] lean_lib Zkpc
