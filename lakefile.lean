/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Lake
open Lake DSL

package cvc {
  precompileModules := true
  testDriver := "cvcTests"
}

require "leanprover-community" / batteries

require "abdoo8080" / cvc5

@[default_target]
lean_lib Cvc {}

-- `Cvc.Proto2` is a fork of `Cvc.Proto`, so the two cannot be imported together: a
-- `declare_syntax_cat` and a command token are both global, and each fork declares its own. It
-- gets its own target rather than being pulled in by `Cvc.lean`.
@[default_target]
lean_lib proto2 {
  roots := #[`Cvc.Proto2]
}

lean_lib cvcTests {
  globs := #[Glob.submodules `Cvc.Tests]
}
