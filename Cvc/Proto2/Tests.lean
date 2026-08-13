/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto2.Tests.Srt
import Cvc.Proto2.Tests.Signatures
import Cvc.Proto2.Tests.Fun
import Cvc.Proto2.Tests.Untyped.Term.Bool
import Cvc.Proto2.Tests.Untyped.Term.Arith
import Cvc.Proto2.Tests.Untyped.Term.BitVec
import Cvc.Proto2.Tests.Untyped.Term.Array
import Cvc.Proto2.Tests.Untyped.Term.Set
import Cvc.Proto2.Tests.Untyped.Term.Bag
import Cvc.Proto2.Tests.Untyped.Term.Seq
import Cvc.Proto2.Tests.Untyped.Term.Nullable
import Cvc.Proto2.Tests.Untyped.Term.Nullable.Arith
import Cvc.Proto2.Tests.Untyped.Term.String
import Cvc.Proto2.Tests.Untyped.Term.Regex
import Cvc.Proto2.Tests.Untyped.Term.Float
import Cvc.Proto2.Tests.Untyped.Term.FiniteField
import Cvc.Proto2.Tests.Untyped.Term.Tuple
import Cvc.Proto2.Tests.Untyped.Term.Fun
import Cvc.Proto2.Tests.Untyped.Term.Ext
import Cvc.Proto2.Tests.Untyped.Solver
import Cvc.Proto2.Tests.Untyped.Datatype
import Cvc.Proto2.Tests.Untyped.Grammar
import Cvc.Proto2.Tests.Untyped.Synth
import Cvc.Proto2.Tests.Untyped.BVar
import Cvc.Proto2.Tests.Untyped.Subst
import Cvc.Proto2.Tests.Untyped.Value
import Cvc.Proto2.Tests.Typed.Term.Bool
import Cvc.Proto2.Tests.Typed.Term.Arith
import Cvc.Proto2.Tests.Typed.Term.BitVec
import Cvc.Proto2.Tests.Typed.Term.Array
import Cvc.Proto2.Tests.Typed.Term.Set
import Cvc.Proto2.Tests.Typed.Term.Bag
import Cvc.Proto2.Tests.Typed.Term.Seq
import Cvc.Proto2.Tests.Typed.Term.Nullable
import Cvc.Proto2.Tests.Typed.Term.Nullable.Arith
import Cvc.Proto2.Tests.Typed.Term.Nullable.Theories
import Cvc.Proto2.Tests.Typed.Term.String
import Cvc.Proto2.Tests.Typed.Term.Regex
import Cvc.Proto2.Tests.Typed.Term.Float
import Cvc.Proto2.Tests.Typed.Term.FiniteField
import Cvc.Proto2.Tests.Typed.Term.Tuple
import Cvc.Proto2.Tests.Typed.Term.Fun
import Cvc.Proto2.Tests.Typed.Term.Ext
import Cvc.Proto2.Tests.Typed.Solver
import Cvc.Proto2.Tests.Typed.Datatype
import Cvc.Proto2.Tests.Typed.Grammar
import Cvc.Proto2.Tests.Typed.Synth
import Cvc.Proto2.Tests.Typed.BVar
import Cvc.Proto2.Tests.Typed.Subst
import Cvc.Proto2.Tests.Typed.Value



/-! # Test suite

Run with `lake build Cvc.Proto2.Tests`.

Deliberately *not* imported by `Cvc.Proto2`, so that depending on the library does not drag its
tests in. That also means `lake test` does not cover it: the `cvcTests` library globs `Cvc.Tests`,
and picking these up as well would take adding `Cvc.Proto2.Tests` to that glob in `lakefile.lean`.

Layout mirrors the modules under test:

- `Signatures` — pins the generated signatures of both layers, and the definitional facts
  (`bvConcat`'s size arithmetic, `neg`'s generality over `IsArith`);
- `Untyped/`, `Typed/` — one module per theory, plus `Ext` for that layer's `smt!` DSL.
-/
