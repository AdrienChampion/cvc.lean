/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto.Tests.Srt
import Cvc.Proto.Tests.Signatures
import Cvc.Proto.Tests.Fun
import Cvc.Proto.Tests.Untyped.Term.Bool
import Cvc.Proto.Tests.Untyped.Term.Arith
import Cvc.Proto.Tests.Untyped.Term.BitVec
import Cvc.Proto.Tests.Untyped.Term.Array
import Cvc.Proto.Tests.Untyped.Term.Set
import Cvc.Proto.Tests.Untyped.Term.Bag
import Cvc.Proto.Tests.Untyped.Term.Seq
import Cvc.Proto.Tests.Untyped.Term.String
import Cvc.Proto.Tests.Untyped.Term.Regex
import Cvc.Proto.Tests.Untyped.Term.Float
import Cvc.Proto.Tests.Untyped.Term.FiniteField
import Cvc.Proto.Tests.Untyped.Term.Tuple
import Cvc.Proto.Tests.Untyped.Term.Fun
import Cvc.Proto.Tests.Untyped.Term.Ext
import Cvc.Proto.Tests.Untyped.Solver
import Cvc.Proto.Tests.Untyped.Datatype
import Cvc.Proto.Tests.Untyped.Grammar
import Cvc.Proto.Tests.Untyped.Synth
import Cvc.Proto.Tests.Untyped.BVar
import Cvc.Proto.Tests.Untyped.Value
import Cvc.Proto.Tests.Typed.Term.Bool
import Cvc.Proto.Tests.Typed.Term.Arith
import Cvc.Proto.Tests.Typed.Term.BitVec
import Cvc.Proto.Tests.Typed.Term.Array
import Cvc.Proto.Tests.Typed.Term.Set
import Cvc.Proto.Tests.Typed.Term.Bag
import Cvc.Proto.Tests.Typed.Term.Seq
import Cvc.Proto.Tests.Typed.Term.String
import Cvc.Proto.Tests.Typed.Term.Regex
import Cvc.Proto.Tests.Typed.Term.Float
import Cvc.Proto.Tests.Typed.Term.FiniteField
import Cvc.Proto.Tests.Typed.Term.Tuple
import Cvc.Proto.Tests.Typed.Term.Fun
import Cvc.Proto.Tests.Typed.Term.Ext
import Cvc.Proto.Tests.Typed.Solver
import Cvc.Proto.Tests.Typed.Grammar
import Cvc.Proto.Tests.Typed.Synth
import Cvc.Proto.Tests.Typed.BVar
import Cvc.Proto.Tests.Typed.Value



/-! # Test suite

Run with `lake build Cvc.Proto.Tests`.

Deliberately *not* imported by `Cvc.Proto`, so that depending on the library does not drag its
tests in. That also means `lake test` does not cover it: the `cvcTests` library globs `Cvc.Tests`,
and picking these up as well would take adding `Cvc.Proto.Tests` to that glob in `lakefile.lean`.

Layout mirrors the modules under test:

- `Signatures` — pins the generated signatures of both layers, and the definitional facts
  (`bvConcat`'s size arithmetic, `neg`'s generality over `IsArith`);
- `Untyped/`, `Typed/` — one module per theory, plus `Ext` for that layer's `smt!` DSL.
-/
