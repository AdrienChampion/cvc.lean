/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Proto2.Env
import all Cvc.Proto2.Untyped.Term.Defs
import all Cvc.Proto2.Typed.Term.Defs

public import Cvc.Proto2.Untyped.Term.Nullable.Arith
public import Cvc.Proto2.Typed.Term.Defs
public import Cvc.Proto2.Typed.Term.Nullable
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Spec.Arith



/-! # Arithmetic over nullables, typed

Each lifted operator has its plain counterpart's signature with an `Option` around every argument
and around the result, so `add? : Term (Option α) → Term (Option α) → Env (Term (Option α))` under
the same `IsArith α`. Everything the plain operator checks is checked here.

The lift is **strict**: `none` unless every argument is `some`.
-/
namespace Cvc.Proto2.Typed.Term public section

open Cvc.Proto2 renaming Untyped.Term → T

variable [Ω]

gen_typed_nullable% from Cvc.Proto2.Spec.Arith
