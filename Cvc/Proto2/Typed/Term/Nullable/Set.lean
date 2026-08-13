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

public import Cvc.Proto2.Untyped.Term.Nullable.Set
public import Cvc.Proto2.Typed.Term.Set
public import Cvc.Proto2.Typed.Term.Defs
public import Cvc.Proto2.Typed.Term.Nullable
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Spec.Set



/-! # Sets over nullables, typed

Each lifted operator has its plain counterpart's signature with an `Option` around every argument
and around the result, and nothing else changed. The lift is **strict**: `none` unless every
argument is `some`.

The set *term* becomes nullable, not its elements — `Option (Set α)`, not `Set (Option α)`. The
element type is untouched, so the `Ord` binders are the plain operators'.
-/
namespace Cvc.Proto2.Typed.Term public section

open Cvc.Proto2 renaming Untyped.Term → T

variable [Ω]

gen_typed_nullable% from Cvc.Proto2.Spec.Set
