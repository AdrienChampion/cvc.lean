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

public import Cvc.Proto2.Untyped.Term.Nullable.Regex
public import Cvc.Proto2.Typed.Term.Regex
public import Cvc.Proto2.Typed.Term.Defs
public import Cvc.Proto2.Typed.Term.Nullable
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Spec.Regex



/-! # Regular expressions over nullables, typed

Each lifted operator has its plain counterpart's signature with an `Option` around every argument
and around the result, and nothing else changed. The lift is **strict**: `none` unless every
argument is `some`.

The regex *term* becomes nullable. Note the string-matching operators live in the string theory,
so `strInRe?` is generated there.
-/
namespace Cvc.Proto2.Typed.Term public section

open Cvc.Proto2 renaming Untyped.Term → T

variable [Ω]

gen_typed_nullable% from Cvc.Proto2.Spec.Regex
