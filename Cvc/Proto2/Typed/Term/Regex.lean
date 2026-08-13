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

public import Cvc.Proto2.Untyped.Term.Regex
public import Cvc.Proto2.Typed.Term.Defs
public import Cvc.Proto2.Ext
public import Cvc.Proto2.Typed.Term.Value
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Spec.Regex



/-! # Generated Regex constructors, typed -/
namespace Cvc.Proto2.Typed.Term public section

open Cvc.Proto2 renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Proto2.Spec.Regex



/-! ## Values

A regular expression reads back only as a term for now: cvc5 exposes no accessor for the language
a constant regex denotes, and nothing reconstructs one from a `Cvc.Proto2.Regex`.
-/

@[inherit_doc T.getRegexValue]
def getRegexValue (term : Term Regex) : Env Regex := T.getRegexValue term

instance : SrtLike Regex where
  valueToTerm _value := throwTodo "value-to-term for `Regex`"
  termToValue := getRegexValue
