/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Proto2.Untyped.Term.Bool

import all Cvc.Proto2.Env
import all Cvc.Proto2.Srt
import all Cvc.Proto2.Untyped.Term.Defs



namespace Cvc.Proto2.Untyped public section variable [Ω]



/-- A bound variable. -/
def BVar := Term

/-- An array of bound variables. -/
abbrev BVars := Array BVar

namespace Term

/-- A bound variable of the given sort.

Only meaningful under a binder: the bound variables of a definition's body, or of a quantifier,
lambda or witness. Each call produces a fresh variable even for the same name and sort.
-/
def mkBVar (srt : Srt) (name : String) : Env BVar :=
  runUnsafe fun tm => tm.mkVar srt.toUnsafe name

end Term

namespace BVar

@[inherit_doc Term.mkBVar]
def mk (srt : Srt) (name : String) : Env BVar := Term.mkBVar srt name

/-- Turns itself into a term. -/
def toTerm : (bv : BVar) → Term := id

instance : Coe BVar Term := ⟨toTerm⟩

end BVar
