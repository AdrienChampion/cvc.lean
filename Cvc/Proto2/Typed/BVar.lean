/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Proto2.Untyped.BVar
public import Cvc.Proto2.Typed.Term.Bool

import all Cvc.Proto2.Untyped.BVar
-- `import all` and not a plain `import`: `BVar α` is `Term α` is `Untyped.Term`, and that chain is
-- what lets a typed bound variable be built by the sort-erased constructor
import all Cvc.Proto2.Typed.Term.Defs



namespace Cvc.Proto2.Typed public section variable [Ω]



/-- A bound variable. -/
def BVar (α : Type) := Term α

namespace Term

/-- A bound variable of the sort `α` describes.

Only meaningful under a binder: the bound variables of a definition's body, or of a quantifier,
lambda or witness. Each call produces a fresh variable even for the same name and sort.
-/
def mkBVar' (α : Type) [ToTyp α] (name : String) : Env (BVar α) := do
  Untyped.Term.mkBVar (← Srt.of α) name

@[inherit_doc mkBVar']
abbrev mkBVar [ToTyp α] (name : String) : Env (BVar α) := mkBVar' α name

end Term

namespace BVar

@[inherit_doc Term.mkBVar']
def mk [ToTyp α] (name : String) : Env (BVar α) := Term.mkBVar' α name

/-- Turns itself into a term. -/
def toTerm : (bv : BVar α) → Term α := id

instance : Coe (BVar α) (Term α) := ⟨toTerm⟩

end BVar

abbrev BVars := List ((α : Type) × ToTyp α × BVar α)

namespace BVars

abbrev push [ToTyp α] (bv : BVar α) (bvs : BVars) : BVars :=
  ⟨α, inferInstance, bv⟩ :: bvs

abbrev signatureTo (β : Type) : (bvs : BVars) → Type
  | [] => β
  | ⟨α, _, _⟩ :: bvs => signatureTo (α → β) bvs

def erase (bvs : BVars) : Untyped.BVars :=
  bvs.foldr (init := Array.mkEmpty bvs.length) fun ⟨_, _, bv⟩ acc => acc.push bv.erase

def toTerms (bvs : BVars) : Untyped.Terms :=
  bvs.erase

end BVars
