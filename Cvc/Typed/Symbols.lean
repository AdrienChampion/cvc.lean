/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Solver



namespace Cvc.Typed variable [Ω] open Cvc.Typed renaming Term → T



structure Symbol (F : Type → Type) (α : Type) where
  get : F α


namespace Symbol

instance : Coe (Symbol F α) (F α) := ⟨get⟩

abbrev Ident := Symbol (𝕂 String)

abbrev Value := Symbol Id

abbrev Term := Symbol T

structure TermAt (k : Nat) (α : Type) extends toTerm : Term α where private mk' ::

structure ValueAt (k : Nat) (α : Type) extends toValue : Value α where private mk' ::

/-- The `Cvc.Typed.Term` in a `Symbol.Term`. -/
def toTerm (symbol : Term α) : T α := symbol.get

def declare [ToTyp α] (symbol : Ident α) : Env (Term α) :=
  return { symbol with get := ← Term.mkSymbol symbol.get }

def declareAt [ToTyp α] (symbol : Ident α) (k : Nat) : Env (TermAt k α) :=
  let ident := s!"{symbol.get}__@__{k}"
  return { get := ← Term.mkSymbol ident }

def getValue [TermToValue α] (symbol : Term α) (solver : Solver) : EnvSat (Value α) :=
  return {get := ← solver.getValue symbol.get}

def getValueTerm (symbol : Term α) (solver : Solver) : EnvSat (Term α) :=
  return {get := ← solver.getValueTerm symbol.get}

namespace TermAt

def mk [ToTyp α] (symbol : Ident α) (k : Nat) : Env (TermAt k α) :=
  symbol.declareAt k

def getValue [TermToValue α] (symbol : TermAt k α) (solver : Solver) : EnvSat (ValueAt k α) :=
  return {get := ← solver.getValue symbol.get}

def getValueTerm [TermToValue α] (symbol : TermAt k α) (solver : Solver) : EnvSat (TermAt k α) :=
  return {get := ← solver.getValueTerm symbol.get}

end TermAt

end Symbol



class Symbols (S : (Type → Type) → Type) where
  mapM [Monad m] {F' : Type → Type} (syms : S F)
    (f : {α : Type} → [ToTyp α] → [TermToValue α] → F α → m (F' α))
  : m (S F')

namespace Symbols

abbrev Idents (S : (Type → Type) → Type) [Symbols S] := S Symbol.Ident
abbrev Terms (S : (Type → Type) → Type) [Symbols S] := S Symbol.Term
abbrev TermsAt (k : Nat) (S : (Type → Type) → Type) [Symbols S] := S (Symbol.TermAt k)
abbrev Values (S : (Type → Type) → Type) [Symbols S] := S Symbol.Value
abbrev ValuesAt (k : Nat) (S : (Type → Type) → Type) [Symbols S] := S (Symbol.ValueAt k)

variable [inst : Symbols S]

def declare (syms : Idents S) : Env (Terms S) :=
  inst.mapM syms fun sym => sym.declare

def declareAt (syms : Idents S) : Env (TermsAt k S) :=
  inst.mapM syms fun sym => sym.declareAt k

def Terms.getValues (syms : Terms S) (solver : Solver) : EnvSat (Values S) :=
  inst.mapM syms fun sym => sym.getValue solver

def TermsAt.getValues (syms : TermsAt k S) (solver : Solver) : EnvSat (ValuesAt k S) :=
  inst.mapM syms fun sym => sym.getValue solver

end Symbols
