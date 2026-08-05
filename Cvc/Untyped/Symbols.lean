/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Untyped.Solver

public import Cvc.Untyped.Solver
public import Cvc.Untyped.Term



namespace Cvc public section variable [Ω] open Cvc renaming Untyped.Term → T

open Untyped



structure Symbol (α T : Type) where
  get : T


namespace Symbol

instance : CoeDep (Symbol α T) sym T := ⟨sym.get⟩

abbrev Ident (α : Type) := Symbol α String

abbrev Term (α : Type) := Symbol α T

abbrev ValueTerm (α : Type) := Symbol α T

abbrev Value (α : Type) := Symbol α α

structure TermAt (k : Nat) (α : Type) extends Symbol.Term α where private mk' ::

structure ValueTermAt (k : Nat) (α : Type) extends ValueTerm α

structure ValueAt (k : Nat) (α : Type) extends Value α

/-- The `Cvc.Term` in a `Symbol.Term`. -/
def toTerm (symbol : Term α) : T := symbol.get

def declare [ToTyp α] (symbol : Ident α) : Env (Symbol.Term α) := do
  let srt ← Srt.of α
  return { get := ← Term.mkSymbol symbol.get srt }

def declareAt [ToTyp α] (symbol : Ident α) (k : Nat) : Env (TermAt k α) := do
  let ident := s!"{symbol.get}__@__{k}"
  let srt ← Srt.of α
  return { get := ← Term.mkSymbol ident srt }

def getValueTerm (symbol : Symbol.Term α) (solver : Solver) : EnvSat (ValueTerm α) :=
  return { get := ← solver.getValue symbol.get }

def getValue [TermToValue α] (symbol : Symbol.Term α) (solver : Solver) : EnvSat (Value α) := do
  let termValue ← solver.getValue symbol.get
  return { get := ← Term.getValueAs α termValue }

namespace TermAt variable (symbol : TermAt k α)

-- private def mk [ToTyp α] (symbol : String) (k : Nat) (sort : Srt) : Env (TermAt α k) := do
--   declareAt ⟨symbol⟩ k

/-- The `Cvc.Term` in a `TermAt _`. -/
def toTerm : T := symbol.get

def getValueTerm (solver : Solver) : EnvSat (ValueTermAt k α) := do
  return ⟨← Symbol.getValueTerm symbol.toSymbol solver⟩

def getValue [TermToValue α] (solver : Solver) : EnvSat (ValueAt k α) := do
  return ⟨← Symbol.getValue symbol.toSymbol solver⟩

end TermAt

end Symbol



class Symbols (S : (Type → Type) → Type) where
  foldM [Monad m] {σ : Type} (syms : S F)
    (f : {α : Type} → [SrtLike α] → σ → F α → m σ) (init : σ)
  : m σ
  mapM [Monad m] (syms : S F)
    (f : {α : Type} → [SrtLike α] → F α → m (F' α))
  : m (S F')

namespace Symbols

abbrev Idents (S : (Type → Type) → Type) [Symbols S] := S Symbol.Ident
abbrev Terms (S : (Type → Type) → Type) [Symbols S] := S Symbol.Term
abbrev TermsAt (k : Nat) (S : (Type → Type) → Type) [Symbols S] := S (Symbol.TermAt k)
abbrev Values (S : (Type → Type) → Type) [Symbols S] := S Symbol.Value
abbrev ValuesAt (k : Nat) (S : (Type → Type) → Type) [Symbols S] := S (Symbol.ValueAt k)

variable [inst : Symbols S]

def Idents.declare (syms : Idents S) : Env (Terms S) :=
  inst.mapM syms fun sym => sym.declare

def Idents.declareAt (syms : Idents S) : Env (TermsAt k S) :=
  inst.mapM syms fun sym => sym.declareAt k

def Terms.getValues (syms : Terms S) (solver : Solver) : EnvSat (Values S) :=
  inst.mapM syms fun sym => sym.getValue solver

def TermsAt.getValues (syms : TermsAt k S) (solver : Solver) : EnvSat (ValuesAt k S) :=
  inst.mapM syms fun sym => sym.getValue solver

end Symbols
