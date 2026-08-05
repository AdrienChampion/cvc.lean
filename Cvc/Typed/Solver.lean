module

import all Cvc.Untyped.Solver
import all Cvc.Typed.Term

public import Cvc.Untyped.Solver
public import Cvc.Typed.Term



namespace Cvc.Typed public section variable [Ω]

open Cvc.Untyped renaming Solver → S



abbrev Solver := S

export Cvc.Untyped (EnvSatT EnvSat EnvUnsatT EnvUnsat EnvUnknownT EnvUnknown)

namespace Solver variable (s : Solver)

export Cvc.Untyped.Solver (Result)
open Cvc.Untyped.Solver (Result)

def new : Env Solver := S.new

def get : Solver → S := id

def getAssertions : Env (Terms Bool) := S.getAssertions s

def assert (t : Term Bool) : Env Unit := S.assert s t



section check_sat variable [Monad m] [MonadLiftT BaseIO m] (assuming : Option (Terms Bool) := none)

/-- Checks the satisfiability of the constraints asserted so far. -/
def checkSatResult : Env Result := S.checkSatResult s (assuming := assuming)

@[inherit_doc checkSatResult]
def checkIsSat? : Env Result.Sat? := do
  let res ← s.checkSatResult assuming
  res.isSat?

@[inherit_doc checkSatResult]
def checkIsSat : Env Bool := do
  let res ← s.checkSatResult assuming
  res.isSat

@[inherit_doc checkSatResult]
def checkSat
  (ifSat : EnvSatT m α := liftM (S.unexpectedSat s))
  (ifUnsat : EnvUnsatT m α := s.unexpectedUnsat)
  (ifUnknown : Unknown.Explanation → EnvUnknownT m α := liftM ∘ s.unexpectedUnknown)
: EnvT m α := do
  match ← s.checkIsSat? (assuming := assuming) with
  | .inl true => ifSat.toEnv
  | .inl false => ifUnsat.toEnv
  | .inr unkExpl => ifUnknown unkExpl |>.toEnv

@[inherit_doc checkSatResult]
def checkSat?
  (ifSat : EnvSatT m (Option α) := return none)
  (ifUnsat : EnvUnsatT m (Option α) := return none)
  (ifUnknown : Unknown.Explanation → EnvUnknownT m (Option α) := liftM ∘ s.unexpectedUnknown)
: EnvT m (Option α) :=
  s.checkSat assuming ifSat ifUnsat ifUnknown

end check_sat



section sat

@[inherit_doc S.getValue]
def getValueTerm (term : Term α) : EnvSat (Term α) := s.getValue term
@[inherit_doc S.getValues]
def getValueTerms (terms : Terms α) : EnvSat (Terms α) :=
  runUnsafe' do s.toUnsafe.getValues terms

@[inherit_doc getValueTerm]
def getValue [TermToValue α] (s : Solver) (term : Term α) : EnvSat α := do
  let valTerm ← s.getValueTerm term
  valTerm.getValue
@[inherit_doc getValueTerms]
def getValues [TermToValue α] (s : Solver) (ts : Terms α) : EnvSat (Array α) := do
  let valTerms ← s.getValueTerms ts
  valTerms.mapM (Term.getValue ·)

@[inherit_doc S.isModelCoreSymbol]
def isModelCoreSymbol (term : Term α) : EnvSat Bool :=
  runUnsafe' do s.toUnsafe.isModelCoreSymbol term

end sat



section unsat

@[inherit_doc S.getUnsatAssumptions]
def getUnsatAssumptions: EnvUnsat (Terms Bool) := runUnsafe' do s.toUnsafe.getUnsatAssumptions

@[inherit_doc S.getUnsatCore]
def getUnsatCore : EnvUnsat (Terms Bool) := runUnsafe' do s.toUnsafe.getUnsatCore

@[inherit_doc S.getUnsatCoreLemmas]
def getUnsatCoreLemmas : EnvUnsat (Terms Bool) := runUnsafe' do s.toUnsafe.getUnsatCoreLemmas

end unsat



section unknown

@[inherit_doc S.getTimeoutCore]
def getTimeoutCore : EnvUnknown (cvc5.Result × Terms Bool) :=
  runUnsafe' do s.toUnsafe.getTimeoutCore

@[inherit_doc S.getTimeoutCoreAssuming]
def getTimeoutCoreAssuming (assumptions : Terms Bool) : EnvUnknown (cvc5.Result × Terms Bool) :=
  runUnsafe' do s.toUnsafe.getTimeoutCoreAssuming assumptions

end unknown

end Solver
