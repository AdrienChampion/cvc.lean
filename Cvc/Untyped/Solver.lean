/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic
import all Cvc.Untyped.Term

public import Cvc.Basic
public import Cvc.Logic
public import Cvc.Untyped.Defs



namespace Cvc.Untyped public section




def Solver [Ω] := cvc5.Solver

/-! ## Solver-mode monadic environment -/
section variable [Ω] [Monad m]

local macro "env_gen% " envT:ident " / " env:ident : command =>
  let pureId := Lean.mkIdent `pure
  let bindId := Lean.mkIdent `bind
  let throwId := Lean.mkIdent `throw
  let tryCatchId := Lean.mkIdent `tryCatch
  let baseIOIdent := Lean.mkIdent ``BaseIO
  `(
abbrev $env := $envT $baseIOIdent

namespace $envT variable {α β : Type} {m : Type → Type} [Monad m]

protected def $pureId (a : α) : $envT m α := ⟨return a⟩
protected def $bindId (a : $envT m α) (f : α → $envT m β) : $envT m β :=
  ⟨a.toEnv.bind (fun a => f a |>.toEnv)⟩

instance [Monad m] : Monad ($envT m) where
  pure := .$pureId
  bind := .$bindId

protected def $throwId (e : Error) : $envT m α := ⟨throw e⟩
protected def $tryCatchId (code : $envT m α) (errorDo : Error → $envT m α) : $envT m α :=
  ⟨code.toEnv.tryCatch fun e => errorDo e |>.toEnv⟩

instance : MonadExcept Error ($envT m) where
  throw := .$throwId
  tryCatch := .$tryCatchId

def transformLift (code : m α) : $envT m α :=
  ⟨code⟩

instance : MonadLift m ($envT m) := ⟨transformLift⟩

/-- Lifts `EnvT`-code.

‼️ dangerous: allows performing check-sat-s, thus changing  -/
private def lift : EnvT m α → $envT m α := .wrap

private instance : MonadLift (EnvT m) ($envT m) := ⟨lift⟩

def liftMonadVersion [Monad m] [MonadLiftT BaseIO m] (code : $env α) : $envT m α :=
  ⟨liftM code.toEnv⟩
instance [Monad m] [MonadLiftT BaseIO m] : MonadLift $env ($envT m) := ⟨liftMonadVersion⟩
end $envT
  )

structure EnvSatT [Ω] (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvSatT / EnvSat

structure EnvUnsatT (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvUnsatT / EnvUnsat

structure EnvUnknownT (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvUnknownT / EnvUnknown



namespace Solver variable [Ω] open cvc5 renaming TermManager → Tm, Solver → S

/-- Creates a new solver. -/
def new : Env Solver := runUnsafe (S.new ·)

section variable [MonadLiftT BaseIO m] (s : Solver)

/-- Conversion to cvc5. -/
private def toUnsafe : S := s



def Result := cvc5.Result

namespace Result

private def toUnsafe : Result → cvc5.Result := id
private def ofUnsafe : cvc5.Result → Result := id

section variable (r : Result)

protected def toString : String := r.toUnsafe.toString
instance : ToString Result := ⟨Result.toString⟩

private def isSat! : Bool := r.toUnsafe.isSat
private def isUnsat! : Bool := r.toUnsafe.isUnsat
private def isUnknown! : Bool := r.toUnsafe.isUnknown
private def getUnknownExplanation? : Option Unknown.Explanation :=
  r.toUnsafe.getUnknownExplanation? |>.map Unknown.Explanation.ofUnsafe

abbrev Sat? := Bool ⊕ Unknown.Explanation

def isSat? : Res Sat? :=
  if r.isSat then return .inl true
  else if r.isUnsat then return .inl false
  else if let some unkExpl := r.getUnknownExplanation? then return .inr unkExpl
  else throwInternal s!"check result is neither sat, unsat, or unknown\n{r}"

def isSat : Res Bool := r.isSat? >>= fun
  | .inl res => return res
  | .inr unkExpl => throwUser s!"unexpected unknown result: {unkExpl}"


end

end Result



@[inherit_doc S.getVersion]
def getVersion : Env String := runUnsafe' do
  s.toUnsafe.getVersion

@[inherit_doc S.setOption]
def setOption (option value : String) : Env Unit := runUnsafe' do
  s.toUnsafe.setOption option value

@[inherit_doc S.getOption]
def getOption (flag : String) : Env String := runUnsafe' do
  s.toUnsafe.getOption flag

@[inherit_doc S.getOptionNames]
def getOptionNames : Env (Array String) := runUnsafe' do
  s.toUnsafe.getOptionNames

@[inherit_doc S.setInfo]
def setInfo (option value : String) : Env Unit := runUnsafe' do
  s.toUnsafe.setInfo option value

@[inherit_doc S.getInfo]
def getInfo (flag : String) : Env String := runUnsafe' do
  s.toUnsafe.getInfo flag

@[inherit_doc S.setLogic]
def setLogic (logic : Logic) : Env Unit := runUnsafe' do
  s.toUnsafe.setLogic logic.toSmtLib

@[inherit_doc S.isLogicSet]
def isLogicSet : Env Bool := runUnsafe' do
  s.toUnsafe.isLogicSet

@[inherit_doc S.getLogic]
def getLogicString : Env String := runUnsafe' do
  s.toUnsafe.getLogic

@[inherit_doc S.getLogic]
def getLogic : Env Logic := s.getLogicString >>= liftM ∘ Logic.ofSmtLib

@[inherit_doc S.getAssertions]
def getAssertions : Env Terms := runUnsafe' do
  s.toUnsafe.getAssertions

@[inherit_doc S.getInstantiations]
def getInstantiations : Env String := runUnsafe' do
  s.toUnsafe.getInstantiations



@[inherit_doc S.resetAssertions]
def reset : Env Unit := runUnsafe' do
  s.toUnsafe.resetAssertions

@[inherit_doc S.push]
def push (nscopes : UInt32 := 1) : Env Unit := runUnsafe' do
  s.toUnsafe.push nscopes

@[inherit_doc S.pop]
def pop (nscopes : UInt32 := 1) : Env Unit := runUnsafe' do
  s.toUnsafe.pop nscopes



@[inherit_doc S.assertFormula]
def assert (t : Term) : Env Unit := runUnsafe' do
  s.toUnsafe.assertFormula t

@[inherit_doc S.declareFun]
def declareFun (symbol : String) (sorts : Srts) (sort : Srt) (fresh : Bool := true) : Env Term :=
  runUnsafe' do s.toUnsafe.declareFun symbol sorts sort fresh

/-- Declares a constant function symbol. -/
def declareConst (symbol : String) (sort : Srt) (fresh : Bool := true) : Env Term :=
  s.declareFun symbol #[] sort (fresh := fresh)

@[inherit_doc S.declareSort]
def declareSrt
  (symbol : String) (arity : UInt32) (fresh : Bool := false)
: Env Srt :=
  runUnsafe' do s.toUnsafe.declareSort symbol arity fresh

@[inherit_doc S.defineFun]
def defineFun
  (symbol : String) (boundVars : Terms) (sort : Srt) (body : Term) (global : Bool := false)
: Env Term :=
  runUnsafe' do s.toUnsafe.defineFun symbol boundVars sort body global

/-- Defines a constant function symbol. -/
def defineConst (symbol : String) (sort : Srt) (body : Term) (global : Bool := false) : Env Term :=
  s.defineFun symbol #[] sort body (global := global)

@[inherit_doc S.defineFunRec]
def defineFunRec
  (symbol : String) (boundVars : Terms) (sort : Srt) (body : Term) (global : Bool := false)
: Env Term :=
  runUnsafe' do s.toUnsafe.defineFunRec symbol boundVars sort body global

@[inherit_doc S.defineFunRecTerm]
def defineFunRecTerm
  (fn : Term) (boundVars : Terms) (body : Term) (global : Bool := false)
: Env Term :=
  runUnsafe' do s.toUnsafe.defineFunRecTerm fn boundVars body global

@[inherit_doc S.defineFunsRec]
def defineFunsRec
  (funs : Terms) (boundVars : Array Terms) (bodies : Terms) (global : Bool := false)
: Env Unit :=
  runUnsafe' do s.toUnsafe.defineFunsRec funs boundVars bodies global



@[inherit_doc S.getQuantifierElimination]
def qe (q : Term) : Env Term := runUnsafe' do s.toUnsafe.getQuantifierElimination q

@[inherit_doc S.getQuantifierEliminationDisjunct]
def qeDisjunct (q : Term) : Env (Option Term) := do
  let term ← runUnsafe' do s.toUnsafe.getQuantifierEliminationDisjunct q
  return if term.isNull then none else some term

@[inherit_doc S.getInterpolant]
def getInterpolant (conj : Term) (grammar : Option Grammar := none) : Env Term :=
  runUnsafe' do s.toUnsafe.getInterpolant conj grammar

@[inherit_doc S.getInterpolantNext]
def getNextInterpolant : Env (Option Term) := do
  let term ← runUnsafe' do s.toUnsafe.getInterpolantNext
  return if term.isNull then none else some term

@[inherit_doc S.getAbduct]
def getAbduct (conj : Term) (grammar : Option Grammar := none) : Env Term :=
  runUnsafe' do s.toUnsafe.getAbduct conj grammar

@[inherit_doc S.getAbductNext]
def getNextAbduct : Env (Option Term) := do
  let term ← runUnsafe' do s.toUnsafe.getAbductNext
  return if term.isNull then none else some term

@[inherit_doc S.proofToString]
def proofToString (proof : Proof)
  (format : Proof.Format := default)
: Env (Option String) :=
  runUnsafe' do s.toUnsafe.proofToString proof format.toUnsafe

@[inherit_doc S.getLearnedLiterals]
def getLearnedLiterals (t : LearnedLitType := LearnedLitType.input) : Env Terms :=
  runUnsafe' do s.toUnsafe.getLearnedLiterals t.toUnsafe



section unexpected

private def unexpectedResult (badResDesc : String) (dumpAssertions : Bool)
  (explanation : Option String := none)
: Env α := do
  let _ := s
  let mut msg := s!"unexpected `{badResDesc}` result"
  if let some e := explanation then msg := s!"{msg}\n- {e}"
  if dumpAssertions then
    let assertions ← s.getAssertions
    if assertions.isEmpty then
      msg := s!"{msg}, solver does not have any assertions"
    else
      msg := msg ++ " for the following assertions\n```smtlib"
        |> assertions.foldl (s!"{·}\n(assert {·})")
      msg := msg ++ "\n```"
  throwUser msg

variable (e : Unknown.Explanation) (dumpAssertions : Bool := false)

/-- Fails if `sat` was unexpected, shows all assertions if `dumpAssertions` (default false). -/
def unexpectedSat : EnvSat α := s.unexpectedResult "sat" dumpAssertions
/-- Fails if `unsat` was unexpected, shows all assertions if `dumpAssertions` (default false). -/
def unexpectedUnsat : EnvUnsat α := s.unexpectedResult "unsat" dumpAssertions
/-- Fails if `unknown` was unexpected, shows all assertions if `dumpAssertions` (default false). -/
def unexpectedUnknown : EnvUnknown α :=
  s.unexpectedResult "unknown" dumpAssertions (explanation := toString e)

end unexpected



section check_sat variable (assuming : Option Terms := none)

/-- Checks the satisfiability of the constraints asserted so far. -/
def checkSatResult : Env Result := do
  let code := if let some terms := assuming then S.checkSatAssuming s terms else S.checkSat s
  Result.ofUnsafe <$> runUnsafe' code

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
  (ifSat : EnvSatT m α := s.unexpectedSat)
  (ifUnsat : EnvUnsatT m α := s.unexpectedUnsat)
  (ifUnknown : Unknown.Explanation → EnvUnknownT m α := liftM ∘ s.unexpectedUnknown)
: EnvT m α := do
  match ← s.checkIsSat? (assuming := assuming) with
  | .inl true => ifSat.toEnv
  | .inl false => ifUnsat.toEnv
  | .inr unkExpl => ifUnknown unkExpl |>.toEnv

@[inherit_doc checkSatResult]
def checkSat? {α : Type} (s : Solver) (assuming : Option Terms := none)
  (ifSat : EnvSatT m (Option α) := return none)
  (ifUnsat : EnvUnsatT m (Option α) := return none)
  (ifUnknown : Unknown.Explanation → EnvUnknownT m (Option α) := liftM ∘ s.unexpectedUnknown)
: EnvT m (Option α) :=
  s.checkSat assuming ifSat ifUnsat ifUnknown

end check_sat



section sat

/-- Get the value of `term` in the current model.

# TODO
- requires model-production
-/
def getValue (term : Term) : EnvSat Term := runUnsafe' do s.toUnsafe.getValue term
/-- Get the value of each term in  `terms` in the current model.

# TODO
- requires model-production
-/
def getValues (terms : Terms) : EnvSat Terms := runUnsafe' do s.toUnsafe.getValues terms

@[inherit_doc S.getModelDomainElements]
def getModelDomainElements (sort : Srt) : EnvSat Terms :=
  runUnsafe' do s.toUnsafe.getModelDomainElements sort

@[inherit_doc S.isModelCoreSymbol]
def isModelCoreSymbol (term : Term) : EnvSat Bool :=
  runUnsafe' do s.toUnsafe.isModelCoreSymbol term

@[inherit_doc S.getModel]
def getModelAsString (sorts : Srts) (consts : Terms) : EnvSat String :=
  runUnsafe' do s.toUnsafe.getModel sorts consts

@[inherit_doc S.blockModel]
def blockModel (mode : Model.BlockMode) : EnvSat Unit :=
  runUnsafe' do s.toUnsafe.blockModel mode.toUnsafe

@[inherit_doc S.blockModelValues]
def blockModelValues (terms : Terms) : EnvSat Unit :=
  runUnsafe' do s.toUnsafe.blockModelValues terms

end sat



section unsat

@[inherit_doc S.getUnsatAssumptions]
def getUnsatAssumptions: EnvUnsat Terms := runUnsafe' do s.toUnsafe.getUnsatAssumptions

@[inherit_doc S.getProof]
def getUnsatProof (c : Proof.Component := Proof.Component.full) : EnvUnsat (Array Proof) :=
  runUnsafe' do s.toUnsafe.getProof c.toUnsafe

@[inherit_doc S.getUnsatCore]
def getUnsatCore : EnvUnsat Terms := runUnsafe' do s.toUnsafe.getUnsatCore

@[inherit_doc S.getUnsatCoreLemmas]
def getUnsatCoreLemmas : EnvUnsat Terms := runUnsafe' do s.toUnsafe.getUnsatCoreLemmas

end unsat



section unknown

@[inherit_doc S.getTimeoutCore]
def getTimeoutCore : EnvUnknown (cvc5.Result × Terms) := runUnsafe' do s.toUnsafe.getTimeoutCore

@[inherit_doc S.getTimeoutCoreAssuming]
def getTimeoutCoreAssuming (assumptions : Terms) : EnvUnknown (cvc5.Result × Terms) :=
  runUnsafe' do s.toUnsafe.getTimeoutCoreAssuming assumptions

end unknown

end

end Solver
