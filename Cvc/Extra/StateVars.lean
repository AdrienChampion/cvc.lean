/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Solver



namespace Cvc



abbrev StateVars.Sig := (Var : Type) → Type

class StateVars (S : StateVars.Sig) where
  init [Monad m] [Ω] : (s : S String) → (f : String → Srt → m α) → m (S α)
  foldM [Monad m] : (s : S α) → (f : β → α → m β) → (init : β) → m (S β)
  mapM [Monad m] : (s : S α) → (f : α → m β) → m (S β)

section variable [Ω] [SVars : StateVars S]

def declareStateVars (s : S String) : Env (S Term) := SVars.init s Term.mkConst

def Solver.getStateVarValues (solver : Solver) (s : S Term) : EnvSat (S Term) :=
  SVars.mapM s solver.getValue

end


-- syntax atomic((declModifiers true) "state_vars ") $id:ident (" where " <|> " := ") ppLineIndent
--   ( (declModifiers true) rawIdent )*
