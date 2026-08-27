/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Typed.Symbols



namespace Cvc.Typed public section



namespace Symbol

structure At (k : Nat) (W : Symbols.Wrap) (α : Type) [ToTyp α] [TermToValue α] where
private mk' ::
  get : W α

namespace At

instance [ToTyp α] [TermToValue α] (value : At k W α) : CoeDep (At k W α) value (W α) where
  coe := value.get

instance [Ω] [ToTyp α] [TermToValue α] (value : At k (Term ·) α)
: CoeDep (At k (Term ·) α) value (Term α) where
  coe := value.get

end At

end Symbol



abbrev SVars (S : Symbols.Sig) := Symbols S


namespace SVars

@[inherit_doc Symbols.Wrap]
abbrev Wrap := Symbols.Wrap

@[inherit_doc Symbols.Sig]
abbrev Sig := Symbols.Sig

@[inherit_doc Symbols.Idents]
abbrev Idents [ι : SVars S] := @Symbols.Idents S ι

abbrev TermsAt [SVars S] [Ω] (k : Nat) : Type := S (Symbol.At k (Term ·))

abbrev ValueTermsAt [SVars S] [Ω] (k : Nat) : Type := S (Symbol.At k (Term ·))

abbrev ValuesAt [SVars S] (k : Nat) : Type := S (Symbol.At k fun α => α)

abbrev FunAt [ι : SVars S] (k : Nat) (α : Type) : Type := [Ω] → ι.TermsAt k → Env (Term α)

abbrev Fun [ι : SVars S] (α : Type) : Type := [Ω] → {k : Nat} → ι.TermsAt k → Env (Term α)

abbrev PredAt [ι : SVars S] (k : Nat) : Type := [Ω] → ι.TermsAt k → Env (Term Bool)

abbrev Pred [ι : SVars S] : Type := [Ω] → {k : Nat} → ι.TermsAt k → Env (Term Bool)

abbrev Fun2At [ι : SVars S] (k : Nat) (α : Type) (k' : Nat := k + 1) :=
  [Ω] → ι.TermsAt k → ι.TermsAt k' → Env (Term α)

abbrev Fun2 [ι : SVars S] (α : Type) :=
  [Ω] → {k k' : Nat} → ι.TermsAt k → ι.TermsAt k' → Env (Term α)

abbrev RelAt [ι : SVars S] (k : Nat) (k' : Nat := k + 1) :=
  [Ω] → ι.TermsAt k → ι.TermsAt k' → Env (Term Bool)

abbrev Rel [ι : SVars S] := [Ω] → {k k' : Nat} → ι.TermsAt k → ι.TermsAt k' → Env (Term Bool)


namespace Idents variable [ι : SVars S]

/-- Declare `ids` as symbols at depth `k`. -/
def declareAt [Ω] (k : Nat) (ids : ι.Idents) : Env (ι.TermsAt k) := do
  ι.mapM ids fun ident => return ⟨← Term.mkSymbol ident⟩

/-- Declare `ids` as symbols at depth `k`. -/
def declareAtIn [Ω] (k : Nat) (ids : ι.Idents) (solver : Solver) : Env (ι.TermsAt k) := do
  ι.mapM ids fun ident => return ⟨← solver.declareFun ident⟩

end Idents

namespace TermsAt variable [ι : SVars S]

def getValues [Ω] (terms : ι.TermsAt k) (solver : Solver) : solver.EnvSat (ι.ValuesAt k) := do
  ι.mapM terms fun term => return ⟨← solver.getValue term⟩

end TermsAt

end SVars

namespace Solver

@[inherit_doc SVars.Idents.declareAtIn]
abbrev declareSymbolsAt := @SVars.Idents.declareAtIn

end Solver
