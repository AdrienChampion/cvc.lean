/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Symbols



namespace Cvc.Untyped public section



namespace Symbol

structure At (k : Nat) (W : Symbols.Wrap) (α : Type) [ToTyp α] [TermToValue α] where
private mk' ::
  get : W α

namespace At

instance [ToTyp α] [TermToValue α] (value : At k W α) : CoeDep (At k W α) value (W α) where
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
abbrev Idents [ι : SVars S] : Type := @Symbols.Idents S ι

abbrev TermsAt [SVars S] [Ω] (k : Nat) : Type := S (Symbol.At k (𝕂 Term))

abbrev ValueTermsAt [SVars S] [Ω] (k : Nat) : Type := S (Symbol.At k (𝕂 Term))

abbrev ValuesAt [SVars S] (k : Nat) : Type := S (Symbol.At k fun α => α)

abbrev FunAt [ι : SVars S] (k : Nat) : Type := [Ω] → ι.TermsAt k → Env Term

abbrev Fun [ι : SVars S] : Type := [Ω] → {k : Nat} → ι.TermsAt k → Env Term

abbrev Fun2At [ι : SVars S] (k : Nat) (k' : Nat := k + 1) :=
  [Ω] → ι.TermsAt k → ι.TermsAt k' → Env Term

abbrev Fun2 [ι : SVars S] : Type := [Ω] → {k k' : Nat} → ι.TermsAt k → ι.TermsAt k' → Env Term


namespace Idents variable [ι : SVars S]

private def identAt (k : Nat) (symbol : String) : String :=
  s!"{symbol}__@__{k}"

def declareAt [Ω] (ids : ι.Idents) (k : Nat) : Env (ι.TermsAt k) := do
  ι.mapM ids fun {α} _ _ ident => return ⟨← Term.mkSymbol (← Srt.of α) (identAt k ident)⟩

def declareAtIn [Ω] (ids : ι.Idents) (k : Nat) (solver : Solver) (fresh : Bool := false)
: Env (ι.TermsAt k) := ι.mapM ids fun {α} _ _ ident =>
    return ⟨← Srt.of α >>= solver.declareFun (identAt k ident) #[] (fresh := fresh)⟩

end Idents

namespace TermsAt variable [ι : SVars S]

def getValueTerms [Ω] (terms : ι.TermsAt k) (solver : Solver)
: solver.EnvSat (ι.ValueTermsAt k) := do
  ι.mapM terms fun term => return ⟨← solver.getValue term⟩

def getValues [Ω] (terms : ι.TermsAt k) (solver : Solver) : solver.EnvSat (ι.ValuesAt k) := do
  ι.mapM terms fun {α} _ _ term => return ⟨← solver.getValueAs α term⟩

end TermsAt

end SVars

def Solver.declareSymbolsAt [Ω] [ι : SVars S]
  (s : Solver) (k : Nat) (idents : ι.Idents)
: Env (ι.TermsAt k) :=
  idents.declareAtIn k s
