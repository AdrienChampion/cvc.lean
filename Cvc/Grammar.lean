/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Defs

public import Cvc.Untyped.Defs



namespace Cvc.Grammar variable [Ω] (g : Grammar)

open cvc5 renaming Grammar → G



@[inherit_doc G.addRule]
def addRule (ntSymbol : Term) (rule : Term) : Env Grammar :=
  runUnsafe' do liftM <| g.toUnsafe.addRule ntSymbol rule

@[inherit_doc G.addRules]
def addRules (ntSymbol : Term) (rules : Terms) : Env Grammar :=
  runUnsafe' do g.toUnsafe.addRules ntSymbol rules

@[inherit_doc G.addAnyConstant]
def addAnyConstant (ntSymbol : Term) : Env Grammar :=
  runUnsafe' do g.toUnsafe.addAnyConstant ntSymbol

@[inherit_doc G.addAnyVariable]
def addAnyVariable (ntSymbol : Term) : Env Grammar :=
  runUnsafe' do g.toUnsafe.addAnyVariable ntSymbol
