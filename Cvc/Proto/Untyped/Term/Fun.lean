/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Proto.Untyped.Term.Defs

public import Cvc.Proto.Untyped.Term.Defs
public import Cvc.Proto.Ext
public import Cvc.Proto.Gen
public import Cvc.Proto.Spec.Fun



/-! # Generated function-application constructors, sort-erased -/
namespace Cvc.Proto.Untyped.Term public section

variable [Ω]

gen_untyped% from Cvc.Proto.Spec.Fun
