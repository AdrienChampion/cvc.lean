/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto2.Typed.Term.Array
import Cvc.Proto2.Typed.Term.Bool
import Cvc.Proto2.Typed.Term.Arith

public meta import Cvc.Proto2.Typed.Term.Array
public meta import Cvc.Proto2.Typed.Term.Bool
public meta import Cvc.Proto2.Typed.Term.Arith



/-! # Generated Array constructors, typed -/
namespace Cvc.Proto2.Tests.Typed.Term.Array

open Cvc
open Cvc.Proto2.Typed.Term

/-- info:
select  : (select a i)
store   : (store a i j)
eqRange : (eqrange a a i j)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Proto2.Typed.Term.mkSymbolAs (Cvc.Proto2.TotalMap Int Int) "a"
  let i ← Cvc.Proto2.Typed.Term.mkSymbolAs (Int) "i"
  let j ← Cvc.Proto2.Typed.Term.mkSymbolAs (Int) "j"

  println! "select  : {← select a i}"
  println! "store   : {← store a i j}"
  println! "eqRange : {← eqRange a a i j}"

/-! ## Constructors -/

/-- info: mkConstArray : ((as const (Array Int Int)) 0) -/
#guard_msgs in #eval Env.runIO do
  let zero ← mkInt 0
  println! "mkConstArray : {← (mkConstArray zero : Env (Cvc.Proto2.Typed.Term (Cvc.Proto2.TotalMap Int Int)))}"
