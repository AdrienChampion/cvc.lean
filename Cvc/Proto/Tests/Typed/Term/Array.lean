/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto.Typed.Term.Array
import Cvc.Proto.Typed.Term.Bool
import Cvc.Proto.Typed.Term.Arith

public meta import Cvc.Proto.Typed.Term.Array
public meta import Cvc.Proto.Typed.Term.Bool
public meta import Cvc.Proto.Typed.Term.Arith



/-! # Generated Array constructors, typed -/
namespace Cvc.Proto.Tests.Typed.Term.Array

open Cvc
open Cvc.Proto.Typed.Term

/-- info:
select  : (select a i)
store   : (store a i j)
eqRange : (eqrange a a i j)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Proto.Typed.Term.mkSymbolAs (Cvc.Proto.TotalMap Int Int) "a"
  let i ← Cvc.Proto.Typed.Term.mkSymbolAs (Int) "i"
  let j ← Cvc.Proto.Typed.Term.mkSymbolAs (Int) "j"

  println! "select  : {← select a i}"
  println! "store   : {← store a i j}"
  println! "eqRange : {← eqRange a a i j}"

/-! ## Constructors -/

/-- info: mkConstArray : ((as const (Array Int Int)) 0) -/
#guard_msgs in #eval Env.runIO do
  let zero ← mkInt 0
  println! "mkConstArray : {← (mkConstArray zero : Env (Cvc.Proto.Typed.Term (Cvc.Proto.TotalMap Int Int)))}"
