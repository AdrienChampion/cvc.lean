/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto.Untyped.Term.Array
import Cvc.Proto.Untyped.Term.Bool
import Cvc.Proto.Untyped.Term.Arith
import Cvc.Proto.Types.Array

public meta import Cvc.Proto.Untyped.Term.Array
public meta import Cvc.Proto.Untyped.Term.Bool
public meta import Cvc.Proto.Untyped.Term.Arith
public meta import Cvc.Proto.Types.Array



/-! # Generated Array constructors, sort-erased -/
namespace Cvc.Proto.Tests.Untyped.Term.Array

open Cvc
open Cvc.Proto.Untyped.Term

/-- info:
select  : (select a i)
store   : (store a i j)
eqRange : (eqrange a a i j)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Proto.Untyped.Term.mkSymbolAs (Cvc.Proto.TotalMap Int Int) "a"
  let i ← Cvc.Proto.Untyped.Term.mkSymbolAs (Int) "i"
  let j ← Cvc.Proto.Untyped.Term.mkSymbolAs (Int) "j"

  println! "select  : {← select a i}"
  println! "store   : {← store a i j}"
  println! "eqRange : {← eqRange a a i j}"

/-! ## Constructors -/

/-- info: mkConstArray : ((as const (Array Int Int)) 0) -/
#guard_msgs in #eval Env.runIO do
  let zero ← mkInt 0
  let srt ← Srt.of (Cvc.Proto.TotalMap Int Int)
  println! "mkConstArray : {← mkConstArray srt zero}"
