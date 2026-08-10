/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto.Typed.Term.Regex
import Cvc.Proto.Typed.Term.Bool

public meta import Cvc.Proto.Typed.Term.Regex
public meta import Cvc.Proto.Typed.Term.Bool



/-! # Generated Regex constructors, typed -/
namespace Cvc.Proto.Tests.Typed.Term.Regex

open Cvc
open Cvc.Proto.Typed.Term

/-- info:
concat    : (re.++ re re)
union     : (re.union re re)
inter     : (re.inter re re)
diff      : (re.diff re re)
star      : (re.* re)
plus      : (re.+ re)
opt       : (re.opt re)
range     : (re.range s t)
complement: (re.comp re)
loop      : ((_ re.loop 2 5) re)
repeat    : ((_ re.^ 3) re)
-/
#guard_msgs in #eval Env.runIO do
  let re ← Cvc.Proto.Typed.Term.mkSymbolAs (Cvc.Proto.Regex) "re"
  let s ← Cvc.Proto.Typed.Term.mkSymbolAs (String) "s"
  let t ← Cvc.Proto.Typed.Term.mkSymbolAs (String) "t"

  println! "concat    : {← reConcat re re}"
  println! "union     : {← reUnion re re}"
  println! "inter     : {← reInter re re}"
  println! "diff      : {← reDiff re re}"
  println! "star      : {← reStar re}"
  println! "plus      : {← rePlus re}"
  println! "opt       : {← reOpt re}"
  println! "range     : {← reRange s t}"
  println! "complement: {← reComplement re}"
  println! "loop      : {← reLoop 2 5 re}"
  println! "repeat    : {← reRepeat 3 re}"

/-! ## Constants

These take no sort: their result is `RegLan` in every context.
-/

/-- info:
all     : re.all
allChar : re.allchar
none    : re.none
-/
#guard_msgs in #eval Env.runIO do
  println! "all     : {← reAll}"
  println! "allChar : {← reAllChar}"
  println! "none    : {← reNone}"
