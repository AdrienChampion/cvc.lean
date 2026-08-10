/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto.Untyped.Term.Set
import Cvc.Proto.Untyped.Term.Bool
import Cvc.Proto.Types.Set

public meta import Cvc.Proto.Untyped.Term.Set
public meta import Cvc.Proto.Untyped.Term.Bool
public meta import Cvc.Proto.Types.Set



/-! # Generated Set constructors, sort-erased -/
namespace Cvc.Proto.Tests.Untyped.Term.Set

open Cvc
open Cvc.Proto.Untyped.Term

/-- info:
member    : (set.member i s)
subset    : (set.subset s t)
isEmpty   : (set.is_empty s)
isSingle  : (set.is_singleton s)
singleton : (set.singleton i)
insert    : (set.insert i s)
union     : (set.union s t)
inter     : (set.inter s t)
minus     : (set.minus s t)
complement: (set.complement s)
card      : (set.card s)
choose    : (set.choose s)
unionN    : (set.union (set.union s t) s)
-/
#guard_msgs in #eval Env.runIO do
  let i ← Cvc.Proto.Untyped.Term.mkSymbolAs (Int) "i"
  let s ← Cvc.Proto.Untyped.Term.mkSymbolAs (Cvc.Proto.Set Int) "s"
  let t ← Cvc.Proto.Untyped.Term.mkSymbolAs (Cvc.Proto.Set Int) "t"

  println! "member    : {← setMember i s}"
  println! "subset    : {← setSubset s t}"
  println! "isEmpty   : {← setIsEmpty s}"
  println! "isSingle  : {← setIsSingleton s}"
  println! "singleton : {← setSingleton i}"
  println! "insert    : {← setInsert i s}"
  println! "union     : {← setUnion s t}"
  println! "inter     : {← setInter s t}"
  println! "minus     : {← setMinus s t}"
  println! "complement: {← setComplement s}"
  println! "card      : {← setCard s}"
  println! "choose    : {← setChoose s}"
  println! "unionN    : {← setUnionN #[s, t, s]}"

/-! ## Higher-order operators -/

/-- info:
map   : (set.map m s)
filter: (set.filter p s)
fold  : (set.fold acc z s)
all   : (set.all p s)
some  : (set.some p s)
-/
#guard_msgs in #eval Env.runIO do
  let p ← Cvc.Proto.Untyped.Term.mkSymbolAs ((Int → Bool)) "p"
  let m ← Cvc.Proto.Untyped.Term.mkSymbolAs ((Int → Int)) "m"
  let acc ← Cvc.Proto.Untyped.Term.mkSymbolAs ((Int → Int → Int)) "acc"
  let z ← Cvc.Proto.Untyped.Term.mkSymbolAs (Int) "z"
  let s ← Cvc.Proto.Untyped.Term.mkSymbolAs (Cvc.Proto.Set Int) "s"

  println! "map   : {← setMap m s}"
  println! "filter: {← setFilter p s}"
  println! "fold  : {← setFold acc z s}"
  println! "all   : {← setAll p s}"
  println! "some  : {← setSome p s}"

/-! ## Constants

The sort-erased constructor takes the sort it builds; the typed one recovers it from its index.
-/

/-- info:
empty    : (as set.empty (Set Int))
universe : (as set.universe (Set Int))
-/
#guard_msgs in #eval Env.runIO do
  println! "empty    : {← Srt.of (Cvc.Proto.Set Int) >>= setEmpty}"
  println! "universe : {← Srt.of (Cvc.Proto.Set Int) >>= setUniverse}"
