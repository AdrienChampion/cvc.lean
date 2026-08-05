module

import Cvc.Untyped.Term

import Cvc.Tests.TestBasic



namespace Cvc.Untyped.Tests


def displayAs [Ω] (α : Type) [ToTyp α] [TermToValue α] [ToString α]
  (name : String) (t : Term)
: Env Term := do
  println! "{name} := {t}, getValue → {← t.getValueAs α} : {Typ.of α}"
  return t

/--
info: start
i1 := 5, getValue → 5 : Int
i2 := 7, getValue → 7 : Int
b1 := true, getValue → true : Bool
b2 := false, getValue → false : Bool
s1 := "neko", getValue → neko : String
s2 := "inu", getValue → inu : String
-/
#test basic.value.creation do
  println! "start"
  let _i1 ← Term.mkInt 5 >>= displayAs Int "i1"
  let _i2 ← Term.mkValue 7 >>= displayAs Int "i2"
  let _b1 ← Term.mkBool true >>= displayAs Bool "b1"
  let _b2 ← Term.mkValue false >>= displayAs Bool "b2"
  let _s1 ← Term.mkString "neko" >>= displayAs String "s1"
  let _s2 ← Term.mkValue "inu" >>= displayAs String "s2"
