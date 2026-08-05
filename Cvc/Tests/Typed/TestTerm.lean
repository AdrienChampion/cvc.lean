module

import Cvc.Typed.Term

import Cvc.Tests.TestBasic



namespace Cvc.Typed.Tests


def displayAs [Ω] [ToTyp α] [TermToValue α] [ToString α]
  (name : String) (t : Term α)
: Env (Term α) := do
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
#test basic.term.creation do
  println! "start"
  let _i1 ← Term.mkInt 5 >>= displayAs "i1"
  let _i2 ← Term.mkInt 7 >>= displayAs "i2"
  let _b1 ← Term.mkBool true >>= displayAs "b1"
  let _b2 ← Term.mkValue false >>= displayAs "b2"
  let _s1 ← Term.mkString "neko" >>= displayAs "s1"
  let _s2 ← Term.mkValue "inu" >>= displayAs "s2"

/--
info: start
term := (seq.++ (seq.unit "a") (seq.unit "string") (seq.unit "sequence"))
---
error: [internal] invalid argument '(seq.++ (seq.unit "a") (seq.unit "string") (seq.unit "sequence"))' for '*d_node', expected Term to be a sequence value when calling getSequenceValue()
-/
#test basic.seq.getValueError do
  println! "start"
  let seq := #[ "a", "string", "sequence" ]
  let term ← Term.mkValue seq
  println! "term := {term}"
  println! "→ {← term.getValue}"
