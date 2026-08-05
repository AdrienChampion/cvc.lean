module

import Cvc.Typed.Term
import Cvc.Ext

import Cvc.Tests.TestBasic



namespace Cvc.Typed.Tests

open Cvc.Tests

/-- info:
false |>.getValue = false
true |>.getValue = true
5 |>.getValue = 5
7 |>.getValue = 7
"some string" |>.getValue = some string
-/
#test ext.value.creation do
  let fls ← smt! false
  let _ : Term Bool := fls
  println! "{fls} |>.getValue = {← fls.getValue}"
  let tru ← smt! true
  println! "{tru} |>.getValue = {← tru.getValue}"
  let five ← smt! 5
  let _ : Term Int := five
  println! "{five} |>.getValue = {← five.getValue}"
  let seven ← smt! 7
  println! "{seven} |>.getValue = {← seven.getValue}"
  let string ← smt! "some string"
  let _ : Term String := string
  println! "{string} |>.getValue = {← string.getValue}"

#test ext.polyOps do
  let b1 ← Term.mkSymbolAs Bool "b1"
  let b2 ← Term.mkSymbolAs Bool "b2"
  let b3 ← Term.mkSymbolAs Bool "b3"
  let i1 ← Term.mkSymbolAs Int "i1"
  let i2 ← Term.mkSymbolAs Int "i2"
  let fls ← Term.mkValue false
  let tru ← Term.mkValue true

  let eq ← smt! b1 = b2
  let _ : Term Bool := eq
  eq |> assertString "(= b1 b2)"
  smt! i1 = i2
    >>= assertString "(= i1 i2)"
  smt! b1 = b2 = b3 = fls = tru
    >>= assertString "(= b1 (= b2 (= b3 (= false true))))"
  smt! =[b1, b2, b3, fls, tru]
    >>= assertString "(and (= b1 b2) (= b2 b3) (= b3 false) (= false true))"

  let iteBool ← smt! if b3 then fls else tru
  let _ : Term Bool := iteBool
  iteBool |> assertString "(ite b3 false true)"

  let iteInt ← smt! if b3 then i2 else i1
  let _ : Term Int := iteInt
  iteInt |> assertString "(ite b3 i2 i1)"

  let iteNested ← smt! if iteBool then iteInt else (- iteInt)
  let _ : Term Int := iteNested
  iteNested |> assertString
    "(let ((_let_1 (ite b3 i2 i1))) (ite (ite b3 false true) _let_1 (- _let_1)))"
