module

import Cvc.Untyped.Term
import Cvc.Ext

import Cvc.Tests.TestBasic



namespace Cvc.Untyped.Tests

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
  println! "{fls} |>.getValue = {← fls.getBoolValue}"
  let tru ← smt! true
  println! "{tru} |>.getValue = {← tru.getBoolValue}"
  let five ← smt! 5
  println! "{five} |>.getValue = {← five.getIntValue}"
  let seven ← smt! 7
  println! "{seven} |>.getValue = {← seven.getIntValue}"
  let string ← smt! "some string"
  println! "{string} |>.getValue = {← string.getStringValue}"

#test ext.boolOps do
  let b1 ← Term.mkSymbolAs Bool "b1"
  let b2 ← Term.mkSymbolAs Bool "b2"
  let b3 ← Term.mkSymbolAs Bool "b3"
  let fls ← Term.mkValue false
  let tru ← Term.mkValue true

  smt! b1 ∧ b3
    >>= assertString "(and b1 b3)"
  smt! b1 ∧ b2 ∧ b3 ∧ fls ∧ tru
    >>= assertString "(and b1 (and b2 (and b3 (and false true))))"
  smt! ∧[b1, b2, b3, fls, tru]
    >>= assertString "(and b1 b2 b3 false true)"

  smt! b1 ∨ b3
    >>= assertString "(or b1 b3)"
  smt! b1 ∨ b2 ∨ b3 ∨ fls ∨ tru
    >>= assertString "(or b1 (or b2 (or b3 (or false true))))"
  smt! ∨[b1, b2, b3, fls, tru]
    >>= assertString "(or b1 b2 b3 false true)"

  smt! b1 ⊻ b3
    >>= assertString "(xor b1 b3)"
  smt! b1 ⊻ b2 ⊻ b3 ⊻ fls ⊻ tru
    >>= assertString "(xor (xor (xor (xor b1 b2) b3) false) true)"
  smt! ⊻[b1, b2, b3, fls, tru]
    >>= assertString "(xor (xor (xor (xor b1 b2) b3) false) true)"

  smt! b1 → b3
    >>= assertString "(=> b1 b3)"
  smt! b1 → b2 → b3 → fls → tru
    >>= assertString "(=> b1 (=> b2 (=> b3 (=> false true))))"
  smt! →[b1, b2, b3, fls, tru]
    >>= assertString "(=> b1 (=> b2 (=> b3 (=> false true))))"

#test ext.polyOps do
  let b1 ← Term.mkSymbolAs Bool "b1"
  let b2 ← Term.mkSymbolAs Bool "b2"
  let b3 ← Term.mkSymbolAs Bool "b3"
  let i1 ← Term.mkSymbolAs Int "i1"
  let i2 ← Term.mkSymbolAs Int "i2"
  let fls ← Term.mkValue false
  let tru ← Term.mkValue true

  smt! b1 = b2
    >>= assertString "(= b1 b2)"
  smt! i1 = i2
    >>= assertString "(= i1 i2)"
  smt! b1 = b2 = b3 = fls = tru
    >>= assertString "(= b1 (= b2 (= b3 (= false true))))"
  smt! =[b1, b2, b3, fls, tru]
    >>= assertString "(and (= b1 b2) (= b2 b3) (= b3 false) (= false true))"

  smt! if b3 then fls else tru >>= assertString "(ite b3 false true)"
  smt! if b3 then i2 else i1 >>= assertString "(ite b3 i2 i1)"

#test ext.arithOps do
  let i1 ← Term.mkSymbolAs Int "i1"
  let i2 ← Term.mkSymbolAs Int "i2"
  let five ← smt! 5
  let seven ← smt! 7

  smt! 5 + 7 >>= assertString "(+ 5 7)"
  smt! five + seven >>= assertString "(+ 5 7)"
  smt! i1 + i2 >>= assertString "(+ i1 i2)"
  smt! 5 - 7 >>= assertString "(- 5 7)"
  smt! five - seven >>= assertString "(- 5 7)"
  smt! i1 - i2 >>= assertString "(- i1 i2)"
  smt! - 5 >>= assertString "(- 5)"
  smt! - five >>= assertString "(- 5)"
  smt! - i1 >>= assertString "(- i1)"

  smt! five < i1 >>= assertString "(< 5 i1)"
  smt! <[five, i1, i2, seven] >>= assertString "(and (< 5 i1) (< i1 i2) (< i2 7))"
  smt! five < (- i2) >>= assertString "(< 5 (- i2))"
