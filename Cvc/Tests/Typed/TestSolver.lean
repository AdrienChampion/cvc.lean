module

import Cvc.Typed.Solver

import Cvc.Tests.TestBasic



namespace Cvc.Typed.Tests

/-- info:
s1 : (Seq Bool) := s1
→ (seq.++ (seq.unit true) (seq.unit false) (seq.unit true))
  Solver.getValueTerm
→ #[true, false, true]
  Term.getValue
→ #[true, false, true]
  Solver.getValue
-/
#test array.getValue do
  let solver ← Typed.Solver.new
  solver.setOption "produce-models" "true"

  let s1 ← Term.mkSymbolAs (Array Bool) "s1"
  println! "s1 : {← s1.getSort} := {s1}"

  let tru ← Term.mkValue true
  let fls ← Term.mkValue false
  let i0 ← Term.mkInt 0
  let i1 ← Term.mkInt 1
  let i2 ← Term.mkInt 2

  let atEq (idx : Term Int) (val : Term Bool) : Env (Term Bool) := do
    let tAt ← s1.seqAt idx
    val.unitSeq >>= tAt.equal

  atEq i0 tru >>= solver.assert
  atEq i1 fls >>= solver.assert
  atEq i2 tru >>= solver.assert

  let val ← solver.checkSat (ifSat := do
    let value ← solver.getValueTerm s1
    return value)
  println! "→ {val}\n  Solver.getValueTerm"
  let v ← val.getValue
  println! "→ {v}\n  Term.getValue"

  let val ← solver.checkSat (ifSat := do
    let value ← solver.getValue s1
    return value)
  println! "→ {val}\n  Solver.getValue"
