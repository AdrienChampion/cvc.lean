module

import Cvc.Untyped.Srt

import Cvc.Tests.TestBasic

namespace Cvc.Tests



/- Making sure the API works as we expect -/

set_option linter.unusedVariables false in
/--
info: - Bool
- Int
- (-> Int Bool)
- (Array Bool (-> Int Bool))
- (-> Bool (Array Bool (-> Int Bool)))
- (Bag (-> Bool (Array Bool (-> Int Bool))))
- (Bag (-> Int Bool))
- (Set (-> Bool (Array Bool (-> Int Bool))))
- (Set (-> Int Bool))
- (Seq (-> Bool (Array Bool (-> Int Bool))))
- (Seq (-> Int Bool))
Error:
- [internal] invalid argument '(-> Int Bool)' for 'codomain', expected non-function sort as codomain sort
-/
#test basic.sort.creation do
  let printMk (code : Env Srt) : Env Srt := do
    let srt ← code
    println! "- {srt}"
    return srt
  let printError {α : Type} (desc : String) (code : Env α) : Env Unit := do
    try
      let _ ← code
      throwUser s!"{desc}: expected an error, got success"
    catch e => println! "Error:\n- {e}"
  let bool ← printMk Srt.bool
  let int ← printMk Srt.int
  let fn ← printMk do Srt.function #[int] bool
  let arrayFn ← printMk do bool.arrayTo fn
  let fn2 ← printMk do Srt.function #[bool] arrayFn
  let bag ← printMk do fn2.bag
  let bag' ← printMk do fn.bag
  let set ← printMk do fn2.set
  let set' ← printMk do fn.set
  let seq ← printMk do fn2.seq
  let seq' ← printMk do fn.seq
  printError "function with function codomain" do fn.function #[int]



#test array.sort.creation do
  let int ← Srt.int
  let real ← Srt.real
  let intToReal ← int.arrayTo real
  intToReal |> assertString "(Array Int Real)"
  real.array >>= assertEq intToReal
  int.arrayFrom real >>= assertString "(Array Real Int)"

#test function.sort.creation do
  let bool ← Srt.bool
  let int ← Srt.int
  let real ← Srt.real
  Srt.function #[int] real >>= assertString "(-> Int Real)"
  Srt.function #[bool, int] real >>= assertString "(-> Bool Int Real)"

/--
error: could not synthesize default value for parameter 'domNonempty' using tactics
---
error: failed to prove the domain is nonempty
inst✝ : Ω
real : Srt
⊢ 0 < #[].size
-/
#test! function.creation.error do
  let real ← Srt.real
  Srt.function #[] real >>= assertString "(-> Int Real)"
