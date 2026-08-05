module

public meta import Lean.Elab.Command

public import Cvc.Basic.Env



namespace Cvc.Tests public section variable [Ω]

def assert (b : Bool) (desc : Unit → String := fun _ => s!"in {decl_name%}") : Env Unit := do
  if ¬ b then println! "assertion failed: {desc ()}"

def assertFalse (b : Bool) (desc : Unit → String := fun _ => s!"in {decl_name%}") : Env Unit := do
  assert (¬ b) desc

def assertEq [BEq α] [ToString α] (exp val : α)
  (desc : Unit → String := fun _ => s!"expected {exp}, got {val}")
: Env Unit := do
  assert (exp == val) desc

def assertNe [BEq α] [ToString α] (exp val : α)
  (desc : Unit → String := fun _ => s!"expected a value different from {exp}, got {val}")
: Env Unit := do
  assert (exp != val) desc

def assertString [ToString α] (exp : String) (value : α) : Env Unit := do
  toString value |> assertEq exp

declare_syntax_cat testPrefCat

syntax (name := testPrefStx) atomic(docComment ? "#test ") : testPrefCat

macro pref:testPrefStx id:ident body:term : command => do
  let runId := id.getId |>.append `run |> Lean.mkIdent
  let envRunIOId := ``Env.runIO |> Lean.mkIdent
  let doc? ← match pref with
    | `(testPrefStx| $doc:docComment #test) => pure (some doc)
    | _ => pure none
  `(
    def $runId : IO Unit := $envRunIOId $body
    $[ $doc?:docComment ]?
    #guard_msgs in #eval $runId
  )


declare_syntax_cat bodTestPrefCat

syntax (name := bodTestPrefStx) atomic(docComment ? "#test! ") : bodTestPrefCat

macro pref:bodTestPrefStx id:ident body:term : command => do
  let runId := id.getId |>.append `run |> Lean.mkIdent
  let envRunIOId := ``Env.runIO |> Lean.mkIdent
  let doc? ← match pref with
    | `(bodTestPrefStx| $doc:docComment #test!) => pure (some doc)
    | _ => pure none
  `(
    $[ $doc?:docComment ]?
    #guard_msgs in def $runId : IO Unit := $envRunIOId $body
  )
