module

import all Cvc.Untyped.Defs
meta import all Cvc.Untyped.Term

public import Cvc.Untyped.Defs



/-! # Types/helpers dealing with cvc's sorts and lifting them to lean types -/
namespace Cvc.Typed public section variable [Ω]

export Cvc (Srt ToTyp Env Error Ω)


def3% Term α ← Cvc.Untyped.Term (ofUntyped' / toUntyped')

/-- info: Cvc.Typed.Term [Ω] : Type → Type -/
#guard_msgs in #check Term

namespace Term

private def toUnsafe : Term α → cvc5.Term := id
private def ofUnsafe : cvc5.Term → Term α := id

private example (t : Term α) : ofUnsafe (t.toUnsafe) = t := rfl
private example (t : Cvc.Untyped.Term) : (ofUnsafe (α := α) t).toUnsafe = t := rfl

end Term

/-- An array of `Srt`s. -/
abbrev Terms (α : Type) := Array (Term α)

namespace Terms

private def toUnsafe : Terms α → Array cvc5.Term := id
private def ofUnsafe : Array cvc5.Term → Terms α := id

private example (t : Terms α) : ofUnsafe (t.toUnsafe) = t := rfl
private example (t : Array Cvc.Untyped.Term) : (ofUnsafe (α := α) t).toUnsafe = t := rfl

end Terms



class TermToValue (α : Type) where
  termToValue : Term α → Env α

-- private instance [inst : TermToValue α] : Cvc.TermToValue α where
--   termToValue term := inst.termToValue term

-- namespace TermToValue
-- instance : TermToValue α (Term α) := ⟨pure⟩
-- end TermToValue

class ValueToTerm (α : Type) where
  valueToTerm : α → Env (Term α)

-- private instance [inst : ValueToTerm α] : Cvc.ValueToTerm α where
--   valueToTerm value := inst.valueToTerm value

-- namespace ValueToTerm
-- instance : ValueToTerm α (Term α) := ⟨pure⟩
-- end ValueToTerm

class abbrev SrtLike (α : Type) (β : Type := α) := ToTyp α, TermToValue α, ValueToTerm α



-- def Term : Type → Type := 𝕂 Cvc.Term

-- namespace Term

-- def erase : Term α → Cvc.Term := id
-- private def ofErased' : Cvc.Term → Term α := id

-- protected def toString (term : Term α) : String :=
--   Cvc.Term.toString term

-- instance : ToString (Term α) := ⟨Term.toString⟩

-- end Term

-- abbrev Terms (α : Type) := Array (Term α)

-- namespace Terms

-- def erase (ts : Terms α) : Cvc.Terms := ts
-- private def ofErased' (ts : Cvc.Terms) : Terms α := ts

-- private def toUnsafe : Terms α → Array cvc5.Term := id
-- private def ofUnsafe : Array cvc5.Term → Terms α := id

-- end Terms



-- class TermToValue (α : Type) (β : Type := α) where
--   extractValue : Term α → Env β

-- namespace TermToValue open Cvc renaming Term → T

-- def liftExtractValue [inst : Cvc.TermToValue α] (t : Term α) : Env α := inst.extractValue t

-- def lowerExtractValue [inst : TermToValue α β] (t : Cvc.Term) : Env β := inst.extractValue t

-- instance [Cvc.TermToValue α] : TermToValue α := ⟨liftExtractValue⟩

-- abbrev lower [inst : TermToValue α β] : Cvc.TermToValue β := ⟨inst.lowerExtractValue⟩

-- end TermToValue



-- -- class TermToValue (α : Type) (β : Type := α) where
-- --   extractValue : Term α → Env β


-- -- /-! ## Lean types encoding cvc sorts and their values -/



-- -- inductive Typ
-- -- | bool | int | real | string | regex | roundingMode
-- -- | bitVec (size : UInt32)
-- -- | float (exp sig : UInt32)
-- -- | finiteField (size : Nat)
-- -- | arrayTo (idx elm : Typ)
-- -- | bag (elm : Typ) | set (elm : Typ) | seq (elm : Typ)
-- -- | abstract (a : Srt.Abstract)
-- -- | function (dom : Typ) (cod : Typ)

-- -- namespace Typ

-- -- def isArith : Typ → Bool
-- -- | int | real => true
-- -- | bool | string | regex | roundingMode
-- -- | bitVec _ | float _ _ | finiteField _ | arrayTo _ _
-- -- | bag _ | set _ | seq _ | abstract _ | function _ _ => false

-- -- end Typ

-- -- class ToTyp (α : Type) where
-- --   typ : Typ

-- -- namespace ToTyp

-- -- instance : ToTyp Bool := ⟨.bool⟩
-- -- instance : TermToValue Bool where extractValue t := t.erase.getBoolValue
-- -- instance : ToTyp Int := ⟨.int⟩
-- -- instance : TermToValue Int where extractValue t := t.erase.getIntValue
-- -- instance : ToTyp Rat := ⟨.real⟩
-- -- instance : TermToValue Rat where extractValue t := t.erase.getRatValue
-- -- instance : ToTyp String := ⟨.string⟩
-- -- instance : TermToValue String where extractValue t := t.erase.getStringValue

-- -- instance : ToTyp Cvc.Float.RoundingMode := ⟨.roundingMode⟩

-- -- instance [A : ToTyp α] : ToTyp (Array α) := ⟨.seq A.typ⟩

-- -- end ToTyp



-- -- class IsArith (α : Type) extends ToTyp α

-- -- instance : IsArith Int := {}
-- -- instance : IsArith Rat := {}



-- -- /-! ### Regular expressions -/

-- -- structure Regex
-- -- deriving DecidableEq, Hashable, Ord

-- -- namespace Regex

-- -- instance : ToTyp Regex := ⟨.regex⟩

-- -- end Regex



-- -- /-! ### Bit vectors -/

-- -- /-- Bit vector base. -/
-- -- inductive BitVec.Base
-- -- | bin | dec | hex
-- -- deriving DecidableEq, Hashable, Ord

-- -- /-- Bit vectors. -/
-- -- structure BitVec (size : UInt32) where
-- --   base : BitVec.Base
-- --   repr : String
-- -- deriving DecidableEq, Hashable, Ord

-- -- namespace BitVec

-- -- namespace Base

-- -- def toUInt32 : Base → UInt32
-- -- | bin => 2
-- -- | dec => 10
-- -- | hex => 16

-- -- protected def toString : Base → String
-- --   | bin => "0b"
-- --   | dec => ""
-- --   | hex => "0x"

-- -- instance : ToString Base := ⟨Base.toString⟩

-- -- end Base

-- -- protected def toString (bv : BitVec size) : String :=
-- --   s!"{bv.base}{bv.repr}"

-- -- instance : ToString (BitVec size) := ⟨BitVec.toString⟩

-- -- instance : ToTyp (BitVec size) := ⟨.bitVec size⟩

-- -- def ofValueTerm (t : Term (BitVec size)) (base : Base := .dec) : Env (BitVec size) := do
-- --   let s ← t.getBitVectorValue base.toUInt32
-- --   return mk base s

-- -- instance : TermToValue (BitVec size) := ⟨ofValueTerm⟩

-- -- end BitVec



-- -- /-! ### Floats -/

-- -- /-- Floats with exponent `exp` and significand `sig`. -/
-- -- structure Float (exp sig : UInt32) where
-- --   toBitVec : BitVec (1 + exp + sig)
-- -- deriving DecidableEq, Hashable

-- -- namespace Float

-- -- protected def compare (f1 f2 : Float exp sig) : Ordering :=
-- --   compare f1.toBitVec f2.toBitVec

-- -- instance : Ord (Float exp sig) := ⟨Float.compare⟩

-- -- protected def toString (f : Float exp sig) : String :=
-- --   s!"Float[{exp}, {sig}, {f.toBitVec}]"

-- -- instance : ToString (Float exp sig) := ⟨Float.toString⟩

-- -- instance : ToTyp (Float exp sig) := ⟨.float exp sig⟩

-- -- def ofValueTerm (t : Term (Float exp sig)) : Env (Float exp sig) := do
-- --   let (exp', sig', bvTerm) ← t.getFloatingPointValue
-- --   let bv ← BitVec.ofValueTerm bvTerm
-- --   if exp ≠ exp' ∨ sig ≠ sig' then throwInternal s!"\
-- --     expected floating point with exponent/significand sizes {exp}/{sig}, got {exp'}/{sig'}"
-- --   return ⟨bv⟩

-- -- instance : TermToValue (Float exp sig) := ⟨ofValueTerm⟩

-- -- end Float



-- -- /-! ### Finite fields -/

-- -- /-- Finite fields of size `size`. -/
-- -- structure FiniteField (size : Nat) where
-- --   repr : Int
-- -- deriving DecidableEq, Hashable, Ord

-- -- namespace FiniteField

-- -- structure Erased where
-- --   size : Nat
-- --   get : FiniteField size

-- -- protected def toString (ff : FiniteField size) : String :=
-- --   toString ff.repr

-- -- instance : ToString (FiniteField size) := ⟨FiniteField.toString⟩

-- -- instance : ToTyp (FiniteField size) := ⟨.finiteField size⟩

-- -- def ofValueTerm (t : Term (FiniteField size)) : Env (FiniteField size) := do
-- --   let val ← t.getFiniteFieldValue
-- --   if h : val.size = size then return h ▸ val.get
-- --   else throwUser s!"expected finite field value of size {size}, got size {val.size}: {t}"

-- -- instance : TermToValue (FiniteField size) := ⟨ofValueTerm⟩

-- -- end FiniteField



-- -- /-! ### Total maps (cvc arrays) -/



-- -- structure TotalMap (α β : Type) [Ord α] where
-- --   defaultVal : β
-- --   map : Std.TreeMap α β := Std.TreeMap.empty

-- -- namespace TotalMap variable [Ord α]

-- -- def mkConst (defaultVal : β) : TotalMap α β where defaultVal

-- -- protected def default [Inhabited β] : TotalMap α β := mkConst default
-- -- instance [B : Nonempty β] : Nonempty (TotalMap α β) := B.elim (⟨· , Std.TreeMap.empty⟩)
-- -- instance [Inhabited β] : Inhabited (TotalMap α β) := ⟨TotalMap.default⟩

-- -- /-! #### Basic operations -/
-- -- section variable [Ord α] (map : TotalMap α β) (key : α)

-- -- def insert (val : β) : TotalMap α β :=
-- --   {map with map := map.map.insert key val}

-- -- def get? : Option β := map.map.get? key

-- -- def get : β := map.get? key |>.getD map.defaultVal

-- -- end

-- -- /-! #### String representation -/

-- -- section variable [ToString α] [ToString β] (map : TotalMap α β)

-- -- def foldlStrings (f : γ → Bool → String → γ) (init : γ) : γ := Id.run do
-- --   let mut acc := init
-- --   for (key, val) in map.map do
-- --     acc := f acc false s!"{key} ↦ {val}"
-- --   f acc true s!"_ ↦ {map.defaultVal}"

-- -- def lines : Array String := map.foldlStrings (init := #[]) fun acc _ s => acc.push s

-- -- protected def toString : String := Id.run do
-- --   map.foldlStrings (init := "{ ") fun acc isLast line =>
-- --     s!"{acc}{line}{if isLast then " }" else ", "}"

-- -- instance : ToString (TotalMap α β) := ⟨TotalMap.toString⟩

-- -- end

-- -- instance [A : ToTyp α] [B : ToTyp β] : ToTyp (TotalMap α β) := ⟨A.typ.arrayTo B.typ⟩

-- -- def ofConstArrayTerm? [B : TermToValue β]
-- --   (t : Term (TotalMap α β)) (map : Std.TreeMap α β := .empty)
-- -- : Env (Option (TotalMap α β)) := do
-- --   if let some defaultVal := t.getConstArrayBase? then
-- --     let defaultVal ← B.extractValue defaultVal
-- --     return mk defaultVal map
-- --   else return none

-- -- def ofConstArrayTerm [B : TermToValue β]
-- --   (t : Term (TotalMap α β))
-- -- : Env (TotalMap α β) := do
-- --   mkConst <$> B.extractValue (← t.getConstArrayBase)

-- -- partial def ofValueTerm [A : TermToValue α] [B : TermToValue β]
-- --   (t : Term (TotalMap α β))
-- -- : Env (TotalMap α β) := do
-- --   peelStores Std.TreeMap.empty t
-- --   -- if let some map ← ofConstArrayTerm? t then return map
-- --   -- else throwTodo "non-constant array values"
-- -- where peelStores (map : Std.TreeMap α β) (t : Cvc.Term) : Env (TotalMap α β) := do
-- --   let k := t.getKind?
-- --   if let some cvc5.Kind.STORE := k then
-- --     let kids := t.getChildren
-- --     if h : kids.size = 3 then
-- --       let (array, idx, elm) := (kids[0], kids[1], kids[2])
-- --       let idx ← A.extractValue idx
-- --       let elm ← B.extractValue elm
-- --       let map := if ¬ map.contains idx then map.insert idx elm else map
-- --       peelStores map array
-- --     else throwInternal s!"{cvc5.Kind.STORE}-term should have three kids, got {kids}"
-- --   else if let some map ← ofConstArrayTerm? t map then
-- --     return map
-- --   else throwUser "expected a constant array-term"

-- -- instance [TermToValue α] [TermToValue β] : TermToValue (TotalMap α β) := ⟨ofValueTerm⟩

-- -- end TotalMap



-- -- /-! ### Sets -/

-- -- abbrev Set (α : Type) [Ord α] := Std.TreeSet α

-- -- namespace Set variable [Ord α]

-- -- open Std renaming TreeSet → S

-- -- def empty : Set α := S.empty
-- -- def insert : Set α → α → Set α := S.insert
-- -- def erase : Set α → α → Set α := S.erase

-- -- instance [A : ToTyp α] : ToTyp (Set α) := ⟨.set A.typ⟩

-- -- def ofValueTerm [A : TermToValue α] (t : Term (Set α)) : Env (Set α) := do
-- --   let elms ← t.getSetValue
-- --   elms.foldlM (init := Set.empty) fun set elm => do
-- --     set.insert <$> A.extractValue elm

-- -- instance [TermToValue α] : TermToValue (Set α) := ⟨ofValueTerm⟩

-- -- end Set



-- -- /-! ### Bags -/

-- -- abbrev Bag (α : Type) [Ord α] := Std.TreeMap α Nat

-- -- namespace Bag variable [Ord α] (bag : Bag α)

-- -- def alter (key : α) (f : Nat → Nat) : Bag α :=
-- --   Std.TreeMap.alter bag key fun val? => match val?.getD 0 |> f with | 0 => none | n => n

-- -- def increment (key : α) := bag.alter key .succ

-- -- def decrement (key : α) := bag.alter key .pred

-- -- def add (key : α) (n : Nat) := bag.alter key (· + n)

-- -- def sub (key : α) (n : Nat) := bag.alter key (· - n)

-- -- def get? (key : α) : Option Nat := Std.TreeMap.get? bag key

-- -- def get (key : α) : Nat := bag.get? key |>.getD 0

-- -- def contains (key : α) : Bool := 0 < bag.get key

-- -- protected abbrev mem (key : α) : Prop := bag.contains key

-- -- instance : Membership α (Bag α) := ⟨Bag.mem⟩

-- -- omit [Ω] in
-- -- theorem mem_def {key : α} : (key ∈ bag) = bag.contains key := rfl

-- -- instance (key : α) : Decidable (key ∈ bag) :=
-- --   bag.mem_def ▸ if h : bag.contains key then isTrue h else isFalse h

-- -- protected def toString [ToString α] (bag : Bag α) : String :=
-- --   bag.foldl (init := "") fun
-- --     | acc, _key, 0 => acc
-- --     | acc, key, n => s!"{if acc.isEmpty then acc else acc ++ ", "}{key} ↦ {n}"

-- -- instance [ToString α] : ToString (Bag α) := ⟨Bag.toString⟩

-- -- instance [A : ToTyp α] : ToTyp (Bag α) := ⟨.bag A.typ⟩

-- -- def ofValueTerm [TermToValue α] (_t : Term (Bag α)) : Env (Bag α) :=
-- --   throwTodo "bag value extraction from a term"

-- -- instance [TermToValue α] : TermToValue (Bag α) := ⟨ofValueTerm⟩

-- -- end Bag



-- -- /-! ### Abstracted sorts -/

-- -- structure Abstracted (a : Srt.Abstract)
-- -- deriving DecidableEq, Hashable, Ord

-- -- namespace Abstracted

-- -- instance : ToTyp (Abstracted a) := ⟨.abstract a⟩

-- -- end Abstracted



-- -- /-! ### Functions -/

-- -- structure Fun (α β : Type)

-- -- namespace Fun

-- -- end Fun



-- -- /-! ### Conversion from `Typ` to `Srt` -/


-- -- namespace Typ

-- -- /-- Helper for `toSrt`, carries bits of termination-proof around. -/
-- -- def foldFunctionCod [Monad m] (srt' : Typ)
-- --   (acc : α) (f : α → (s : Typ) → (sizeOf s < sizeOf srt') → m α)
-- -- : m (α × (cod : Typ) ×' sizeOf cod ≤ sizeOf srt') :=
-- --   match h : srt' with
-- --   | function dom cod => do
-- --     let acc ← f acc dom (by grind only [= function.sizeOf_spec])
-- --     let (acc, ⟨cod, h⟩) ← cod.foldFunctionCod acc fun acc s h =>
-- --       f acc s (by grind only [= function.sizeOf_spec])
-- --     return (acc, ⟨cod, by grind only [= function.sizeOf_spec]⟩)
-- --   | cod => return (acc, ⟨cod, by grind only⟩)

-- -- /-- Conversion to `Srt`. -/
-- -- public def toSrt [Ω] : Typ → Env Srt
-- -- | bool => Srt.bool | int => Srt.int | real => Srt.real
-- -- | regex => Srt.regex | string => Srt.string
-- -- | roundingMode => Srt.roundingMode
-- -- | bitVec size => Srt.bitVec size
-- -- | float exp sig => Srt.float exp sig
-- -- | finiteField size => Srt.finiteField size
-- -- | arrayTo idx elm => do elm.toSrt >>= (← idx.toSrt).arrayTo
-- -- | bag elm => elm.toSrt >>= Srt.bag
-- -- | set elm => elm.toSrt >>= Srt.set
-- -- | seq elm => elm.toSrt >>= Srt.seq
-- -- | abstract a => Srt.abstract a
-- -- | function dom cod => do
-- --   let dom ← dom.toSrt
-- --   /- non-empty array, required for `Srt.function` -/
-- --   let acc : {a : Array Srt // 0 < a.size} := ⟨#[dom], by grind⟩
-- --   let (dom, ⟨cod, h⟩) ← cod.foldFunctionCod acc fun acc s h =>
-- --     /- push and update proof that array (`acc`) is non-empty -/
-- --     return ⟨acc.val.push (← s.toSrt), by grind⟩
-- --   let cod ← cod.toSrt
-- --   Srt.function dom cod

-- -- instance [A : ToTyp α] [B : ToTyp β] : ToTyp (Fun α β) := ⟨.function A.typ B.typ⟩

-- -- end Typ
