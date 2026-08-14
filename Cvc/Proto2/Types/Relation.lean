/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Proto2.Srt

public import Cvc.Proto2.Srt



/-! # Indices for tuples, relations and tables

A tuple's components are a **list**, and this is the index that says so: `Tup α β` describes the
components `α ++ [β]`. Splitting the last one off does two jobs at once.

It makes the list *non-empty*, since a tuple has at least one component. And — the part that earns
the encoding — it makes "the last component" a **parameter position**, so unification can find it.
`?α ++ [?β]` against a concrete list is higher-order and Lean will not solve it; `Tup ?α ?β` against
`Tup [Int, Bool] Real` is first-order and solves at once. That is what lets relational join say
"drop the left's last and the right's first" as nothing but a signature:

```lean
relJoin : Term (Rel α μ) → Term (Rel (μ :: α') β') → Env (Term (Rel (α ++ α') β'))
```

with the shared `μ` expressing, structurally, cvc5's requirement that the two be joinable.

**This is why `α × β` was not enough.** A right-nested product has no terminator, so the slot for
"rest of the tuple" and the slot for "last component" are the same one: `α × (β × γ)` cannot say
whether it means three components or two whose second is a pair. `Tup [α] (β × γ)` and
`Tup [α, β] γ` are different indices, and denote different sorts.

`Rel` and `Tab` are sets and bags of tuples. Neither is a sort of its own — cvc5 has no
`RELATION_SORT` or `TABLE_SORT` — so these are indices over the same underlying terms, and
`toSet`/`toBag` cross over for free.
-/
namespace Cvc.Proto2 public section



/-- The `Typ`s a list of Lean types denotes. -/
class ToTypList (α : List Type) where
  /-- The `Typ`s, in order. -/
  typs : List Typ

namespace ToTypList

instance : ToTypList [] := ⟨[]⟩

instance [A : ToTyp α] [As : ToTypList αs] : ToTypList (α :: αs) := ⟨A.typ :: As.typs⟩

/-- The `Typ`s of `α ++ [β]`, which is what every index here describes. -/
def typsOf (α : List Type) (β : Type) [As : ToTypList α] [B : ToTyp β] : List Typ :=
  As.typs ++ [B.typ]

end ToTypList



/-- A tuple of the components `α ++ [β]`.

Carries no data: it names a sort, and the terms it indexes are ordinary terms. Built with
`Term.mkTuple` from a `Components` spine.
-/
structure Tup (α : List Type) (β : Type) where
  private mk ::

/-- A relation over the components `α ++ [β]`: a **set** of `Tup α β`. -/
structure Rel (α : List Type) (β : Type) where
  private mk ::

/-- A table over the columns `α ++ [β]`: a **bag** of `Tup α β`, so a row may repeat. -/
structure Tab (α : List Type) (β : Type) where
  private mk ::

/-! ### Instances for nesting

These indices carry no data — they name a sort — so their comparisons are trivial. They exist only
so that a container of them can be *spelled*: `relGroup` answers a `Set (Rel α β)`, and `Set` wants
its element ordered. No `Std.TreeSet` of relations is ever built, since these indices have no value
conversion, so the triviality never shows.

They are written out rather than derived because `deriving` constrains the type parameters even
though nothing uses them, which would demand `Ord β` — and `Ord Rat` does not exist.
-/

instance : DecidableEq (Tup α β) := fun _ _ => isTrue rfl
instance : DecidableEq (Rel α β) := fun _ _ => isTrue rfl
instance : DecidableEq (Tab α β) := fun _ _ => isTrue rfl

instance : Ord (Tup α β) := ⟨fun _ _ => .eq⟩
instance : Ord (Rel α β) := ⟨fun _ _ => .eq⟩
instance : Ord (Tab α β) := ⟨fun _ _ => .eq⟩

instance : Hashable (Tup α β) := ⟨fun _ => 0⟩
instance : Hashable (Rel α β) := ⟨fun _ => 0⟩
instance : Hashable (Tab α β) := ⟨fun _ => 0⟩

instance [ToTypList α] [ToTyp β] : ToTyp (Tup α β) :=
  ⟨.prod (ToTypList.typsOf α β)⟩

instance [ToTypList α] [ToTyp β] : ToTyp (Rel α β) :=
  ⟨.set (.prod (ToTypList.typsOf α β))⟩

instance [ToTypList α] [ToTyp β] : ToTyp (Tab α β) :=
  ⟨.bag (.prod (ToTypList.typsOf α β))⟩
