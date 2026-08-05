/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

-- public import Cvc.Basic.Batteries
public import Cvc.Solver



namespace Cvc variable [Ω]

def Actlit := Term

namespace Actlit

section variable (a1 a2 : Actlit)

protected def beq : Bool := Term.beq a1 a2
protected def compare : Ordering := Term.compare a1 a2

instance : BEq Actlit := ⟨Actlit.beq⟩
instance : Ord Actlit := ⟨Actlit.compare⟩

end

structure Core where
private mk ::
  private nextIdx : Nat
  -- private live : RBSet Actlit

protected abbrev EnvT (m : Type → Type) : (α : Type) → Type :=
  StateRefT' IO.RealWorld Core (EnvT m)

protected abbrev Env : (α : Type) → Type := Actlit.EnvT BaseIO

namespace EnvT

instance [MonadLiftT BaseIO m] : MonadLift (Cvc.EnvT m) (Actlit.EnvT m) where
  monadLift code := fun _ => code

end EnvT

private def mkNameOfNat (idx : Nat) : String :=
  s!"__cvc__actlit__{idx}"

def mk : Actlit.Env Actlit := do
  let core ← getThe Core
  let name := mkNameOfNat core.nextIdx
  let actlit ← Term.mkConst name (← Srt.bool)
  -- if core.live.contains actlit then
  --   throwInternal s!"fresh actlit {actlit} already registered in the set of live actlits"
  set {core with nextIdx := core.nextIdx.succ,
    -- live := core.live.insert actlit
  }
  return actlit

section variable (a : Actlit)

protected def toString : String := Term.toString a
instance : ToString Actlit := ⟨Actlit.toString⟩

def activateIn (solver : Solver) (term : Term) : Cvc.Env Unit :=
  a.implies term >>= solver.assert

def deactivateIn (solver : Solver) : Cvc.Env Unit := do
  -- let core ← getThe Core
  -- set {core with live := core.live.erase a}
  solver.assert (← a.not)

end

end Actlit
