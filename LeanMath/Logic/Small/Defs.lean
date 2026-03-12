import LeanMath.Data.Equiv.Basic
import LeanMath.Tactic.PPWithUniv

@[pp_with_univ]
class inductive Small.{v, u} (α: Type u) : Prop where
| intro (β: Type v) (eqv: α ≃ β)

@[pp_with_univ]
class UnivLE.{u, v} where
  small: ∀(α: Type u), Small.{v} α
attribute [instance] UnivLE.small

namespace Small

def lift.{w, u, v} [h: Small.{u, v} α] : Small.{max u w, v} α :=
  have ⟨β, eqv⟩ := h
  .intro (ULift.{w} β) (eqv.trans (Equiv.ulift _))
instance (priority := 100) uinc [h: Small.{u, v} α] : Small.{u + 1, v} α := lift.{u + 1, u, v}
instance : Small.{v, v} α := .intro α (Equiv.id _)

def iff_equiv.{v, u} {α: Type u} : Small.{v, u} α ↔ ∃β: Type v, Nonempty (α ≃ β) where
  mp | ⟨β, eqv⟩ => ⟨β, ⟨eqv⟩⟩
  mpr | ⟨β, ⟨eqv⟩⟩ => ⟨β, eqv⟩

def exists_equiv.{v, u} (α: Type u) [Small.{v, u} α] : ∃β: Type v, Nonempty (α ≃ β) :=
  iff_equiv.mp inferInstance

instance [UnivLE.{u, v}] : Small.{v, u} α := UnivLE.small _

def trans_univ_le.{v, u, w} (α: Type v) [UnivLE.{u, w}] [h: Small.{u} α] : Small.{w} α :=
  have ⟨β, eqv⟩ := h
  have ⟨γ, eqv'⟩ : Small.{w, u} β := inferInstance
  .intro γ (eqv.trans eqv')

def map [hs: Small.{u} α] (h: α ≃ β) : Small.{u} β :=
  have ⟨γ, hs⟩ := hs
  .intro γ (h.symm.trans hs)

instance small_ulift (α : Type u) [Small.{v} α] : Small.{v} (ULift α) :=
  map (Equiv.ulift _)

instance small_plift (α : Type u) [Small.{v} α] : Small.{v} (PLift α) :=
  map (Equiv.plift _)

instance small_type : Small.{max (u + 1) v} (Type u) := lift

end Small

namespace UnivLE

instance refl.{u} : UnivLE.{u, u} where
  small _ := inferInstance
def max.{u, v} : UnivLE.{u, max u v} where
  small _ := Small.lift

def trans.{u, v, w} [UnivLE.{u, v}] [UnivLE.{v, w}] : UnivLE.{u, w} where
  small α := Small.trans_univ_le α

instance : UnivLE.{0, u} := max
instance univLE_of_max [UnivLE.{max u v, v}] : UnivLE.{u, v} :=
  have := max.{u, v}; trans.{u, max u v, v}
def univLE_succ [UnivLE.{u, v}] : UnivLE.{u, v + 1} :=
  trans.{u, v, v + 1}

example : UnivLE.{v, max v u} := inferInstance
example : UnivLE.{v, max u v} := inferInstance
example : UnivLE.{u, max v u} := inferInstance
example : UnivLE.{u, max u v} := inferInstance

example : UnivLE.{u, u + 32} := inferInstance
example : UnivLE.{2, 5} := inferInstance

example : Small.{max u v, u} α := inferInstance

end UnivLE

def Shrink.{v, u} (α: Type u) [Small.{v, u} α] : Type v :=
  Classical.choose (Small.exists_equiv.{v} α)

noncomputable def Equiv.shrink {α: Type u} [Small.{v, u} α] : α ≃ Shrink.{v, u} α :=
  Classical.choice (Classical.choose_spec (Small.exists_equiv α))
