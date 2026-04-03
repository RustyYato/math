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

@[implicit_reducible]
def of_embed (f: α ↪ β) [h: Small.{u} β] : Small.{u} α := by
  obtain ⟨γ, h⟩ := h
  replace f := f.trans h.toEmbedding
  have ⟨g, hg⟩ := Classical.axiomOfUniqueChoice (P := fun (g: { g: γ // ∃a, f a = g }) (a) => f a = g.val) (fun g: { g: γ // ∃a, f a = g } => by
    have ⟨x, hx⟩ := g.property
    exists x
    apply And.intro hx
    intro y hy
    apply inj f
    rw [hx, hy])
  exact .intro { g: γ // ∃a, f a = g } {
    toFun a := {
      val := f a
      property := ⟨_, rfl⟩
    }
    invFun := g
    leftInv x := by dsimp; congr; rw [(hg _).left]
    rightInv x := by dsimp; apply inj f; rw [(hg _).left]
  }

@[implicit_reducible]
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

@[implicit_reducible]
def trans_univ_le.{v, u, w} (α: Type v) [UnivLE.{u, w}] [h: Small.{u} α] : Small.{w} α :=
  have ⟨β, eqv⟩ := h
  have ⟨γ, eqv'⟩ : Small.{w, u} β := inferInstance
  .intro γ (eqv.trans eqv')

@[implicit_reducible]
def map [hs: Small.{u} α] (h: α ≃ β) : Small.{u} β :=
  have ⟨γ, hs⟩ := hs
  .intro γ (h.symm.trans hs)

instance small_ulift (α : Type u) [Small.{v} α] : Small.{v} (ULift α) :=
  map (Equiv.ulift _)

instance small_plift (α : Type u) [Small.{v} α] : Small.{v} (PLift α) :=
  map (Equiv.plift _)

instance small_type : Small.{max (u + 1) v} (Type u) := lift

@[implicit_reducible]
def of_surj (f: β -> α) (hf: Function.Surjective f) [h: Small.{u} β] : Small.{u} α := by
  obtain ⟨γ, hy⟩ := h
  apply of_embed.{u} (β := γ -> Prop) {
    toFun := ?_
    inj := ?_
  }
  exact fun a g => f (hy.symm g) = a
  intro a b h
  replace h := fun y => congrFun h y
  dsimp at h
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨b, rfl⟩ := hf b
  have := h (hy a)
  rw [Equiv.coe_symm] at this
  rw [←this]

end Small

namespace UnivLE

instance refl.{u} : UnivLE.{u, u} where
  small _ := inferInstance
@[implicit_reducible]
def max.{u, v} : UnivLE.{u, max u v} where
  small _ := Small.lift

@[implicit_reducible]
def trans.{u, v, w} [UnivLE.{u, v}] [UnivLE.{v, w}] : UnivLE.{u, w} where
  small α := Small.trans_univ_le α

instance : UnivLE.{0, u} := max
instance univLE_of_max [UnivLE.{max u v, v}] : UnivLE.{u, v} :=
  have := max.{u, v}; trans.{u, max u v, v}
@[implicit_reducible]
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

-- make this opaque so that it cannot be inspected
private noncomputable opaque ShrinkDef.{v, u} (α: Type u) [Small.{v, u} α] : Σβ: Type v, α ≃ β := {
  fst := Classical.choose (Small.exists_equiv α)
  snd := Classical.choice (Classical.choose_spec (Small.exists_equiv α))
}

def Shrink.{v, u} (α: Type u) [Small.{v, u} α] : Type v := (ShrinkDef α).1
noncomputable def Equiv.shrink {α: Type u} [Small.{v, u} α] : α ≃ Shrink.{v, u} α := (ShrinkDef α).2

/-- this is always safe because `Shrink` is opaque and defined via `Classical.choice`,
  so we can specify the representation of `Shrink` -/
unsafe def Equiv.runtime_shrink {α: Type u} [Small.{v, u} α] : α ≃ Shrink.{v, u} α where
  toFun a := ULift.down.{max u v} (cast lcProof (ULift.up.{max u v, u} a))
  invFun a := ULift.down.{max u v} (cast lcProof (ULift.up.{max u v, v} a))
  leftInv := lcProof
  rightInv := lcProof

@[csimp] unsafe def Equiv.runtime_shrink_eq_shrink : @Equiv.shrink = @Equiv.runtime_shrink := lcProof
