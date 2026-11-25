module

public import Math.Algebra.Group.Theory.Defs
public import Math.Data.Cardinal.Defs
public import Math.Data.FreeGroup.Defs
public import Math.Algebra.GroupQuot.Group

namespace Math.Group

public def card : Group -> Cardinal :=
  lift (fun G => Cardinal.type G) <| by
    intro a b _ _ _ _ h; apply Cardinal.sound
    exact h.toEquiv

public def IsAbelian : Group -> Prop :=
  lift (fun G => IsComm G) <| by
    intro A B _ _ _ _ f
    ext; apply Iff.intro
    intro h; refine ⟨fun a b => ?_⟩
    apply f.symm.inj
    rw [map_mul, map_mul, mul_comm]
    intro h; refine ⟨fun a b => ?_⟩
    apply f.inj
    rw [map_mul, map_mul, mul_comm]

public inductive Cyclic.Rel (G: Type*) (n: ℕ) [GroupOps G] [IsGroup G] : G -> G -> Prop where
| intro a : Rel G n (a ^ n) 1

@[expose] public def Cyclic (n: ℕ) : Group :=
  Group.type (GroupQuot (Cyclic.Rel (FreeGroup Unit) n))
