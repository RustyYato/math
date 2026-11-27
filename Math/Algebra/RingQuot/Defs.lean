module

public import Math.Algebra.Semiring.Congruence
public import Math.Algebra.Semiring.Defs.OfEquiv

namespace Math

public structure RingQuot (r: α -> α -> Prop) [SemiringOps α] where
  ofQuot :: toQuot : AlgQuot (RingCon.generate r)

namespace RingQuot

@[local ext]
theorem ext [SemiringOps α] {r: α -> α -> Prop} (a b: RingQuot r) (h: a.toQuot = b.toQuot) : a = b := by
  cases a; cases b; congr

variable [SemiringOps α] {r: α -> α -> Prop}

def ofQuot' (r: α -> α -> Prop) : AlgQuot (RingCon.generate r) ≃ RingQuot r where
  toFun := RingQuot.ofQuot
  invFun := RingQuot.toQuot
  leftInv _ := rfl
  rightInv _ := rfl

variable [IsSemiring α]

public instance : SemiringOps (RingQuot r) where
  zero := ⟨0⟩
  one := ⟨1⟩
  add a b := ⟨a.toQuot + b.toQuot⟩
  mul a b := ⟨a.toQuot * b.toQuot⟩
  natCast n := ⟨n⟩
  toNSMul := ⟨fun n a => ⟨n • a.toQuot⟩⟩
  toPowN := ⟨fun a n => ⟨a.toQuot ^ n⟩⟩

public instance : IsSemiring (RingQuot r) :=
  OfEquiv.instIsSemiring (ofQuot' r)

@[expose] public def mk (r: α -> α -> Prop) : α →+* RingQuot r where
  toFun := ofQuot ∘ AlgQuot.mk (RingCon.generate r)
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

public theorem sound {a b: α} : r a b -> mk r a = mk r b := by
  intro h; unfold mk
  show ⟨AlgQuot.mk _ _⟩ = ofQuot (AlgQuot.mk _ _)
  congr 1; apply AlgQuot.sound
  apply RingCon.to_generate
  assumption

public theorem exact {a b: α} : mk r a = mk r b -> RingCon.generate r a b := by
  intro h;
  exact AlgQuot.exact (ofQuot.inj h)

@[induction_eliminator]
public theorem ind {motive: RingQuot r -> Prop} (mk: ∀a, motive (mk r a)) (q: RingQuot r) : motive q := by
  obtain ⟨q⟩ := q
  induction q with | _ q =>
  apply mk

variable [SemiringOps R] [IsSemiring R]

def preLift [IsSemiring R] (f: α →+* R) (hf: ∀a b, r a b -> f a = f b) : RingQuot r →+* R where
  toFun q := q.toQuot.lift f <| by
    intro a b h
    apply RingCon.of_generate (RingCon.eq _) _ _ h
    assumption
  map_zero := map_zero f
  map_one := map_one f
  map_add a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    apply map_add (α := α) f a b
  map_mul a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    apply map_mul (α := α) f a b

theorem preLift_mk (f: α →+* R) (hf: ∀a b, r a b -> f a = f b) : preLift f hf (mk r x) = f x := rfl

public def lift : { f: α →+* R // ∀a b, r a b -> f a = f b } ≃ RingQuot r →+* R where
  toFun f := preLift f.val f.property
  invFun f := {
    val := f.comp (mk r)
    property := by
      intro a b h; dsimp; congr 1
      apply RingQuot.sound
      assumption
  }
  leftInv f := by ext a; induction a with | _ a => rfl
  rightInv f := by ext a; rfl

public theorem lift_mk (f: { f: α →+* R // ∀a b, r a b -> f a = f b }) : lift f (mk r x) = f.val x := by
  unfold lift
  rfl
