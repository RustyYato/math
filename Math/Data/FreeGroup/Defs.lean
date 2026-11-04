module

public import Math.Data.FreeMonoid.Defs
import Math.Data.FreeMonoid.Basic
public import Math.Algebra.Group.Defs
public import Math.Algebra.GroupQuot.Defs

namespace Math

open FreeMonoid in
public inductive FreeGroup.Rel (α: Type*) : FreeMonoid (Bool × α) -> FreeMonoid (Bool × α) -> Prop where
| intro (b: Bool) (a: α) : Rel α (ι (!b, a) * ι (b, a)) 1

public structure FreeGroup (α: Type*) where
  ofQuot :: toQuot : GroupQuot (FreeGroup.Rel α)

public structure FreeAddGroup (α: Type*) where
  ofInner :: toInner : AddOfMul (FreeGroup α)

namespace FreeGroup

public instance : MonoidOps (FreeGroup α) where
  one := ⟨1⟩
  mul a b := ⟨a.toQuot * b.toQuot⟩
  toPowN := ⟨fun a n => ⟨a.toQuot ^ n⟩⟩

@[expose] public def eqv : GroupQuot (FreeGroup.Rel α) ≃* FreeGroup α where
  toFun := ofQuot
  invFun := toQuot
  leftInv _ := rfl
  rightInv _ := rfl
  map_one := rfl
  map_mul _ _ := rfl

public instance : IsMonoid (FreeGroup α) :=
  OfEquiv.instIsMonoid eqv.toEquiv

def flip' : FreeMonoid (Bool × α) →* FreeMonoid (Bool × α) :=
  FreeMonoid.lift (fun x => FreeMonoid.ι (!x.1, x.2))

theorem flip'_involution : flip' (flip' x) = x := by
  induction x with
  | one => simp [map_one]
  | mul => simp [map_mul]; congr
  | ι =>
    unfold flip';
    simp [FreeMonoid.lift_ι]

def flip : FreeMonoid (Bool × α) ≃* FreeMonoid (Bool × α) where
  toFun := flip'
  invFun := flip'
  map_one := map_one _
  map_mul _ _ := map_mul _ _ _
  leftInv x := by rw [flip'_involution]
  rightInv x := by rw [flip'_involution]

@[simp] theorem flip_ι (b: Bool) (a: α) : flip (FreeMonoid.ι (b, a)) = FreeMonoid.ι (!b, a) := by
  show flip' _ = _; unfold flip'
  simp [FreeMonoid.lift_ι]

attribute [local irreducible] MulOpp

def preInv : FreeMonoid (Bool × α) →* (GroupQuot (Rel α))ᵐᵒᵖ where
  toFun a := MulOpp.mk <| GroupQuot.mk _ (FreeMonoid.reverse (flip a)).get
  map_one := by simp [map_one]; rfl
  map_mul a b := by simp [map_mul]; rfl

@[simp] theorem apply_preInv (a: FreeMonoid (Bool × α)) : preInv a = MulOpp.mk (GroupQuot.mk _ (FreeMonoid.reverse (flip a)).get) := rfl

def quotInv : GroupQuot (Rel α) →* (GroupQuot (Rel α))ᵐᵒᵖ :=
  GroupQuot.lift {
    val := preInv
    property := by
      intro a b h
      simp; congr 1; cases h
      simp [map_one, map_mul]
      rw [←map_mul]; apply GroupQuot.sound
      apply Rel.intro
  }

public def inv : FreeGroup α →* (FreeGroup α)ᵐᵒᵖ where
  toFun a := .mk (eqv (quotInv (eqv.symm a)).get)
  map_one := by
    simp [map_one]
    rfl
  map_mul a b := by
    simp [map_mul]
    rfl

theorem apply_inv (a: FreeGroup α) : inv a = .mk (eqv (quotInv (eqv.symm a)).get) := rfl

public instance : Inv (FreeGroup α) where
  inv a := (inv a).get
public instance : Div (FreeGroup α) where
  div a b := a * b⁻¹
public instance : Pow (FreeGroup α) ℤ where
  pow a := fun
    | .ofNat n => (a ^ n)
    | .negSucc n => (a ^ (n + 1))⁻¹

theorem inv_one : (1: FreeGroup α)⁻¹ = 1 := by
  show (inv 1).get = 1; rw [map_one]; rfl
theorem inv_mul (a b: FreeGroup α) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  show (inv _).get = _; rw [map_mul]; rfl

public instance : IsGroup (FreeGroup α) where
  div_eq_mul_inv _ _ := rfl
  powz_ofNat _ _ := rfl
  powz_negSucc _ _ := rfl
  inv_mul_cancel x := by
    obtain ⟨x⟩ := x
    show (eqv x)⁻¹ * eqv x = 1
    induction x with | _ x =>
    induction x with
    | one => rw [map_one, map_one, inv_one, mul_one]
    | mul a b iha ihb =>
      simp [map_mul, inv_mul]
      rw [mul_assoc, ←mul_assoc (eqv (GroupQuot.mk _ a))⁻¹,
        iha, one_mul, ihb]
    | ι a =>
      show (inv _).get * _ = _
      rw [apply_inv]; simp; rw [←map_mul]
      show _ = eqv 1; congr
      unfold quotInv
      simp [GroupQuot.lift_mk]
      apply GroupQuot.sound
      rw [flip_ι, FreeMonoid.reverse_ι]
      simp; apply Rel.intro

public def ι : α -> FreeGroup α :=
  fun a => eqv (.mk _ (FreeMonoid.ι (false, a)))

public theorem induction
  {motive: FreeGroup α -> Prop}
  (one: motive 1)
  (ι: ∀a, motive (ι a))
  (inv: ∀a, motive (FreeGroup.ι a)⁻¹)
  (mul: ∀a b, motive a -> motive b -> motive (a * b))
  (g: FreeGroup α) : motive g := by
  obtain ⟨g⟩ := g; induction g with | _ g =>
  induction g with
  | one => apply one
  | mul => apply mul ⟨.mk _ _⟩ ⟨.mk _ _⟩ <;> assumption
  | ι a =>
    obtain ⟨b, a⟩ := a
    cases b
    apply ι
    have : motive (FreeGroup.inv.toFun (FreeGroup.ι a)).get := inv a
    unfold FreeGroup.inv FreeGroup.ι at this
    simp [quotInv, GroupQuot.lift_mk] at this
    apply this

@[induction_eliminator]
public theorem group_induction
  {motive: FreeGroup α -> Prop}
  (one: motive 1)
  (ι: ∀a, motive (ι a))
  (inv: ∀a, motive a -> motive a⁻¹)
  (mul: ∀a b, motive a -> motive b -> motive (a * b))
  (g: FreeGroup α) : motive g := by
  induction g using induction with
  | one => apply one
  | mul => apply mul <;> assumption
  | ι a => apply ι
  | inv a => apply inv; apply ι

variable [GroupOps G] [IsGroup G]

def preLift (f: α -> G) : FreeGroup α →* G :=
  (GroupHom.comp · eqv.symm.toGroupHom) <|
    GroupQuot.lift {
      val := FreeMonoid.lift (fun
        | ⟨false, a⟩ => f a
        | ⟨true, a⟩ => (f a)⁻¹)
      property := by
        intro a b h; cases h
        simp [map_mul, map_one, FreeMonoid.lift_ι]
        rename_i b a; cases b <;> simp
        rw [inv_mul_cancel]
        rw [mul_inv_cancel]
    }

public def lift : (α -> G) ≃ (FreeGroup α →* G) where
  toFun := preLift
  invFun f := f ∘ ι
  leftInv f := by
    ext g; dsimp [preLift]
    induction g using induction with
    | one => simp [map_one]
    | mul => simp [map_mul]; congr
    | ι =>
      conv in eqv.symm _ => { simp [FreeGroup.ι] }
      simp [GroupQuot.lift_mk, FreeMonoid.lift_ι]
    | inv a =>
      simp [map_inv]
      conv in eqv.symm _ => { simp [FreeGroup.ι] }
      show GroupQuot.lift _ (eqv.symm (inv.toFun _).get) = _
      simp [inv, quotInv, GroupQuot.lift_mk, FreeMonoid.lift_ι]
  rightInv f := by
    ext a; simp [preLift]
    conv in eqv.symm _ => { simp [FreeGroup.ι] }
    simp [GroupQuot.lift_mk, FreeMonoid.lift_ι]

public theorem lift_ι (f: α -> G) : lift f (ι a) = f a := by
  show (preLift f) _ = _
  simp [preLift]
  conv in eqv.symm _ => { simp [FreeGroup.ι] }
  simp [GroupQuot.lift_mk, FreeMonoid.lift_ι]

end FreeGroup

namespace FreeAddGroup

public instance : AddGroupOps (FreeAddGroup α) where
  zero := ⟨0⟩
  add a b := ⟨a.toInner + b.toInner⟩
  toNSMul := ⟨fun n a => ⟨n • a.toInner⟩⟩
  neg a := ⟨-a.toInner⟩
  sub a b := ⟨a.toInner - b.toInner⟩
  toZSMul := ⟨fun n a => ⟨n • a.toInner⟩⟩

def eqv : AddOfMul (FreeGroup α) ≃+ FreeAddGroup α where
  toFun := ofInner
  invFun := toInner
  leftInv _ := rfl
  rightInv _ := rfl
  map_zero := rfl
  map_add _ _ := rfl

public instance : IsAddGroup (FreeAddGroup α) :=
  OfEquiv.instIsAddGroup eqv.toEquiv

attribute [local irreducible] MulOfAdd AddOfMul

public def ι : α -> FreeAddGroup α := eqv ∘ AddOfMul.mk ∘ FreeGroup.ι

variable [AddGroupOps G] [IsAddGroup G]

def preLift : (FreeAddGroup α →+ G) ≃ (FreeGroup α →* MulOfAdd G) where
  toFun f := (GroupHom.of (MulOfAdd.mk (f.comp eqv.toAddGroupHom))).comp (GroupEquiv.mul_of_add_inv_add_of_mul _).symm.toGroupHom
  invFun f :=
    have := AddGroupHom.of (AddOfMul.mk f)
    have := (AddGroupEquiv.add_of_mul_inv_mul_of_add _).toAddGroupHom.comp this
    this.comp eqv.symm.toAddGroupHom
  leftInv f := by ext g; simp
  rightInv f := by ext g; simp

def castMulOfAdd : (α -> G) ≃ (α -> MulOfAdd G) where
  toFun f a := MulOfAdd.mk (f a)
  invFun f a := (f a).get
  leftInv _ := rfl
  rightInv _ := rfl

public def lift : (α -> G) ≃ (FreeAddGroup α →+ G) :=
  preLift.symm.comp  <|
  castMulOfAdd.trans <|
  (FreeGroup.lift (G := MulOfAdd G))

public theorem lift_ι (f: α -> G) (a: α) : lift f (ι a) = f a := by
  simp [lift]; show preLift.invFun _ _ = _
  simp [preLift]
  simp [ι, FreeGroup.lift_ι]
  rfl

end FreeAddGroup
