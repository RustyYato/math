import LeanMath.Algebra.Group.Quot
import LeanMath.Algebra.Monoid.Free
import LeanMath.Data.Indicator.Defs

attribute [local irreducible] MulOpp

private inductive Rel (α: Type*) : FreeMonoid (Bool × α) -> FreeMonoid (Bool × α) -> Prop where
| intro (b: Bool) (x: α) : Rel α (.ι (b, x) * .ι (!b, x)) 1

structure FreeGroup (α: Type*) where
  ofQuot :: toQuot : GroupQuot (Rel α)

private def FreeMonoid.inv : FreeMonoid (Bool × α) →* MulOpp (FreeMonoid (Bool × α)) :=
  FreeMonoid.reverse.comp <| FreeMonoid.lift (FreeMonoid.ι ∘ fun (b, x) => (!b, x))

@[simp] private def FreeMonoid.inv_ι (x: Bool × α) : FreeMonoid.inv (ι x) = MulOpp.mk (ι (!x.fst, x.snd)) := by simp [inv]

namespace FreeGroup

instance : One (FreeGroup α) where
  one := { toQuot := 1 }
instance : Mul (FreeGroup α) where
  mul a b := { toQuot := a.toQuot * b.toQuot }
instance : Pow (FreeGroup α) ℕ where
  pow a n := { toQuot := a.toQuot ^ n }

private def toFreeGroup (a: α) : FreeGroup α where
  toQuot := GroupQuot.mk (Rel α) (FreeMonoid.ι (false, a))

instance : IsMonoid (FreeGroup α) where
  mul_assoc a b c := by
    show FreeGroup.ofQuot (a.toQuot * b.toQuot * c.toQuot) = FreeGroup.ofQuot (a.toQuot * (b.toQuot * c.toQuot))
    rw [mul_assoc]
  one_mul a := by
    show FreeGroup.ofQuot (1 * a.toQuot) = FreeGroup.ofQuot (a.toQuot)
    rw [one_mul]
  mul_one a := by
    show FreeGroup.ofQuot (a.toQuot * 1) = FreeGroup.ofQuot (a.toQuot)
    rw [mul_one]
  npow_zero a := by
    show FreeGroup.ofQuot (a.toQuot ^ 0) = FreeGroup.ofQuot 1
    rw [npow_zero]
  npow_succ a n := by
    show FreeGroup.ofQuot (a.toQuot ^ (n + 1)) = FreeGroup.ofQuot (a.toQuot ^ n * a.toQuot)
    rw [npow_succ]

private def preInvHom : GroupQuot (Rel α) →* MulOpp (GroupQuot (Rel α)) :=
  GroupQuot.lift (Rel α) {
    val := (MulOpp.liftGroupHom (GroupQuot.mk (Rel α))).comp FreeMonoid.inv
    property a b h := by
      induction h with | intro b x =>
      simp
      congr 1
      apply GroupQuot.sound
      simp [map_mul, map_one]
      cases b <;> apply Rel.intro
  }

@[simp] private def apply_preInvHom (x: FreeMonoid (Bool × α)) :
  preInvHom (GroupQuot.mk (Rel α) x) = MulOpp.mk (GroupQuot.mk (Rel α) (FreeMonoid.inv x).get) := by simp [preInvHom]

def invHom : FreeGroup α →* MulOpp (FreeGroup α) where
  toFun x := MulOpp.mk ⟨(preInvHom x.toQuot).get⟩
  map_one := by
    show MulOpp.mk (FreeGroup.ofQuot ((preInvHom 1).get)) = _
    rw [map_one (preInvHom (α := α))]
    rfl
  map_mul a b := by
    show MulOpp.mk (FreeGroup.ofQuot ((preInvHom (a.toQuot * b.toQuot)).get)) = _
    rw [map_mul (preInvHom (α := α))]
    rfl

instance : Inv (FreeGroup α) where
  inv g := (invHom g).get

instance : Div (FreeGroup α) where
  div a b := a * b⁻¹

instance : Pow (FreeGroup α) ℤ where
  pow a z := match z with
    | .ofNat x => a ^ x
    | .negSucc x => (a ^ (x + 1))⁻¹

instance : IsLawfulDiv (FreeGroup α) where
  div_eq_mul_inv _ _ := rfl
instance : IsLawfulPowZ (FreeGroup α) where
  zpow_ofNat _ _ := rfl
  zpow_negSucc _ _ := rfl
instance : IsGroup (FreeGroup α) where
  mul_inv_cancel a := by
    cases a with | ofQuot a =>
    show ofQuot (a * (preInvHom a).get) = _
    induction a with | mk a =>
    congr; simp
    induction a with
    | one =>
      simp [map_one, one_mul]
      rfl
    | ι a =>
      simp
      rw [←map_mul]
      apply GroupQuot.sound
      apply Rel.intro
    | mul a b iha ihb =>
      rw [map_mul, map_mul, MulOpp.mul_get, map_mul]
      rw [←mul_assoc, mul_assoc (GroupQuot.mk _ _), ihb, mul_one, iha]

private def inv_toFreeGroup (x: α) : (toFreeGroup x)⁻¹ = ofQuot (GroupQuot.mk _ (FreeMonoid.ι (true, x))) := by
  show MulOpp.get (MulOpp.mk _) = _
  simp [toFreeGroup]

@[induction_eliminator]
def induction {motive: FreeGroup α -> Prop}
  (one: motive 1)
  (ι: ∀x, motive (toFreeGroup x))
  (inv: ∀x, motive x -> motive x⁻¹)
  (mul: ∀a b, motive a -> motive b -> motive (a * b))
  (g: FreeGroup α): motive g := by
  cases g with | ofQuot g =>
  induction g with | mk g =>
  induction g with
  | one => apply one
  | mul a b =>
    apply mul ⟨GroupQuot.mk _ a⟩ ⟨GroupQuot.mk _ b⟩
    assumption
    assumption
  | ι x =>
    obtain ⟨b, x⟩ := x
    cases b
    apply ι
    rw [←inv_toFreeGroup]
    apply inv (toFreeGroup x)
    apply ι

variable [GroupOps G] [IsGroup G]

@[simp] private def toQuot_1 : toQuot (α := α) 1 = 1 := rfl
@[simp] private def toQuot_mul (a b: FreeGroup α) : toQuot (a * b) = a.toQuot * b.toQuot := rfl

private def preLift (f: α -> G) : FreeGroup α →* G where
  toFun g := GroupQuot.lift (Rel α) {
    val := FreeMonoid.lift (fun
      | (false, x) => f x
      | (true, x) => (f x)⁻¹)
    property := by
      intro a b h
      induction h with | intro b x =>
      rw [map_mul, map_one]
      cases b <;> simp
      rw [mul_inv_cancel]
      rw [inv_mul_cancel]
  } g.toQuot
  map_one := by simp [map_one]
  map_mul a b := by simp [map_mul]

private def preLift_toFreeGroup (f: α -> G) (x: α) : preLift f (toFreeGroup x) = f x := by
  simp [preLift, toFreeGroup]

def lift : (α -> G) ≃ (FreeGroup α →* G) where
  toFun := preLift
  invFun f := f ∘ toFreeGroup
  leftInv f := by
    simp; ext x
    induction x with
    | one => simp [map_one]
    | inv a ih => simp [map_inv, ih]
    | mul a b iha ihb => simp [map_mul, iha, ihb]
    | ι a => simp [preLift_toFreeGroup]
  rightInv f := by
    ext x; simp
    rw [preLift_toFreeGroup]

@[simp] private def lift_toFreeGroup (f: α -> G) (x: α) : lift f (toFreeGroup x) = f x := preLift_toFreeGroup f x

attribute [irreducible] invHom lift toFreeGroup

instance [Subsingleton α] : IsComm (FreeGroup α) where
  mul_comm a b := by
    induction a with
    | one => rw [mul_one, one_mul]
    | ι a =>
      induction b with
      | one => rw [mul_one, one_mul]
      | ι b => rw [Subsingleton.allEq a b]
      | inv b ih =>
        have : IsCommAt (toFreeGroup a) b := ⟨ih⟩
        rw [mul_comm]
      | mul b₀ b₁ ih₀ ih₁ => rw [←mul_assoc, ih₀, mul_assoc, ih₁, mul_assoc]
    | inv a ih =>
      have : IsCommAt a b := ⟨ih⟩
      rw [mul_comm]
    | mul a₀ a₁ ih₀ ih₁ => rw [mul_assoc, ih₁, ←mul_assoc, ih₀, mul_assoc]

private def toFreeGroup_inj : Function.Injective (toFreeGroup (α := α)) := by
  intro a b h
  classical
  let f := lift (G := Indicator) (fun x => if x = b then 1 else .flip)
  have : f (toFreeGroup b) = 1 := by rw [lift_toFreeGroup, if_pos rfl]
  have : f (toFreeGroup a) = 1 := by rw [h, this]
  simpa [f] using this

def ι : α ↪ FreeGroup α where
  toFun := toFreeGroup
  inj := toFreeGroup_inj

def lift_ι (f: α -> G) (x: α) : lift f (ι x) = f x := lift_toFreeGroup f x

end FreeGroup
