import LeanMath.Algebra.Group.Defs
import LeanMath.Data.Equiv.Defs

structure GroupQuot [MonoidOps G] [IsMonoid G] (r: G -> G -> Prop) where
  ofQuot :: toQuot : AlgQuot (MulCon.generate r)

namespace GroupQuot

variable (r: G -> G -> Prop)

instance [MonoidOps G] [IsMonoid G] : One (GroupQuot r) where
  one := ⟨1⟩
instance [MonoidOps G] [IsMonoid G] : Mul (GroupQuot r) where
  mul a b := ⟨a.toQuot * b.toQuot⟩
instance [MonoidOps G] [IsMonoid G] : Pow (GroupQuot r) ℕ where
  pow a n := ⟨a.toQuot ^ n⟩

instance [GroupOps G] [IsGroup G] : Inv (GroupQuot r) where
  inv a := ⟨a.toQuot⁻¹⟩
instance [GroupOps G] [IsGroup G] : Div (GroupQuot r) where
  div a b := ⟨a.toQuot / b.toQuot⟩
instance [GroupOps G] [IsGroup G] : Pow (GroupQuot r) ℤ where
  pow a n := ⟨a.toQuot ^ n⟩

def mk [MonoidOps G] [IsMonoid G] : G →* GroupQuot r where
  toFun g := {
    toQuot := AlgQuot.mk (MulCon.generate r) g
  }
  map_one := rfl
  map_mul _ _ := rfl

@[induction_eliminator]
def ind [MonoidOps G] [IsMonoid G] { motive: GroupQuot r -> Prop } (mk: ∀x, motive (.mk r x)) (g: GroupQuot r) : motive g := by
  cases g with | ofQuot g =>
  induction g with | mk g =>
  apply mk g

instance [MonoidOps G] [IsMonoid G] [IsComm G] : IsComm (GroupQuot r) where
  mul_comm a b := by
    induction a with | mk a =>
    induction b with | mk b =>
    rw [←map_mul, ←map_mul, mul_comm]

instance [MonoidOps G] [IsMonoid G] : IsMonoid (GroupQuot r) where
  mul_assoc a b c := by
    induction a with | mk a =>
    induction b with | mk b =>
    induction c with | mk c =>
    show mk r (a * b * c) = mk r (a * (b * c))
    rw [mul_assoc]
  one_mul a := by
    induction a with | mk a =>
    show mk r (1 * a) = mk r a
    rw [one_mul]
  mul_one a := by
    induction a with | mk a =>
    show mk r (a * 1) = mk r a
    rw [mul_one]
  npow_zero a := by
    induction a with | mk a =>
    show mk r (a ^ 0) = mk r 1
    rw [npow_zero]
  npow_succ a n := by
    induction a with | mk a =>
    show mk r (a ^ (n + 1)) = mk r (a ^ n * a)
    rw [npow_succ]

instance [GroupOps G] [IsGroup G] : IsGroup (GroupQuot r) where
  div_eq_mul_inv a b := by
    induction a with | mk a =>
    induction b with | mk b =>
    show mk r (a / b) = mk r (a * b⁻¹)
    rw [div_eq_mul_inv]
  zpow_ofNat a n := by
    induction a with | mk a =>
    show mk r (a ^ (n: ℤ)) = mk r (a ^ n)
    rw [zpow_ofNat]
  zpow_negSucc a n := by
    induction a with | mk a =>
    show mk r (a ^ (Int.negSucc n)) = mk r (a ^ (n + 1))⁻¹
    rw [zpow_negSucc]
  mul_inv_cancel a := by
    induction a with | mk a =>
    show mk r (a * a⁻¹) = mk r 1
    rw [mul_inv_cancel]

variable [MonoidOps G] [IsMonoid G] [MonoidOps M] [IsMonoid M] [AddMonoidOps N] [IsAddMonoid N]

def sound {r: G -> G -> Prop} {a b: G} : r a b -> mk r a = mk r b := by
  intro h
  unfold mk
  show ofQuot _ = ofQuot _
  congr 1
  apply Quotient.sound
  apply MulCon.generate_of
  assumption

def lift : { f: G →* M // ∀x y: G, r x y -> f x = f y } ≃ GroupQuot r →* M where
  toFun f := {
    toFun g := g.toQuot.liftOn f.val <| by
      intro a b h
      induction h with
      | refl => rfl
      | symm => symm; assumption
      | trans _ _ _ _ _ ih₀ ih₁ => rw [ih₀, ih₁]
      | mul a b _ _ _ _ ih₀ ih₁ => rw [map_mul, map_mul, ih₀, ih₁]
      | of a b =>
        apply f.property
        assumption
    map_one := map_one f.val
    map_mul a b := by
      induction a; induction b
      apply map_mul f.val
  }
  invFun f := {
    val := {
      toFun g := f (mk _ g)
      map_one := by rw [map_one, map_one]
      map_mul a b := by rw [map_mul, map_mul]
    }
    property a b h := by
      show f (mk r a) = f (mk r b)
      rw [GroupQuot.sound h]
  }
  leftInv f := by
    ext x; induction x with | mk x =>
    rfl
  rightInv f := by
    ext x
    rfl

def liftLog : { f: G →*+ N // ∀x y: G, r x y -> f x = f y } ≃ GroupQuot r →*+ N where
  toFun f := {
    toFun g := g.toQuot.liftOn f.val <| by
      intro a b h
      induction h with
      | refl => rfl
      | symm => symm; assumption
      | trans _ _ _ _ _ ih₀ ih₁ => rw [ih₀, ih₁]
      | mul a b _ _ _ _ ih₀ ih₁ => rw [map_mul_to_add, map_mul_to_add, ih₀, ih₁]
      | of a b =>
        apply f.property
        assumption
    map_one_to_zero := map_one_to_zero f.val
    map_mul_to_add a b := by
      induction a; induction b
      apply map_mul_to_add f.val
  }
  invFun f := {
    val := {
      toFun g := f (mk _ g)
      map_one_to_zero := by rw [map_one, map_one_to_zero]
      map_mul_to_add a b := by rw [map_mul, map_mul_to_add]
    }
    property a b h := by
      show f (mk r a) = f (mk r b)
      rw [GroupQuot.sound h]
  }
  leftInv f := by
    ext x; induction x with | mk x =>
    rfl
  rightInv f := by
    ext x
    rfl

@[simp] def lift_mk (f: { f: G →* M // ∀x y: G, r x y -> f x = f y }) (x: G) : lift r f (mk r x) = f.val x := rfl
@[simp] def liftLog_mk (f: { f: G →*+ N // ∀x y: G, r x y -> f x = f y }) (x: G) : liftLog r f (mk r x) = f.val x := rfl

attribute [irreducible] lift

instance [MonoidOps G] [IsMonoid G] [Subsingleton G] : Subsingleton (GroupQuot r) where
  allEq a b := by
    induction a; induction b
    rename_i a b
    rw [Subsingleton.allEq (α := G) a b]

def exact : mk r a = mk r b -> MulCon.generate r a b := by
  intro h
  apply Quotient.exact (s := ⟨MulCon.generate r, IsCon.eqv _⟩)
  exact ofQuot.inj h

end GroupQuot

structure AddGroupQuot [AddMonoidOps G] [IsAddMonoid G] (r: G -> G -> Prop) where
  ofQuot :: toQuot : AlgQuot (AddCon.generate r)

namespace AddGroupQuot

variable (r: G -> G -> Prop)

instance [AddMonoidOps G] [IsAddMonoid G] : Zero (AddGroupQuot r) where
  zero := ⟨0⟩
instance [AddMonoidOps G] [IsAddMonoid G] : Add (AddGroupQuot r) where
  add a b := ⟨a.toQuot + b.toQuot⟩
instance [AddMonoidOps G] [IsAddMonoid G] : SMul ℕ (AddGroupQuot r) where
  smul n a := ⟨n • a.toQuot⟩

instance [AddGroupOps G] [IsAddGroup G] : Neg (AddGroupQuot r) where
  neg a := ⟨-a.toQuot⟩
instance [AddGroupOps G] [IsAddGroup G] : Sub (AddGroupQuot r) where
  sub a b := ⟨a.toQuot - b.toQuot⟩
instance [AddGroupOps G] [IsAddGroup G] : SMul ℤ (AddGroupQuot r) where
  smul n a := ⟨n • a.toQuot⟩

def mk [AddMonoidOps G] [IsAddMonoid G] : G →+ AddGroupQuot r where
  toFun g := {
    toQuot := AlgQuot.mk (AddCon.generate r) g
  }
  map_zero := rfl
  map_add _ _ := rfl

@[induction_eliminator]
def ind [AddMonoidOps G] [IsAddMonoid G] { motive: AddGroupQuot r -> Prop } (mk: ∀x, motive (.mk r x)) (g: AddGroupQuot r) : motive g := by
  cases g with | ofQuot g =>
  induction g with | mk g =>
  apply mk g

instance [AddMonoidOps G] [IsAddMonoid G] : IsAddMonoid (AddGroupQuot r) where
  add_assoc a b c := by
    induction a with | mk a =>
    induction b with | mk b =>
    induction c with | mk c =>
    show mk r (a + b + c) = mk r (a + (b + c))
    rw [add_assoc]
  zero_add a := by
    induction a with | mk a =>
    show mk r (0 + a) = mk r a
    rw [zero_add]
  add_zero a := by
    induction a with | mk a =>
    show mk r (a + 0) = mk r a
    rw [add_zero]
  zero_nsmul a := by
    induction a with | mk a =>
    show mk r (0 • a) = mk r 0
    rw [zero_nsmul]
  succ_nsmul n a := by
    induction a with | mk a =>
    show mk r ((n + 1) • a) = mk r (n • a + a)
    rw [succ_nsmul]

instance [AddGroupOps G] [IsAddGroup G] : IsAddGroup (AddGroupQuot r) where
  sub_eq_add_neg a b := by
    induction a with | mk a =>
    induction b with | mk b =>
    show mk r (a - b) = mk r (a + -b)
    rw [sub_eq_add_neg]
  ofNat_zsmul a n := by
    induction a with | mk a =>
    show mk r ((n: ℤ) • a) = mk r (n • a)
    rw [ofNat_zsmul]
  negSucc_zsmul a n := by
    induction a with | mk a =>
    show mk r ((Int.negSucc n) • a) = mk r (-((n + 1) • a))
    rw [negSucc_zsmul]
  add_neg_cancel a := by
    induction a with | mk a =>
    show mk r (a + -a) = mk r 0
    rw [add_neg_cancel]

end AddGroupQuot
