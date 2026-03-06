import LeanMath.Algebra.Monoid.Action.Defs
import LeanMath.Logic.Relation.Defs

section

variable (R α: Type*)

inductive LinearCombo.Pre where
| zero
| of (r: R) (a: α)
| add (a b: Pre)

local instance : Zero (LinearCombo.Pre R α) where
  zero := .zero

local instance : Add (LinearCombo.Pre R α) where
  add := .add

inductive LinearCombo.Rel [Zero R] [Add R] : Pre R α -> Pre R α -> Prop where
| refl (a: Pre R α) : Rel a a
| symm {a b: Pre R α} : Rel a b -> Rel b a
| trans {a b c: Pre R α} : Rel a b -> Rel b c -> Rel a c

| zero a : Rel (.of 0 a) 0

| zero_add (a: Pre R α) : Rel (0 + a) a

| add_of (r s: R) (a: α) : Rel (.of (r + s) a) ((.of r a) + (.of s a))
| add_comm (a b: Pre R α) : Rel (a + b) (b + a)
| add_assoc (a b c: Pre R α) : Rel (a + b + c) (a + (b + c))

| add_congr (a b c d: Pre R α) : Rel a c -> Rel b d -> Rel (a + b) (c + d)

instance [Zero R] [Add R] : Relation.IsRefl (LinearCombo.Rel R α) where
  refl := .refl
instance [Zero R] [Add R] : Relation.IsSymm (LinearCombo.Rel R α) where
  symm := .symm
instance [Zero R] [Add R] : Relation.IsTrans (LinearCombo.Rel R α) where
  trans := .trans

instance LinearCombo.setoid [Zero R] [Add R] : Setoid (LinearCombo.Pre R α) := Relation.setoid (LinearCombo.Rel R α)

end

def LinearCombo.Pre.smul [SMul S R] (s: S) : LinearCombo.Pre R α -> LinearCombo.Pre R α
| zero => .zero
| of r a => .of (s • r) a
| add a b => .add (a.smul s) (b.smul s)

structure LinearCombo (R α: Type*) [Zero R] [Add R] where
  ofQuot :: toQuot : Quotient (LinearCombo.setoid R α)

namespace LinearCombo

section

variable [Zero R] [Add R]

def ofPre (p: Pre R α) : LinearCombo R α where
  toQuot := Quotient.mk _ p

def sound {a b: Pre R α} (h: a ≈ b) : ofPre a = ofPre b := by
  unfold ofPre; rw [Quotient.sound h]

def liftPre (f: Pre R α -> β) (h: ∀a b, a ≈ b -> f a = f b) (l: LinearCombo R α) : β :=
  l.toQuot.liftOn f h

def liftPre₂ (f: Pre R α -> Pre R α -> β) (h: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (a b: LinearCombo R α) : β :=
  a.toQuot.liftOn₂ b.toQuot f h

@[simp] def liftPre_ofPre (f: Pre R α -> β) (h) (a: Pre R α) : liftPre f h (ofPre a) = f a := rfl
@[simp] def liftPre₂_ofPre (f: Pre R α -> Pre R α -> β) (h) (a b: Pre R α) : liftPre₂ f h (ofPre a) (ofPre b) = f a b := rfl

def ind {motive: LinearCombo R α -> Prop} (ofPre: ∀a, motive (ofPre a)) (l: LinearCombo R α) : motive l := by
  obtain ⟨l⟩ := l
  induction l using Quotient.ind with | _ =>
  apply ofPre

end

instance [Zero R] [Add R] : Zero (LinearCombo R α) where
  zero := ofPre .zero

instance [Zero R] [Add R] : Add (LinearCombo R α) where
  add := liftPre₂ (fun a b => ofPre (a.add b)) <| by
    intro a b c d ac bd; apply sound
    apply Rel.add_congr
    assumption
    assumption

instance [SMul S R] [MonoidOps S] [IsMonoid S]
  [AddMonoidOps R] [IsAddMonoid R] [IsDistributiveAction S R]
  : SMul S (LinearCombo R α) where
  smul s := liftPre (fun a => ofPre (a.smul s)) <| by
    intro a b h
    dsimp
    induction h with
    | refl => rfl
    | symm => symm; assumption
    | trans _ _ iha ihb => rw [iha, ihb]
    | zero_add =>
      apply sound
      apply Rel.zero_add
    | zero =>
      apply sound
      show Pre.of _ _ ≈ _
      rw [smul_zero]
      apply Rel.zero
    | add_of =>
      apply sound
      show Pre.of _ _ ≈ Pre.add _ _
      rw [smul_add]
      apply Rel.add_of
    | add_comm =>
      apply sound
      apply Rel.add_comm
    | add_assoc =>
      apply sound
      apply Rel.add_assoc
    | add_congr =>
      show ofPre _ + ofPre _ = ofPre _ + ofPre _
      congr

variable [AddMonoidOps R] [IsAddMonoid R] [IsAddComm R]

def ι (a: α) : R →+ LinearCombo R α where
  toFun r := ofPre (.of r a)
  map_zero := by
    apply sound
    apply Rel.zero
  map_add := by
    intro a b
    apply sound
    apply Rel.add_of

def ιHom (S: Type*) [SMul S R] [MonoidOps S] [IsMonoid S] [IsDistributiveAction S R] (a: α) : R →ₗ[S] LinearCombo R α where
  toAddHom := (ι a).toAddHom
  map_smul _ _ := rfl

variable {S: Type*} [SMul S R] [MonoidOps S] [IsMonoid S] [IsDistributiveAction S R]

@[simp] def ιHom_eq_ι (a: α) (r: R) : ιHom S a r = ι a r := rfl

instance : IsLawfulSMulZero S (LinearCombo R α) where
  smul_zero _ := rfl

instance : IsRightDistribSMul S (LinearCombo R α) where
  smul_add s a b := by
    induction a using ind with | _ =>
    induction b using ind with | _ =>
    rfl

@[simp] def smul_ι (s: S) (a: α) (r: R) : s • ι a r = ι a (s • r) := rfl

@[induction_eliminator]
def induction
  {motive: LinearCombo R α -> Prop}
  (zero: motive 0)
  (ι: ∀(a: α) (r: R), motive (ι a r))
  (add: ∀a b, motive a -> motive b -> motive (a + b))
  (lc: LinearCombo R α) : motive lc := by
  induction lc using ind with | _ lc =>
  induction lc with
  | zero => apply zero
  | of => apply ι
  | add a b =>
    show motive (ofPre a + ofPre b)
    apply add
    assumption
    assumption

instance : SMul ℕ (LinearCombo R α) := inferInstance

instance : IsAddComm (LinearCombo R α) where
  add_comm a b := by
    induction a using ind with | _ a =>
    induction b using ind with | _ b =>
    apply sound
    apply Rel.add_comm

instance : IsLawfulZeroAdd (LinearCombo R α) where
  zero_add a := by
    induction a using ind with | _ =>
    apply sound
    apply Rel.zero_add
  add_zero a := by
    rw [add_comm]
    induction a using ind with | _ =>
    apply sound
    apply Rel.zero_add

instance : IsAddSemigroup (LinearCombo R α) where
  add_assoc a b c := by
    induction a using ind with | _ a =>
    induction b using ind with | _ b =>
    induction c using ind with | _ c =>
    apply sound
    apply Rel.add_assoc

instance : IsAddMonoid (LinearCombo R α) where
  zero_nsmul a := by
    induction a with
    | zero => rfl
    | ι a r =>
      show ι a (0 • r) = 0
      rw [zero_smul, map_zero]
    | add a b iha ihb =>
      rw [smul_add, iha, ihb, add_zero]
  succ_nsmul n a := by
    induction a with
    | zero => symm; apply add_zero
    | ι a r => simp [←map_add, succ_nsmul]
    | add a b iha ihb  =>
      rw [smul_add, smul_add, iha, ihb]
      ac_rfl

instance : IsDistributiveAction S (LinearCombo R α) where
  one_smul a := by
    induction a with
    | zero => rfl
    | ι a r => simp [one_smul]
    | add a b iha ihb => rw [smul_add, iha, ihb]
  mul_smul r s a := by
    induction a with
    | zero => rfl
    | ι a r => simp [mul_smul]
    | add a b iha ihb => simp [smul_add, iha, ihb]

attribute [irreducible] ι

end LinearCombo
