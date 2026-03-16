import LeanMath.Logic.Funlike
import LeanMath.Logic.Relation.Defs

class IsCon (R: Sort*) {α: Sort*} [RelLike R α] : Prop where
  protected eqv (r: R): Equivalence r := by intro r; exact r.eqv

class IsAddCon (R: Sort*) {α: Type*} [RelLike R α] [Add α] extends IsCon R where
  protected resp_add (r: R) {a b c d: α} : r a c -> r b d -> r (a + b) (c + d) := by intro r; exact r.resp_add

class IsMulCon (R: Sort*) {α: Type*} [RelLike R α] [Mul α] extends IsCon R where
  protected resp_mul (r: R) {a b c d: α} : r a c -> r b d -> r (a * b) (c * d) := by intro r; exact r.resp_mul

class IsSMulCon (R: Sort*) (S: Type*) {α: Type*} [RelLike R α] [SMul S α] extends IsCon R where
  protected resp_smul (r: R) (s: S) {a b: α} : r a b -> r (s • a) (s • b) := by intro r; exact r.resp_smul

class IsPowCon (R: Sort*) (S: Type*) {α: Type*} [RelLike R α] [Pow α S] extends IsCon R where
  protected resp_pow (r: R) (s: S) {a b: α} : r a b -> r (a ^ s) (b ^ s) := by intro r; exact r.resp_pow

def resp_add [RelLike R α] [Add α] [IsAddCon R] (r: R): ∀{a b c d: α}, r a c -> r b d -> r (a + b) (c + d) := IsAddCon.resp_add _
def resp_mul [RelLike R α] [Mul α] [IsMulCon R] (r: R): ∀{a b c d: α}, r a c -> r b d -> r (a * b) (c * d) := IsMulCon.resp_mul _
def resp_smul [RelLike R α] [SMul S α] [IsSMulCon R S] (r: R): ∀(s: S) {a b: α}, r a b -> r (s • a) (s • b) := IsSMulCon.resp_smul _
def resp_pow [RelLike R α] [Pow α S] [IsPowCon R S] (r: R): ∀(s: S) {a b: α}, r a b -> r (a ^ s) (b ^ s) := IsPowCon.resp_pow _

structure EqCon (α: Sort*)
deriving Inhabited

instance : RelLike (EqCon α) α where
  coeFun _ a b := a = b
  coeInj _ _ _ := rfl

instance : IsCon (EqCon α) where
  eqv _ := Relation.equiv (· = ·)
instance [Add α] : IsAddCon (EqCon α) where
  resp_add := by
    intros
    congr
instance [Mul α] : IsMulCon (EqCon α) where
  resp_mul := by
    intros
    congr
instance [SMul R α] : IsSMulCon (EqCon α) R where
  resp_smul := by
    intros
    congr
instance [Pow α R] : IsPowCon (EqCon α) R where
  resp_pow := by
    intros
    congr


instance (R: Sort*) {α: Sort*} [RelLike R α] [IsCon R] (r: R) : Relation.IsRefl r where
  refl := (IsCon.eqv r).refl
instance (R: Sort*) {α: Sort*} [RelLike R α] [IsCon R] (r: R) : Relation.IsSymm r where
  symm := (IsCon.eqv r).symm
instance (R: Sort*) {α: Sort*} [RelLike R α] [IsCon R] (r: R) : Relation.IsTrans r where
  trans := (IsCon.eqv r).trans

structure Con (α: Type*) where
  protected toFun: α -> α -> Prop
  protected eqv: Equivalence toFun

instance : RelLike (Con α) α where

structure AddCon (α: Type*) [Add α] extends Con α where
  protected resp_add {a b c d: α} : toFun a c -> toFun b d -> toFun (a + b) (c + d)

instance [Add α] : RelLike (AddCon α) α where
instance [Add α] : IsAddCon (AddCon α) where

inductive AddCon.GenerateRel [Add α] (r: α -> α -> Prop) : α -> α -> Prop where
| of (a b: α) : r a b -> GenerateRel r a b
| add (a b c d: α) : GenerateRel r a c -> GenerateRel r b d -> GenerateRel r (a + b) (c + d)
| refl (a: α) : GenerateRel r a a
| symm (a b: α) : GenerateRel r b a -> GenerateRel r a b
| trans (a b c: α) : GenerateRel r a b -> GenerateRel r b c -> GenerateRel r a c

def AddCon.generate [Add α] (r: α -> α -> Prop) : AddCon α where
  toFun := AddCon.GenerateRel r
  eqv := ⟨
    AddCon.GenerateRel.refl,
    AddCon.GenerateRel.symm _ _,
    AddCon.GenerateRel.trans _ _ _,
  ⟩
  resp_add := AddCon.GenerateRel.add _ _ _ _

def AddCon.generate_of [Add α] {r: α -> α -> Prop} (h: r a b) : AddCon.generate r a b :=
  AddCon.GenerateRel.of _ _ h

def AddCon.of_generate
  [Add α] [RelLike S α] [IsAddCon S]
  {r: α -> α -> Prop} {s: S}
  (h: ∀a b, r a b -> s a b) (rab: AddCon.generate r a b) : s a b := by
  induction rab with
  | of => apply h; assumption
  | add =>
    apply resp_add
    assumption
    assumption
  | refl => rfl
  | symm =>
    apply Relation.symm
    assumption
  | trans =>
    apply Relation.trans <;> assumption

def AddCon.map [Add α] {r s: α -> α -> Prop} (h: ∀a b, r a b -> s a b) (rab: AddCon.generate r a b) : AddCon.generate s a b := by
  apply of_generate _ rab
  intro _ _ g
  apply generate_of
  apply h
  assumption

structure MulCon (α: Type*) [Mul α] extends Con α where
  protected resp_mul {a b c d: α} : toFun a c -> toFun b d -> toFun (a * b) (c * d)

instance [Mul α] : RelLike (MulCon α) α where
instance [Mul α] : IsMulCon (MulCon α) where

inductive MulCon.GenerateRel [Mul α] (r: α -> α -> Prop) : α -> α -> Prop where
| of (a b: α) : r a b -> GenerateRel r a b
| mul (a b c d: α) : GenerateRel r a c -> GenerateRel r b d -> GenerateRel r (a * b) (c * d)
| refl (a: α) : GenerateRel r a a
| symm (a b: α) : GenerateRel r b a -> GenerateRel r a b
| trans (a b c: α) : GenerateRel r a b -> GenerateRel r b c -> GenerateRel r a c

def MulCon.generate [Mul α] (r: α -> α -> Prop) : MulCon α where
  toFun := MulCon.GenerateRel r
  eqv := ⟨
    MulCon.GenerateRel.refl,
    MulCon.GenerateRel.symm _ _,
    MulCon.GenerateRel.trans _ _ _,
  ⟩
  resp_mul := MulCon.GenerateRel.mul _ _ _ _

def MulCon.generate_of [Mul α] {r: α -> α -> Prop} (h: r a b) : MulCon.generate r a b :=
  MulCon.GenerateRel.of _ _ h

def MulCon.of_generate
  [Mul α] [RelLike S α] [IsMulCon S]
  {r: α -> α -> Prop} {s: S}
  (h: ∀a b, r a b -> s a b) (rab: MulCon.generate r a b) : s a b := by
  induction rab with
  | of => apply h; assumption
  | mul =>
    apply resp_mul
    assumption
    assumption
  | refl => rfl
  | symm =>
    apply Relation.symm
    assumption
  | trans =>
    apply Relation.trans <;> assumption

structure SMulCon (S α: Type*) [SMul S α] extends Con α where
  protected resp_smul (s: S) {a b: α} : toFun a b -> toFun (s • a) (s • b)

instance [SMul S α] : RelLike (SMulCon S α) α where
instance [SMul S α] : IsSMulCon (SMulCon S α) S where

inductive SMulCon.GenerateRel [SMul S α] (r: α -> α -> Prop) : α -> α -> Prop where
| of (a b: α) : r a b -> GenerateRel r a b
| smul (s: S) (a b: α) : GenerateRel r a b -> GenerateRel r (s • a) (s • b)
| refl (a: α) : GenerateRel r a a
| symm (a b: α) : GenerateRel r b a -> GenerateRel r a b
| trans (a b c: α) : GenerateRel r a b -> GenerateRel r b c -> GenerateRel r a c

def SMulCon.generate [SMul S α] (r: α -> α -> Prop) : SMulCon S α where
  toFun := SMulCon.GenerateRel r
  eqv := ⟨
    SMulCon.GenerateRel.refl,
    SMulCon.GenerateRel.symm _ _,
    SMulCon.GenerateRel.trans _ _ _,
  ⟩
  resp_smul := SMulCon.GenerateRel.smul

def SMulCon.generate_of [SMul S α] {r: α -> α -> Prop} (h: r a b) : SMulCon.generate (S := S) r a b :=
  SMulCon.GenerateRel.of _ _ h

def SMulCon.of_generate
  [SMul R α] [RelLike S α] [IsSMulCon S R]
  {r: α -> α -> Prop} {s: S}
  (h: ∀a b, r a b -> s a b) (rab: SMulCon.generate (S := R) r a b) : s a b := by
  induction rab with
  | of => apply h; assumption
  | smul =>
    apply resp_smul
    assumption
  | refl => rfl
  | symm =>
    apply Relation.symm
    assumption
  | trans =>
    apply Relation.trans <;> assumption

def SMulCon.map [SMul R α] {r s: α -> α -> Prop} (h: ∀a b, r a b -> s a b) (rab: SMulCon.generate (S := R) r a b) : SMulCon.generate (S := R) s a b := by
  apply of_generate _ rab
  intro _ _ g
  apply generate_of
  apply h
  assumption

structure RingCon (α: Type*) [Add α] [Mul α] extends AddCon α, MulCon α where

instance [Add α] [Mul α] : RelLike (RingCon α) α where
instance [Add α] [Mul α] : IsAddCon (RingCon α) where
instance [Add α] [Mul α] : IsMulCon (RingCon α) where

inductive RingCon.GenerateRel [Add α] [Mul α] (r: α -> α -> Prop) : α -> α -> Prop where
| of (a b: α) : r a b -> GenerateRel r a b
| add (a b c d: α) : GenerateRel r a c -> GenerateRel r b d -> GenerateRel r (a + b) (c + d)
| mul (a b c d: α) : GenerateRel r a c -> GenerateRel r b d -> GenerateRel r (a * b) (c * d)
| refl (a: α) : GenerateRel r a a
| symm (a b: α) : GenerateRel r b a -> GenerateRel r a b
| trans (a b c: α) : GenerateRel r a b -> GenerateRel r b c -> GenerateRel r a c

def RingCon.generate [Add α] [Mul α] (r: α -> α -> Prop) : RingCon α where
  toFun := RingCon.GenerateRel r
  eqv := ⟨
    RingCon.GenerateRel.refl,
    RingCon.GenerateRel.symm _ _,
    RingCon.GenerateRel.trans _ _ _,
  ⟩
  resp_add := RingCon.GenerateRel.add _ _ _ _
  resp_mul := RingCon.GenerateRel.mul _ _ _ _

def RingCon.generate_of [Add α] [Mul α] {r: α -> α -> Prop} (h: r a b) : RingCon.generate r a b :=
  RingCon.GenerateRel.of _ _ h

def RingCon.of_generate
  [Add α] [Mul α] [RelLike S α] [IsAddCon S] [IsMulCon S]
  {r: α -> α -> Prop} {s: S}
  (h: ∀a b, r a b -> s a b) (rab: RingCon.generate r a b) : s a b := by
  induction rab with
  | of => apply h; assumption
  | add =>
    apply resp_add
    assumption
    assumption
  | mul =>
    apply resp_mul
    assumption
    assumption
  | refl => rfl
  | symm =>
    apply Relation.symm
    assumption
  | trans =>
    apply Relation.trans <;> assumption

def RingCon.map [Add α] [Mul α] {r s: α -> α -> Prop} (h: ∀a b, r a b -> s a b) (rab: RingCon.generate r a b) : RingCon.generate s a b := by
  apply of_generate _ rab
  intro _ _ g
  apply generate_of
  apply h
  assumption

structure ModuleCon (S α: Type*) [Add α] [SMul S α] extends AddCon α, SMulCon S α where

instance [Add α] [SMul S α] : RelLike (ModuleCon S α) α where
instance [Add α] [SMul S α] : IsAddCon (ModuleCon S α) where
instance [Add α] [SMul S α] : IsSMulCon (ModuleCon S α) S where

inductive ModuleCon.GenerateRel [Add α] [SMul S α] (r: α -> α -> Prop) : α -> α -> Prop where
| of (a b: α) : r a b -> GenerateRel r a b
| add (a b c d: α) : GenerateRel r a c -> GenerateRel r b d -> GenerateRel r (a + b) (c + d)
| smul (s: S) (a b: α) : GenerateRel r a b -> GenerateRel r (s • a) (s • b)
| refl (a: α) : GenerateRel r a a
| symm (a b: α) : GenerateRel r b a -> GenerateRel r a b
| trans (a b c: α) : GenerateRel r a b -> GenerateRel r b c -> GenerateRel r a c

def ModuleCon.generate [Add α] [SMul S α] (r: α -> α -> Prop) : ModuleCon S α where
  toFun := ModuleCon.GenerateRel r
  eqv := ⟨
    ModuleCon.GenerateRel.refl,
    ModuleCon.GenerateRel.symm _ _,
    ModuleCon.GenerateRel.trans _ _ _,
  ⟩
  resp_add := ModuleCon.GenerateRel.add _ _ _ _
  resp_smul := ModuleCon.GenerateRel.smul

def ModuleCon.generate_of [Add α] [SMul S α] {r: α -> α -> Prop} (h: r a b) : ModuleCon.generate (S := S) r a b :=
  ModuleCon.GenerateRel.of _ _ h

def AlgQuot {R α: Sort*} [RelLike R α] [IsCon R] (r: R) := Quotient ⟨r, IsCon.eqv r⟩

variable {R: Sort*} {α: Type*} [RelLike R α] [IsCon R] (r: R)

namespace AlgQuot

structure MkHom (r: R) where

instance : FunLike (MkHom r) α (AlgQuot r) where
  coeFun _ := Quotient.mk _
  coeInj _ _ _ := rfl

def mk : MkHom r := ⟨⟩
def sound (a b: α) : r a b -> mk r a = mk r b := Quotient.sound (s := ⟨_ ,_⟩)
@[induction_eliminator]
def ind {motive: AlgQuot r -> Prop} (mk: ∀x, motive (AlgQuot.mk r x)) (q: AlgQuot r) : motive q := Quotient.ind mk q

instance [Zero α] [IsCon R] : Zero (AlgQuot r) where
  zero := AlgQuot.mk r 0
instance [One α] [IsCon R] : One (AlgQuot r) where
  one := AlgQuot.mk r 1

instance [Add α] [IsAddCon R] : Add (AlgQuot r) where
  add := by
    refine Quotient.lift₂ ?_ ?_
    exact fun a b => AlgQuot.mk r (a + b)
    intros
    apply AlgQuot.sound
    apply resp_add
    assumption
    assumption

instance [Mul α] [IsMulCon R] : Mul (AlgQuot r) where
  mul := by
    refine Quotient.lift₂ ?_ ?_
    exact fun a b => AlgQuot.mk r (a * b)
    intros
    apply AlgQuot.sound
    apply resp_mul
    assumption
    assumption

instance [SMul S α] [IsSMulCon R S] : SMul S (AlgQuot r) where
  smul s := by
    refine Quotient.lift ?_ ?_
    exact fun a => AlgQuot.mk r (s • a)
    intros
    apply AlgQuot.sound
    apply resp_smul
    assumption

instance [Pow α S] [IsPowCon R S] : Pow (AlgQuot r) S where
  pow := flip fun s => by
    refine Quotient.lift ?_ ?_
    exact fun a => AlgQuot.mk r (a ^ s)
    intros
    apply AlgQuot.sound
    apply resp_pow
    assumption

instance [NatCast α] : NatCast (AlgQuot r) where
  natCast n := AlgQuot.mk r n
instance [IntCast α] : IntCast (AlgQuot r) where
  intCast n := AlgQuot.mk r n

end AlgQuot
