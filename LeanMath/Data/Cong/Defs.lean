import LeanMath.Logic.Funlike

class IsCon (R: Sort*) {α: Sort*} [RelLike R α] : Prop where
  protected eqv (r: R): Equivalence r := by intro r; exact r.eqv

class IsAddCon (R: Sort*) {α: Type*} [RelLike R α] [Add α] extends IsCon R where
  protected resp_add (r: R) {a b c d: α} : r a c -> r b d -> r (a + b) (c + d) := by intro r; exact r.resp_add

class IsMulCon (R: Sort*) {α: Type*} [RelLike R α] [Mul α] extends IsCon R where
  protected resp_mul (r: R) {a b c d: α} : r a c -> r b d -> r (a * b) (c * d) := by intro r; exact r.resp_mul

class IsSMulCon (R: Sort*) (S: Type*) {α: Type*} [RelLike R α] [SMul S α] extends IsCon R where
  protected resp_smul (r: R) (s: S) {a b: α} : r a b -> r (s • a) (s • b) := by intro r; exact r.resp_smul

def resp_add [RelLike R α] [Add α] [IsAddCon R] (r: R): ∀{a b c d: α}, r a c -> r b d -> r (a + b) (c + d) := IsAddCon.resp_add _
def resp_mul [RelLike R α] [Mul α] [IsMulCon R] (r: R): ∀{a b c d: α}, r a c -> r b d -> r (a * b) (c * d) := IsMulCon.resp_mul _
def resp_smul [RelLike R α] [SMul S α] [IsSMulCon R S] (r: R): ∀(s: S) {a b: α}, r a b -> r (s • a) (s • b) := IsSMulCon.resp_smul _

structure Con (α: Type*) where
  toFun: α -> α -> Prop
  eqv: Equivalence toFun

instance : RelLike (Con α) α where

structure AddCon (α: Type*) [Add α] extends Con α where
  resp_add {a b c d: α} : toFun a c -> toFun b d -> toFun (a + b) (c + d)

instance [Add α] : RelLike (AddCon α) α where
instance [Add α] : IsAddCon (AddCon α) where

private inductive AddCon.GenerateRel [Add α] (r: α -> α -> Prop) : α -> α -> Prop where
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

structure MulCon (α: Type*) [Mul α] extends Con α where
  resp_mul {a b c d: α} : toFun a c -> toFun b d -> toFun (a * b) (c * d)

instance [Mul α] : RelLike (MulCon α) α where
instance [Mul α] : IsMulCon (MulCon α) where

private inductive MulCon.GenerateRel [Mul α] (r: α -> α -> Prop) : α -> α -> Prop where
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

structure SMulCon (S α: Type*) [SMul S α] extends Con α where
  resp_smul (s: S) {a b: α} : toFun a b -> toFun (s • a) (s • b)

instance [SMul S α] : RelLike (SMulCon S α) α where
instance [SMul S α] : IsSMulCon (SMulCon S α) S where

private inductive SMulCon.GenerateRel [SMul S α] (r: α -> α -> Prop) : α -> α -> Prop where
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

structure RingCon (α: Type*) [Add α] [Mul α] extends AddCon α, MulCon α where

instance [Add α] [Mul α] : RelLike (RingCon α) α where
instance [Add α] [Mul α] : IsAddCon (RingCon α) where
instance [Add α] [Mul α] : IsMulCon (RingCon α) where

private inductive RingCon.GenerateRel [Add α] [Mul α] (r: α -> α -> Prop) : α -> α -> Prop where
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

structure ModuleCon (S α: Type*) [Add α] [SMul S α] extends AddCon α, SMulCon S α where

instance [Add α] [SMul S α] : RelLike (ModuleCon S α) α where
instance [Add α] [SMul S α] : IsAddCon (ModuleCon S α) where
instance [Add α] [SMul S α] : IsSMulCon (ModuleCon S α) S where

private inductive ModuleCon.GenerateRel [Add α] [SMul S α] (r: α -> α -> Prop) : α -> α -> Prop where
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

def AlgQuot {R α: Sort*} [RelLike R α] [IsCon R] (r: R) := Quotient ⟨r, IsCon.eqv r⟩

variable {R: Sort*} {α: Type*} [RelLike R α] [IsCon R] (r: R)

def AlgQuot.mk : α -> AlgQuot r := Quotient.mk _
def AlgQuot.sound (a b: α) : r a b -> mk r a = mk r b := Quotient.sound (s := ⟨_ ,_⟩)

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
