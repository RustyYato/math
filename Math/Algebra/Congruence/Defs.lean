module

public import Math.Order.Relation.Defs
public import Math.Data.AddMul.Defs
public import Math.Tactic.Basic

namespace Math

section Property

public class IsCon (C α: Type*) [RelLike C α] where
  toEquiv (c: C) : Equivalence c := by intro c; exact c.toEquiv

public class IsAddCon (C α: Type*) [RelLike C α] [Add α] extends IsCon C α where
  resp_add (r: C) (a b c d: α) : r a c -> r b d -> r (a + b) (c + d) := by intro r; exact r.resp_add

public class IsMulCon (C α: Type*) [RelLike C α] [Mul α] extends IsCon C α where
  resp_mul (r: C) (a b c d: α) : r a c -> r b d -> r (a * b) (c * d) := by intro r; exact r.resp_mul

public class IsSMulCon (C K α: Type*) [RelLike C α] [SMul K α] extends IsCon C α where
  resp_smul (r: C) (k: K) (a b: α) : r a b -> r (k • a) (k • b) := by intro r; exact r.resp_smul

export IsAddCon (resp_add)
export IsMulCon (resp_mul)
export IsSMulCon (resp_smul)

public instance [RelLike C α ] [IsCon C α] (c: C) : IsRefl c where
  refl := (IsCon.toEquiv c).refl
public instance [RelLike C α ] [IsCon C α] (c: C) : IsSymm c where
  symm := (IsCon.toEquiv c).symm
public instance [RelLike C α ] [IsCon C α] (c: C) : IsTrans c where
  htrans := (IsCon.toEquiv c).trans

public instance (priority := 2000) (C α: Type*) [RelLike C α] : RelLike (MulOfAdd C) (MulOfAdd α) where
  coeFun c a b := c.get a b
  coeInj f g h := by
    apply DFunlike.ext (F := C); intro a
    apply DFunlike.ext; intro b
    apply congrFun (congrFun h _)
public instance (C α: Type*) [RelLike C α] [c: IsCon C α] : IsCon (MulOfAdd C) (MulOfAdd α) where
  toEquiv := c.toEquiv
public instance (C α: Type*) [RelLike C α] [IsCon C α] [Add α] [IsAddCon C α] : IsMulCon (MulOfAdd C) (MulOfAdd α) where
  resp_mul := resp_add (C := C) (α := α)

public instance (priority := 2000) (C α: Type*) [RelLike C α] : RelLike (AddOfMul C) (AddOfMul α) where
  coeFun c a b := c.get a b
  coeInj f g h := by
    apply DFunlike.ext (F := C); intro a
    apply DFunlike.ext; intro b
    apply congrFun (congrFun h _)
public instance (C α: Type*) [RelLike C α] [c: IsCon C α] : IsCon (AddOfMul C) (AddOfMul α) where
  toEquiv := c.toEquiv
public instance (C α: Type*) [RelLike C α] [IsCon C α] [Mul α] [IsMulCon C α] : IsAddCon (AddOfMul C) (AddOfMul α) where
  resp_add := resp_mul (C := C) (α := α)

end Property

section Defs

public structure Con (α: Type*) where
  toRel : α -> α -> Prop
  toEquiv : Equivalence toRel

public abbrev Con.toFun := @Con.toRel
public instance : RelLike (Con α) α where

public structure AddCon (α: Type*) [Add α] extends Con α where
  protected resp_add (a b c d: α) : toRel a c -> toRel b d -> toRel (a + b) (c + d)

public structure MulCon (α: Type*) [Mul α] extends Con α where
  protected resp_mul (a b c d: α) : toRel a c -> toRel b d -> toRel (a * b) (c * d)

public structure SMulCon (K α: Type*) [SMul K α] extends Con α where
  protected resp_smul (k: K) (a b: α) : toRel a b -> toRel (k • a) (k • b)

public structure LinearCon (K α: Type*) [Add α] [SMul K α] extends AddCon α, SMulCon K α where
public structure RingCon (α: Type*) [Add α] [Mul α] extends AddCon α, MulCon α where

public instance [Add α] : RelLike (AddCon α) α where
public instance [Mul α] : RelLike (MulCon α) α where
public instance [SMul K α] : RelLike (SMulCon K α) α where
public instance [Add α] [SMul K α] : RelLike (LinearCon K α) α where
public instance [Add α] [Mul α] : RelLike (RingCon α) α where

public instance [Add α] : IsAddCon (AddCon α) α where
public instance [Mul α] : IsMulCon (MulCon α) α where
public instance [SMul K α] : IsSMulCon (SMulCon K α) K α where
public instance [Add α] [SMul K α] : IsAddCon (LinearCon K α) α where
public instance [Add α] [SMul K α] : IsSMulCon (LinearCon K α) K α where
public instance [Add α] [Mul α] : IsAddCon (RingCon α) α where
public instance [Add α] [Mul α] : IsMulCon (RingCon α) α where

public structure AlgQuot {C α: Type*} (c: C) [RelLike C α] [IsCon C α] where
  ofQuot :: toQuot : Quotient ⟨c, IsCon.toEquiv c⟩

end Defs

namespace AlgQuot

variable {C α: Type*} [RelLike C α] [IsCon C α]

@[expose] public def mk (c: C) (val: α) : AlgQuot c where
  toQuot := Quotient.mk _ val

@[expose] public def lift {c: C} (f: α -> β) (h: ∀a b, c a b -> f a = f b) (q: AlgQuot c) : β := q.toQuot.lift f h

@[expose] public def lift₂ {c: C} (f: α -> α -> β) (h: ∀a₀ a₁ b₀ b₁, c a₀ b₀ -> c a₁ b₁ -> f a₀ a₁ = f b₀ b₁) (a b: AlgQuot c) : β := a.toQuot.liftOn₂ b.toQuot f h

@[induction_eliminator]
public theorem ind {c: C} {motive: AlgQuot c -> Prop} (mk: ∀a, motive (mk c a)) (q: AlgQuot c) : motive q := by
  obtain ⟨q⟩ := q
  induction q using Quotient.ind with | _ q => apply mk

public theorem sound {c: C} {a b: α} : c a b -> mk c a = mk c b := by
  intro h; unfold mk
  congr 1; apply Quotient.sound
  assumption

public theorem exact {c: C} {a b: α} : mk c a = mk c b -> c a b := by
  intro h
  exact Quotient.exact (ofQuot.inj h)

public instance [Add α] [IsAddCon C α] (c: C) : Add (AlgQuot c) where
  add := AlgQuot.lift₂ (fun a b => mk c (a + b)) <| by
    intro a₀ a₁ b₀ b₁ h g
    apply sound
    apply resp_add
    assumption
    assumption

public instance [Mul α] [IsMulCon C α] (c: C) : Mul (AlgQuot c) where
  mul := AlgQuot.lift₂ (fun a b => mk c (a * b)) <| by
    intro a₀ a₁ b₀ b₁ h g
    apply sound
    apply resp_mul
    assumption
    assumption

public instance [SMul K α] [IsSMulCon C K α] (c: C) : SMul K (AlgQuot c) where
  smul k := AlgQuot.lift (fun a => mk c (k • a)) <| by
    intro a b h
    apply sound
    apply resp_smul
    assumption

public instance [Zero α] (c: C) : Zero (AlgQuot c) where
  zero := AlgQuot.mk _ 0
public instance [One α] (c: C) : One (AlgQuot c) where
  one := AlgQuot.mk _ 1
public instance [NatCast α] (c: C) : NatCast (AlgQuot c) where
  natCast n := AlgQuot.mk _ n
public instance [IntCast α] (c: C) : IntCast (AlgQuot c) where
  intCast n := AlgQuot.mk _ n

end AlgQuot
