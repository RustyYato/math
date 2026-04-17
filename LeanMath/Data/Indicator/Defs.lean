import LeanMath.Algebra.Group.Defs

def Decidable.not_exists_not' {P: α -> Prop} [∀x, Decidable (P x)] : (¬ ∃x, ¬P x) ↔ ∀x, P x := by
  apply Iff.intro
  · intro h x
    exact Decidable.not_not.mp (fun p => h ⟨x, p⟩)
  · intro h ⟨_, g⟩
    exact g (h _)

inductive Indicator where
| one
| flip
deriving DecidableEq

namespace Indicator

instance : One Indicator where
  one := .one
instance : Mul Indicator where
  mul
  | 1, x => x
  | x, 1 => x
  | .flip, .flip => 1
instance : Inv Indicator where
  inv := id

instance {P: Indicator -> Prop} [∀x, Decidable (P x)] : Decidable (∃x, P x) :=
  if h:P 1 then
    .isTrue ⟨_, h⟩
  else if g:P .flip then
    .isTrue ⟨_, g⟩
  else
    .isFalse fun
      | ⟨1, hx⟩ => h hx
      | ⟨.flip, hx⟩ => g hx

instance {P: Indicator -> Prop} [∀x, Decidable (P x)] : Decidable (∀x, P x) :=
  decidable_of_decidable_of_iff (p := ¬∃x, ¬P x) <| Decidable.not_exists_not'

instance : IsSemigroup Indicator where
  mul_assoc := of_decide_eq_true rfl
instance : IsLawfulOneMul Indicator where
  one_mul := of_decide_eq_true rfl
  mul_one := of_decide_eq_true rfl

instance : MonoidOps Indicator where
  toPowN := defaultPowN
instance : GroupOps Indicator where
  toPowZ := defaultPowZ
  div a b := a * b⁻¹

instance : IsGroup Indicator where
  mul_assoc := of_decide_eq_true rfl
  one_mul := of_decide_eq_true rfl
  mul_one := of_decide_eq_true rfl
  div_eq_mul_inv := of_decide_eq_true rfl
  mul_inv_cancel := of_decide_eq_true rfl
  zpow_ofNat _ _ := rfl
  zpow_negSucc _ _ := rfl

end Indicator
