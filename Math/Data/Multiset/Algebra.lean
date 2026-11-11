module

public import Math.Data.Multiset.Defs
public import Math.Algebra.Monoid.Defs

namespace Math.Multiset

public def prod
  [MonoidOps α] [IsMonoid α] [IsComm α]
  (ms: Multiset α) : α := ms.lift List.prod <| by
    intro a b h; induction h with
    | nil => rfl
    | trans _ _ iha ihb => rw [iha, ihb]
    | cons _ _ ih => rw [List.prod_cons, List.prod_cons, ih]
    | swap a b => simp [List.prod_cons]; rw [←mul_assoc, ←mul_assoc, mul_comm a]

public def sum
  [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α]
  (ms: Multiset α) : α := prod (α := MulOfAdd α) ms

section Prod

variable [MonoidOps α] [IsMonoid α] [IsComm α]

@[simp] public theorem prod_nil : prod (α := α) nil = 1 := List.prod_nil
@[simp] public theorem prod_cons (a: α) (as: Multiset α) : (a::ₘas).prod = a * as.prod := by
  unfold prod
  induction as using ind
  show List.prod _ = _
  rw [List.prod_cons]
  rfl

end Prod

section Sum

variable [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α]

@[simp] public theorem sum_nil : sum (α := α) nil = 0 := prod_nil (α := MulOfAdd α)
@[simp] public theorem sum_cons (a: α) (as: Multiset α) : (a::ₘas).sum = a + as.sum := prod_cons (α := MulOfAdd α) _ _

end Sum
