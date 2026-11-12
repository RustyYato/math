module

public import Math.Data.Finset.Defs
public import Math.Data.Multiset.Algebra

namespace Math.Finset

@[expose] public def prod
  [MonoidOps α] [IsMonoid α] [IsComm α]
  (f: ι -> α) (s: Finset ι) : α := (s.toMultiset.map f).prod

@[expose] public def sum
  [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α]
  (f: ι -> α) (s: Finset ι) : α := (s.toMultiset.map f).sum

section Prod

variable [MonoidOps α] [IsMonoid α] [IsComm α]
  (f: ι -> α)

@[simp] public theorem pred_empty : prod f ∅ = 1 := Multiset.prod_nil
@[simp] public theorem prod_insert_unique (a: ι) (s: Finset ι) (ha: a ∉ s) : prod f (s.insert_unique a ha) = f a * prod f s := by
  change Multiset.prod (Multiset.map _ (_::ₘ_)) = _
  rw [Multiset.map_cons, Multiset.prod_cons]; rfl
@[simp] public theorem prod_singleton (a: ι) : prod f {a} = f a := by
  show prod f (Finset.insert_unique ∅ a nofun) = _
  simp [mul_one]
end Prod

section Sum

variable [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α]
  (f: ι -> α)

@[simp] public theorem sum_empty : sum f ∅ = 0 := Multiset.sum_nil
@[simp] public theorem sum_insert_unique (a: ι) (s: Finset ι) (ha: a ∉ s) : sum f (s.insert_unique a ha) = f a + sum f s := by
  change Multiset.sum (Multiset.map _ (_::ₘ_)) = _
  rw [Multiset.map_cons, Multiset.sum_cons]; rfl
@[simp] public theorem sum_singleton (a: ι) : sum f {a} = f a := by
  show sum f (Finset.insert_unique ∅ a nofun) = _
  simp [add_zero]

end Sum
