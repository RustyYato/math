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
