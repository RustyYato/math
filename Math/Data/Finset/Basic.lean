module

public import Math.Data.Finset.Defs
public import Math.Data.Embedding.Defs

namespace Math

public def of_embedding (f: Fin n ↪ α) : Finset α where
  toMultiset := Multiset.mk (List.ofFn f)
  nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj; simp; simp at hi hj
    intro h; exact Fin.val_inj.mpr (f.inj h)
