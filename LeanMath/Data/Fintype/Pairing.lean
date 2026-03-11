import LeanMath.Data.Fintype.Defs
import LeanMath.Data.Fin.Pairing
import LeanMath.Data.Bijection.Basic
import LeanMath.Data.Equiv.Basic

namespace Fintype

instance [fa: Fintype α] [fb: Fintype β] : Fintype (α ⊕' β) where
  card := card α + card β
  repr :=
    fa.repr.bind fun fa =>
    fb.repr.map fun fb => {
      bij := (Fin.sum (card α) (card β)).toBij.trans
        <| Equiv.sum_equiv_psum.toBij.trans
        <| (Bijection.psum_congr fa.bij fb.bij)
      try_decode :=
        match fa.try_decode with
        | .none => .none
        | .some da =>
        match fb.try_decode with
        | .none => .none
        | .some db => .some {
          val x := by
            apply (Fin.sum (card α) (card β)).symm _
            exact match x with
            | .inl x => .inl (da.val x)
            | .inr x => .inr (db.val x)
          property := by
            intro x
            dsimp
            apply (Fin.sum (card α) (card β)).inj
            rw [Equiv.symm_coe]
            generalize Fin.sum (card α) (card β) x = y
            cases y
            show Sum.inl _ = _
            rw [da.property]
            show Sum.inr _ = _
            rw [db.property]
        }
    }

instance [fa: Fintype α] [fb: Fintype β] : Fintype (α ×' β) where
  card := card α * card β
  repr :=
    fa.repr.bind fun fa =>
    fb.repr.map fun fb => {
      bij := (Fin.prod (card α) (card β)).toBij.trans
        <| Equiv.prod_equiv_pprod.toBij.trans
        <| (Bijection.pprod_congr fa.bij fb.bij)
      try_decode :=
        match fa.try_decode with
        | .none => .none
        | .some da =>
        match fb.try_decode with
        | .none => .none
        | .some db => .some {
          val x := by
            apply (Fin.prod (card α) (card β)).symm _
            exact (da.val x.fst, db.val x.snd)
          property x := by
            apply (Fin.prod (card α) (card β)).inj
            dsimp
            generalize Fin.prod (card α) (card β) x = y
            rw [Equiv.symm_coe]
            show (_, _) = _
            congr
            apply da.property
            apply db.property
        }
    }

instance [fa: Fintype α] [fb: Fintype β] : Fintype (α ⊕ β) :=
  ofEquiv Equiv.sum_equiv_psum.symm

instance [fa: Fintype α] [fb: Fintype β] : Fintype (α × β) :=
  ofEquiv Equiv.prod_equiv_pprod.symm

end Fintype
