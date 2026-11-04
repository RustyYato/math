module

public import Math.Data.Bijection.Defs
public import Math.Data.Equiv.Defs
public import Math.Tactic.Basic

namespace Math

public inductive Fintype.Pre (α: Type*) (card: ℕ) where
| noInv
  (toBijection: Bijection (Fin card) α)
| hasInv
  (toBijection: Bijection (Fin card) α)
  (invFun: α -> Fin card)
  (h: Function.LeftInverse toBijection invFun)

public class Fintype (α: Type*) where
  card: ℕ
  toPre: Squash (Fintype.Pre α card)

public class inductive Finite (α: Type*) : Prop where
| intro (card: ℕ) (toBijection: Bijection (Fin card) α)

namespace Fintype

@[expose] public def Pre.toBijection : Pre α c -> Bijection (Fin c) α
| .noInv f => f
| .hasInv f _ _ => f

public instance [h: Fintype α] : Finite α :=
  h.toPre.recOnSubsingleton fun p => ⟨_, p.toBijection⟩

public theorem Pre.card_eq (a: Pre α ac) (b: Pre α bc) : ac = bc := by
  replace ⟨a, ha⟩ := a.toBijection
  replace ⟨b, hb⟩ := b.toBijection
  have h (x: α) : (∃i, a i = x) ↔ (∃i, b i = x) := by
    apply Iff.intro <;> intro
    apply hb
    apply ha
  clear ha hb
  induction ac generalizing bc with
  | zero =>
    cases bc with
    | zero => rfl
    | succ bc => nomatch (h (b 0)).mpr ⟨_, rfl⟩
  | succ ac ih =>
    cases bc with
    | zero => nomatch (h (a 0)).mp ⟨_, rfl⟩
    | succ bc =>
    have ⟨i, hi⟩ := (h (a 0)).mp ⟨_, rfl⟩
    let fin_succ : Fin ac ↪ Fin (ac + 1) := {
      toFun := Fin.succ
      injective _ _ := Fin.succ_inj.mp
    }
    let re : Fin bc ↪ Fin (bc + 1) := {
      toFun j :=
        if j.val < i.val then
          j.castSucc
        else
          j.succ
      injective := by
        intro x y h; dsimp at h
        split at h <;> split at h <;> rename_i h₀ h₁
        · exact Fin.castSucc_inj.mp h
        · have := congrArg Fin.val h
          simp at this
          rw [this] at h₀
          omega
        · have := congrArg Fin.val h
          simp at this
          rw [←this] at h₁
          omega
        · exact Fin.succ_inj.mp h
    }
    congr; apply ih (fin_succ.trans a) (b.comp re)
    intro x; dsimp
    apply Iff.intro
    · rintro ⟨j, rfl⟩
      have ⟨k, hk⟩ := (h (a (fin_succ j))).mp ⟨_, rfl⟩
      if hk':k.val < i.val then
        exists ⟨k.val, by omega⟩
        show b (re.toFun _) = _
        simpa [re, hk']
      else
        have : i ≠ k := by
          intro rfl
          rw [hi]  at hk
          nomatch Fin.succ_ne_zero _ (a.inj hk).symm
        exists ⟨k.val - 1, by omega⟩
        show b (re.toFun _) = _
        simp [re]; rw [ite_eq_right]
        rw [←hk]; congr; omega
        omega
    · rintro ⟨j, rfl⟩
      have ⟨k, hk⟩ := (h (b (re j))).mpr ⟨_, rfl⟩
      rw [←hk]
      cases k using Fin.cases
      rw [←hi, b.inj.eq_iff] at hk
      replace hk : i = re.toFun j := hk
      simp [re] at hk
      split at hk <;> rename_i h
      rw [hk] at h; nomatch Nat.lt_irrefl _ h
      rw [hk] at h; nomatch h (Nat.lt_succ_self _)
      refine ⟨_, rfl⟩

public instance : Subsingleton (Fintype α) where
  allEq a b := by
    obtain ⟨a, pa⟩ := a
    obtain ⟨b, pb⟩ := b
    induction pa using Quotient.ind with | _ pa =>
    induction pb using Quotient.ind with | _ pb =>
    cases pa.card_eq pb
    congr 1; apply Subsingleton.allEq

@[expose, instance_reducible] public def ofEquivFin (f: Fin n ≃ β) : Fintype β where
  card := n
  toPre := .mk <| .hasInv {
    toFun := f.toFun
    injective := f.rightInv.injective
    surjective x := ⟨f.invFun x, f.leftInv _⟩
  } f.invFun f.leftInv
@[expose, instance_reducible] public def ofBijectionFin (f: Bijection (Fin n) β) : Fintype β where
  card := n
  toPre := .mk <| .noInv f

public instance : Fintype (Fin n) := ofEquivFin (Equiv.id _)
public instance : Fintype Unit := ofEquivFin (n := 1) {
  toFun _ := ()
  invFun _ := ⟨0, by decide⟩
  leftInv _ := rfl
  rightInv x := by
    obtain ⟨x, xLt⟩ := x
    match x with
    | 0 => rfl
    | x + 1 => nomatch (Nat.lt_of_succ_lt_succ xLt)
}
public instance : Fintype Bool := ofEquivFin (n := 2) {
  toFun
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => true
  | ⟨n + 2, h⟩ => nomatch (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h))
  invFun
  | false => ⟨0, by decide⟩
  | true => ⟨1, by decide⟩
  leftInv b := by cases b <;> rfl
  rightInv x := by
    obtain ⟨x, xLt⟩ := x
    match x with
    | 0 | 1 => rfl
    | x + 2 => nomatch (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ xLt))
}

@[expose, instance_reducible] public def ofEquiv [ft: Fintype α] (f: α ≃ β) : Fintype β where
  card := ft.card
  toPre :=
    ft.toPre.recOnSubsingleton fun p =>
    let bij (g: Bijection (Fin ft.card) α) := (g.trans {
      toFun := f
      injective := f.inj
      surjective := f.surj
    })
    .mk <| match p with
      | .noInv g => .noInv (bij g)
      | .hasInv g inv hinv => .hasInv (bij g) (fun b => inv (f.symm b)) <| by
        intro b; dsimp
        show f (g (inv (f.symm _))) = _
        rw [hinv, f.symm_apply]
@[expose, instance_reducible] public def ofBijection [ft: Fintype α] (f: Bijection α β) : Fintype β where
  card := ft.card
  toPre := ft.toPre.recOnSubsingleton fun p =>
    .mk <| .noInv (f.comp p.toBijection)

end Fintype

namespace Finite

public theorem ofBijection [ft: Finite α] (f: Bijection α β) : Finite β := by
  obtain ⟨c, bij⟩ := ft
  refine ⟨c, ?_⟩
  exact f.comp bij
public theorem ofEquiv [ft: Finite α] (f: α ≃ β) : Finite β :=
  ofBijection {
    toFun := f.toFun
    injective := f.rightInv.injective
    surjective := f.symm.rightInv.surjective
  }

end Finite
