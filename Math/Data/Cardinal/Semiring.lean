module

public import Math.Data.Equiv.Basic
public import Math.Data.Cardinal.Order
public import Math.Algebra.Semiring.Char

import Math.Algebra.AddMonoidWithOne.Defs.Lemmas

namespace Math.Cardinal

public def ofNat : ℕ ↪ Cardinal.{u} :=
  Cardinal.ulift.comp Cardinal.fin

public def zero : Cardinal := type PEmpty
public def one : Cardinal := type PUnit

@[simp] public theorem ofNat_zero : ofNat 0 = zero := by
  change ulift (type _) = zero
  rw [ulift_type]
  exact sound (Equiv.empty _ _)
@[simp] public theorem ofNat_one : ofNat 1 = one := by
  change ulift (type _) = one
  rw [ulift_type]
  exact sound (Equiv.unique _ _)
@[simp] public theorem ofNat_eq_fin (n: ℕ) : ofNat n = fin n := by
  change ulift (type _) = type _
  rw [ulift_type]
  exact sound Equiv.ulift

public def add : Cardinal -> Cardinal -> Cardinal :=
  lift₂ (fun a b => type (a ⊕ b)) <| by
    intro A B C D h g
    apply sound
    apply Equiv.congr_sum <;> assumption

public def mul : Cardinal -> Cardinal -> Cardinal :=
  lift₂ (fun a b => type (a × b)) <| by
    intro A B C D h g
    apply sound
    apply Equiv.congr_prod <;> assumption

public def pow : Cardinal -> Cardinal -> Cardinal :=
  lift₂ (fun a b => type (b -> a)) <| by
    intro A B C D h g
    apply sound
    apply Equiv.congr_func <;> assumption

public instance : Zero Cardinal where
  zero := zero
public instance : One Cardinal where
  one := one
public instance : Add Cardinal where
  add := add
public instance : Mul Cardinal where
  mul := mul
public instance : HPow Cardinal Cardinal Cardinal where
  hPow := pow

public theorem zero_eq : 0 = type PEmpty := by rfl
public theorem one_eq : 1 = type PUnit := by rfl

@[simp] public theorem type_add_type : type A + type B = type (A ⊕ B) := by
  apply lift₂_type
@[simp] public theorem type_mul_type : type A * type B = type (A × B) := by
  apply lift₂_type
@[simp] public theorem type_hpow_type {A: Type u} {B: Type v} : type A ^ type B = type (B -> A) := by
  apply lift₂_type

public instance : NatCast Cardinal where
  natCast := ofNat
public instance : SMul ℕ Cardinal where
  smul n a := n * a
public instance : Pow Cardinal ℕ where
  pow a n := a ^ (fin n)

public theorem natCast_eq (n: ℕ) : n = type (ULift (Fin n)) := by
  apply ulift_type

public instance : IsLawfulNatCast Cardinal where
  natCast_zero := ofNat_zero
  natCast_succ n := by
    rw [natCast_eq, natCast_eq, one_eq, type_add_type]
    apply sound;
    apply Equiv.trans Equiv.ulift
    apply Equiv.trans _ (Equiv.congr_sum Equiv.ulift.symm (Equiv.id _))
    apply Equiv.trans Equiv.fin_succ
    exact {
      toFun
      | .some x => .inl x
      | .none => .inr .unit
      invFun
      | .inl x => .some x
      | .inr _ => .none
      leftInv x := by cases x <;> rfl
      rightInv x := by cases x <;> rfl
    }

public instance : IsAddComm Cardinal where
  add_comm a b := by
    induction a
    induction b
    simp; apply sound
    apply Equiv.sum_comm
public instance : IsAddSemigroup Cardinal where
  add_assoc a b c := by
    induction a
    induction b
    induction c
    simp; apply sound
    apply Equiv.sum_assoc
public instance : IsComm Cardinal where
  mul_comm a b := by
    induction a
    induction b
    simp; apply sound
    apply Equiv.prod_comm
public instance : IsSemigroup Cardinal where
  mul_assoc a b c := by
    induction a
    induction b
    induction c
    simp; apply sound
    apply Equiv.prod_assoc

public instance : IsLeftDistrib Cardinal where
  mul_add k a b := by
    induction k
    induction a
    induction b
    simp; apply sound
    apply Equiv.prod_sum

public instance : IsRightDistrib Cardinal where
  add_mul a b k := by
    iterate 3 rw [mul_comm _ k]
    rw [mul_add]

public instance : IsLawfulZeroMul Cardinal where
  mul_zero a := by
    induction a with | _ a =>
    simp [zero_eq]
    apply sound (Equiv.empty _ _)
  zero_mul a := by
    induction a with | _ a =>
    simp [zero_eq]
    apply sound (Equiv.empty _ _)

public instance : IsLawfulOne Cardinal where
  mul_one a := by
    induction a with | _ a =>
    simp [one_eq]
    exact sound {
      toFun := Prod.fst
      invFun a := (a, default)
      leftInv _ := rfl
      rightInv _ := rfl
    }
  one_mul a := by
    induction a with | _ a =>
    simp [one_eq]
    exact sound {
      toFun := Prod.snd
      invFun a := (default, a)
      leftInv _ := rfl
      rightInv _ := rfl
    }

public instance : IsLawfulZero Cardinal where
  add_zero a := by
    induction a with | _ a =>
    simp [zero_eq]
    exact sound {
      toFun | .inl x => x
      invFun := .inl
      leftInv _ := rfl
      rightInv | .inl _ => rfl
    }
  zero_add a := by
    induction a with | _ a =>
    simp [zero_eq]
    exact sound {
      toFun | .inr x => x
      invFun := .inr
      leftInv _ := rfl
      rightInv | .inr _ => rfl
    }

public instance : IsLawfulNSMul Cardinal where
  zero_nsmul a := by
    show (0: ℕ) * a = 0
    rw [natCast_zero, zero_mul]
  succ_nsmul a n := by
    show (n + 1: ℕ) * a = n * a + a
    rw [natCast_succ, add_mul, one_mul]

public instance : IsLawfulPowN Cardinal where
  pown_zero a := by
    induction a with | _ a =>
    show type a ^ (type _) = _
    simp [one_eq]
    exact sound (Equiv.unique _ _)
  pown_succ a n := by
    induction a with | _ a =>
    show type a ^ type _ = type a ^ type _ * type _
    simp; apply sound
    apply Equiv.trans (Equiv.congr_func _ (Equiv.id _))
    apply Equiv.option_func
    apply Equiv.fin_succ

public instance : IsSemiring Cardinal where

public instance : HasChar Cardinal 0 :=
  HasChar.of_ring_emb (α := ℕ) {
    toEmbedding := ofNat
    map_zero := natCast_zero
    map_one := natCast_one
    map_add := natCast_add
    map_mul := natCast_mul
  }
