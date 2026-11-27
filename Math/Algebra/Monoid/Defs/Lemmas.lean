module

public import Math.Algebra.Monoid.Defs.Basic
import Math.Algebra.Monoid.Defs.Hom

namespace Math

public theorem subingleton_of_zero_eq_one (α: Type*) [Zero α] [One α] [Mul α] [IsLawfulZeroMul α] [IsLawfulOne α] (h: (0: α) = (1: α)) : Subsingleton α where
  allEq a b := by
    rw [←one_mul a, ←one_mul b, ←h, zero_mul, zero_mul]

public instance
  (priority := 100)
  [Nontrivial α] [Zero α] [One α] [Mul α]
  [IsLawfulOne α] [IsLawfulZeroMul α]
  [∀a: α, ExcludedMiddle (1 = a)] : IsZeroNeOne α where
  zero_ne_one := by
    intro h
    have ⟨b, g⟩ := Nontrivial.exists_ne (1: α)
    rw [←mul_one b, ←h, mul_zero] at g
    contradiction

public instance [Zero α] [One α] [IsZeroNeOne α] : Nontrivial α := .intro 0 1 zero_ne_one

public theorem smul_eq_mul [Mul α] (a b: α) : a • b = a * b := rfl

public instance [MonoidOps α] [IsMonoid α] (a b: α) [IsCommAt a b] (n: ℕ) : IsCommAt a (b ^ n) where
  mul_comm := by
    induction n with
    | zero => rw [pown_zero, mul_one, one_mul]
    | succ n ih => rw [pown_succ, ←mul_assoc, ih, mul_assoc, mul_assoc, mul_comm a]

public instance [AddMonoidOps α] [IsAddMonoid α] (a b: α) [IsAddCommAt a b] (n: ℕ) : IsAddCommAt a (n • b) where
  add_comm := mul_comm (MulOfAdd.mk a) (MulOfAdd.mk b ^ n)

public theorem pown_succ_left [MonoidOps α] [IsMonoid α] (a: α) (n: ℕ) : a ^ (n + 1) = a * a ^ n := by
  rw [mul_comm a, pown_succ]

public theorem succ_nsmul_left [AddMonoidOps α] [IsAddMonoid α] (a: α) (n: ℕ) : (n + 1) • a = a + n • a :=
  pown_succ_left (α := MulOfAdd α) a n

public theorem mul_nsmul [AddMonoidOps α] [IsAddMonoid α] (a: α) (n m: ℕ) : (n * m) • a = n • m • a := by
  rw [←smul_eq_mul n m]
  show nsmul_hom a (n • m) = n • nsmul_hom a m
  rw [map_nsmul]

public theorem pown_mul [MonoidOps α] [IsMonoid α] (a: α) (n m: ℕ) : a ^ (n * m) = (a ^ m) ^ n :=
  mul_nsmul (α := AddOfMul α) a n m

public theorem add_nsmul [AddMonoidOps α] [IsAddMonoid α] (a: α) (n m: ℕ) : (n + m) • a = n • a + m • a :=
  map_add (nsmul_hom a) _ _

public theorem pown_add [MonoidOps α] [IsMonoid α] (a: α) (n m: ℕ) : a ^ (n + m) = a ^ n * a ^ m :=
  add_nsmul (α := AddOfMul α) a n m

public theorem nsmul_add [AddMonoidOps α] [IsAddMonoid α] (a b: α) [IsAddCommAt a b] (n: ℕ) : n • (a + b) = n • a + n • b := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, zero_nsmul, add_zero]
  | succ n ih =>
    iterate 3 rw [succ_nsmul]
    rw [ih, add_assoc, ←add_assoc _ a, add_comm _ a, add_assoc a, ←add_assoc _ a]

public theorem mul_pown [MonoidOps α] [IsMonoid α] (a b: α) [IsCommAt a b] (n: ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
  nsmul_add (α := AddOfMul α) (AddOfMul.mk a) (AddOfMul.mk b) n

public theorem nsmul_zero [AddMonoidOps α] [IsAddMonoid α] (n: ℕ) : n • (0: α) = 0 := by
  induction n with
  | zero => rw [zero_nsmul]
  | succ n ih => rw [succ_nsmul, add_zero, ih]
public theorem one_pown [MonoidOps α] [IsMonoid α] (n: ℕ) : (1: α) ^ n = 1 :=
  nsmul_zero (α := AddOfMul α) n

public theorem one_nsmul [AddMonoidOps α] [IsAddMonoid α] (a: α) : 1 • a = a := by
  rw [succ_nsmul, zero_nsmul, zero_add]
public theorem pown_one [MonoidOps α] [IsMonoid α] (a: α) : a ^ 1 = a :=
  one_nsmul (α := AddOfMul α) a
public theorem two_nsmul [AddMonoidOps α] [IsAddMonoid α] (a: α) : 2 • a = a + a := by
  rw [succ_nsmul, one_nsmul]
public theorem pown_two [MonoidOps α] [IsMonoid α] (a: α) : a ^ 2 = a * a :=
  two_nsmul (α := AddOfMul α) _

public instance : IsZeroNeOne ℕ := inferInstance
public instance : IsZeroNeOne ℤ := inferInstance

public theorem sub_nsmul_add [AddMonoidOps α] [IsAddMonoid α] (a: α) (n m: ℕ) (h: m ≤ n) : (n - m) • a + m • a = n • a := by
  induction m generalizing n with
  | zero => rw [Nat.sub_zero, zero_nsmul, add_zero]
  | succ m ih =>
    cases n with
    | zero => nomatch h
    | succ n =>
      replace h := Nat.le_of_succ_le_succ h
      rw [Nat.succ_sub_succ, succ_nsmul, ←add_assoc, ih _ h, succ_nsmul]
public theorem pown_sub_mul [MonoidOps α] [IsMonoid α] (a: α) (n m: ℕ) (h: m ≤ n) : a ^ (n - m) * a ^ m = a ^ n :=
  sub_nsmul_add (α := AddOfMul α) _ _ _ h
