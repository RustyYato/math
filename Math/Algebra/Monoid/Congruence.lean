module

public import Math.Algebra.Semigroup.Congruence
public import Math.Algebra.Monoid.Defs.Basic

namespace Math

variable [RelLike C α] [IsCon C α]

public theorem resp_pown [MonoidOps α] [IsLawfulPowN α] [IsMulCon C α] (r: C) (a b: α) (n: ℕ) :
  r a b -> r (a ^ n) (b ^ n) := by
  intro h; induction n with
  | zero => rw [pown_zero, pown_zero]; apply refl
  | succ n ih =>
    rw [pown_succ, pown_succ]; apply resp_mul
    assumption
    assumption

public theorem resp_nsmul [AddMonoidOps α] [IsLawfulNSMul α] [IsAddCon C α] (r: C) (n: ℕ) (a b: α) :
  r a b -> r (n • a) (n • b) := resp_pown (MulOfAdd.mk r) (MulOfAdd.mk a) (MulOfAdd.mk b) n

public instance [MonoidOps α] [IsLawfulPowN α] [IsMulCon C α] (r: C) : Pow (AlgQuot r) ℕ where
  pow q n := q.lift (fun a => AlgQuot.mk r (a ^ n)) <| by
    intro a b h; apply AlgQuot.sound
    apply resp_pown
    assumption

public instance [AddMonoidOps α] [IsLawfulNSMul α] [IsAddCon C α] : IsSMulCon C ℕ α where
  resp_smul := resp_nsmul

public instance [MonoidOps α] [IsLawfulPowN α] [IsMulCon C α] (r: C) : IsLawfulPowN (AlgQuot r) where
  pown_zero a := by
    induction a with | _ a =>
    show AlgQuot.mk _ (a ^ 0) = AlgQuot.mk _ 1
    rw [pown_zero]
  pown_succ a n := by
    induction a with | _ a =>
    show AlgQuot.mk _ (a ^ (n + 1)) = AlgQuot.mk _ (a ^ n * a)
    rw [pown_succ]

public instance [AddMonoidOps α] [IsLawfulNSMul α] [IsAddCon C α] (r: C) : IsLawfulNSMul (AlgQuot r) where
  zero_nsmul a := by
    induction a with | _ a =>
    show AlgQuot.mk _ (0 • a) = AlgQuot.mk _ 0
    rw [zero_nsmul]
  succ_nsmul a n := by
    induction a with | _ a =>
    show AlgQuot.mk _ ((n + 1) • a) = AlgQuot.mk _ (n • a + a)
    rw [succ_nsmul]

public instance [MonoidOps α] [IsMonoid α] [IsMulCon C α] (r: C) : IsMonoid (AlgQuot r) where
  mul_one a := by induction a with | _ a => show AlgQuot.mk _ (a * 1) = _; rw [mul_one]
  one_mul a := by induction a with | _ a => show AlgQuot.mk _ (1 * a) = _; rw [one_mul]

public instance [AddMonoidOps α] [IsAddMonoid α] [IsAddCon C α] (r: C) : IsAddMonoid (AlgQuot r) where
  zero_add a := by induction a with | _ a => show AlgQuot.mk _ (0 + a) = _; rw [zero_add]
  add_zero a := by induction a with | _ a => show AlgQuot.mk _ (a + 0) = _; rw [add_zero]
