import LeanMath.Algebra.Group.Free

inductive Rel (n: ℕ) : FreeGroup Unit -> FreeGroup Unit -> Prop where
| intro (g: FreeGroup Unit) : Rel n (g ^ n) 1

-- the cyclic group of order n
def CyclicGroup (n: ℕ) := GroupQuot (Rel n)

namespace CyclicGroup

def ι : CyclicGroup n := GroupQuot.mk _ (FreeGroup.ι ())

instance : One (CyclicGroup n) := inferInstanceAs (One (GroupQuot _))
instance : Mul (CyclicGroup n) := inferInstanceAs (Mul (GroupQuot _))
instance : Inv (CyclicGroup n) := inferInstanceAs (Inv (GroupQuot _))
instance : Div (CyclicGroup n) := inferInstanceAs (Div (GroupQuot _))
instance : Pow (CyclicGroup n) ℕ := inferInstanceAs (Pow (GroupQuot _) ℕ)
instance : Pow (CyclicGroup n) ℤ := inferInstanceAs (Pow (GroupQuot _) ℤ)

instance : IsComm (CyclicGroup n) := inferInstanceAs (IsComm (GroupQuot _))
instance : IsGroup (CyclicGroup n) := inferInstanceAs (IsGroup (GroupQuot _))

def pown_eq_one (x: CyclicGroup n) : x ^ n = 1 := by
  induction x using GroupQuot.ind with | mk x =>
  induction x with
  | one => simp [map_one, one_npow]
  | inv x ih =>
    simp [map_inv]
    rw [←one_inv, ←ih]
    apply eq_inv_of_mul
    rw [←mul_npow, inv_mul_cancel, one_npow]
  | mul a b iha ihb =>
    rw [map_mul, mul_npow, iha, ihb, mul_one]
  | ι x =>
    apply GroupQuot.sound
    apply Rel.intro

end CyclicGroup
