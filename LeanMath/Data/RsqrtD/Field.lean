import LeanMath.Data.RsqrtD.Ring
import LeanMath.Algebra.Field.Defs
import LeanMath.Algebra.Group.Action.Defs

namespace RsqrtD

variable {r: R}

class NoSolution (α: Type*) [SemiringOps R] [SemiringOps α] [AlgebraMap R α] (r: R) where
  protected sq_ne_r (a: α) : a ^ 2 ≠ algebraMap R r

variable [FieldOps α] [IsField α] [RingOps R] [IsRing R] [AlgebraMap R α] [SMul R α] [IsAlgebra R α]
   [NoSolution α r] [ExcludedMiddleEq α]

def eq_zero_of_mul_conj_eq_zero (a: RsqrtD α r) : a * conj a = 0 -> a = 0 := by
  intro h
  replace ⟨h, g⟩ := mk.inj h
  simp [←neg_mul_right] at h g
  rw [add_comm, ←sub_eq_add_neg, ←sub_eq_zero] at g
  rw [←neg_smul_right, ←sub_eq_add_neg, ←sub_eq_zero,
    smul_def] at h
  rcases em (a.imag * a.imag = 0) with hi | hi
  rw [hi, mul_zero] at h
  have : a.imag = 0 := by cases of_mul_eq_zero hi <;> assumption
  have : a.real = 0 := by cases of_mul_eq_zero h <;> assumption
  ext <;> assumption
  replace h : (a.real /? a.imag) ^ 2 = algebraMap R r := by
    rw [
      npow_succ, npow_one,
      div?_eq_mul_inv?,
      mul_assoc, mul_left_comm (a.imag⁻¹?),
      ←mul_assoc, h, ←inv?_mul_rev, mul_assoc, mul_inv?_cancel, mul_one]
    assumption
  nomatch NoSolution.sq_ne_r _ h

def mul_conj_imag_eq_zero (a: RsqrtD α r) : (a * conj a).imag = 0 := by
  simp
  rw [←neg_mul_right, mul_comm, neg_add_cancel]

def mul_conj_real_ne_zero_of_ne_zero (a: RsqrtD α r) : a ≠ 0 -> (a * conj a).real ≠ 0 := by
  intro h g;
  have := h (eq_zero_of_mul_conj_eq_zero a ?_)
  contradiction
  ext; assumption
  apply mul_conj_imag_eq_zero

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply mul_conj_real_ne_zero_of_ne_zero <;> invert_tactic)

instance : CheckedInv? (RsqrtD α r) where
  checked_inv a h :=
    let d := (a * conj a).real
    {
      real := a.real /? d
      imag := -a.imag /? d
    }

@[simp] def inv?_real (a: RsqrtD α r) (ha: a ≠ 0) : a⁻¹?.real = a.real /? (a * conj a).real := rfl
@[simp] def inv?_imag (a: RsqrtD α r) (ha: a ≠ 0) : a⁻¹?.imag = -a.imag /? (a * conj a).real := rfl

instance : CheckedDiv? (RsqrtD α r) where
  checked_div a b h := a * b⁻¹?

instance : CheckedZPow? (RsqrtD α r) where
  checked_pow a b h :=
    match b with
    | .ofNat n => a ^ n
    | .negSucc n => a⁻¹? ^ (n + 1)

instance : IsGroupWithZero (RsqrtD α r) where
  zero_ne_one := by
    intro h
    exact zero_ne_one _ (mk.inj h).left
  mul_inv?_cancel := by
    intro a h
    ext <;> simp
    rw [div?_eq_mul_inv? (-a.imag), ←mul_assoc,
      div?_eq_mul_inv? a.real, ←mul_assoc]
    rw [smul_def r (_ * _ * _), ←mul_assoc, ←smul_def,
    ←add_mul, mul_inv?_cancel]
    rw [div?_eq_mul_inv? (-a.imag), ←mul_assoc,
      div?_eq_mul_inv? a.real, ←mul_assoc,
    ←add_mul, ←neg_mul_right, mul_comm a.real, neg_add_cancel,
      zero_mul]
  div?_eq_mul_inv? _ _ _ := rfl
  zpow?_ofNat _ _ := rfl
  zpow?_negSucc _ _ _ := rfl

instance : ExcludedMiddleEq (RsqrtD α r) := by
  intro a b
  have ⟨_⟩ : Nonempty (Decidable (a.real = b.real)) := inferInstance
  have ⟨_⟩ : Nonempty (Decidable (a.imag = b.imag)) := inferInstance
  have : Decidable ( a.real = b.real ∧ a.imag = b.imag ) := inferInstance
  have : Decidable (a = b) := decidable_of_iff (a.real = b.real ∧ a.imag = b.imag) ?_
  infer_instance
  apply Iff.intro
  intro ⟨_, _⟩
  ext <;> assumption
  intro h
  have ⟨_, _⟩ := mk.inj h
  apply And.intro <;> assumption

instance : FieldOps (RsqrtD α r) := inferInstance
instance : IsField (RsqrtD α r) where

end RsqrtD
