import LeanMath.Algebra.Semiring.Defs
import LeanMath.Algebra.Monoid.Char
import LeanMath.Logic.Checked

variable [SemiringOps α] [IsSemiring α] [SemiringOps β] [IsSemiring β]

namespace HasChar

def of_natCast_eq_zero (n: ℕ) (h: n = (0: α)) (g: ∀m: ℕ, m = (0: α) -> n ∣ m) : HasChar α n where
  dvd_iff_nsmul_eq_zero c := by
    apply Iff.intro
    rintro ⟨k, rfl⟩ a
    rw [mul_nsmul, nsmul_eq_mul_natCast n, h, mul_zero, nsmul_zero]
    intro g'
    apply g
    rw [natCast_eq_nsmul_one]
    apply g'

def natCast_eq_zero [HasChar α n] : (n: α) = 0 := by
  rw [natCast_eq_nsmul_one, spec]

def dvd_of_natCast_eq_zero [HasChar α n] (m: ℕ) (hm: m = (0: α)) : n ∣ m := by
  apply (dvd_iff_nsmul_eq_zero (α := α) _).mpr
  intro a
  rw [nsmul_eq_mul_natCast, hm, mul_zero]

def dvd_of_ring_hom
  [SemiringOps α] [IsSemiring α] [SemiringOps β] [IsSemiring β]
  [HasChar α n] [HasChar β m]
  (h: α →+* β) : m ∣ n := by
  apply HasChar.char_dvd (α := β)
  intro b
  rw [←one_mul b, nsmul_eq_natCast_mul, ←mul_assoc, ←nsmul_eq_natCast_mul,
  ←map_one h, ←map_nsmul, ←natCast_eq_nsmul_one, natCast_eq_zero, map_zero, zero_mul]

def of_ring_emb [HasChar α n] (f: α ↪+* β) : HasChar β n := by
  apply of_natCast_eq_zero
  rw [←map_natCast f, natCast_eq_zero, map_zero]
  intro m hm
  apply dvd_of_natCast_eq_zero (α := α)
  apply inj f
  rwa [map_natCast f, map_zero]

def of_ring_equiv [HasChar β n] (eqv: α ≃+* β) : HasChar α n := by
  apply of_ring_emb (α := β)
  exact { eqv.symm with inj := inj eqv.symm }

def natCast_inj [IsLeftAddCancel α] [HasChar α 0]: Function.Injective (fun n: ℕ => (n: α)) := by
  suffices ∀n m: ℕ, (n: α) = m -> n ≤ m -> n = m by
    intro n m eq
    rcases Nat.le_total n m with h | h
    apply this
    assumption
    assumption
    symm; apply this
    symm; assumption
    assumption
  intro n m h le
  have : (m - n: ℕ) + (n: α) = 0 + m := by
    rw [←natCast_add, Nat.sub_add_cancel le, zero_add]
  rw [h] at this
  replace this := Nat.le_of_sub_eq_zero
    <| Nat.zero_dvd.mp <| dvd_of_natCast_eq_zero _
    <| of_add_right this
  apply Nat.le_antisymm <;> assumption

end HasChar

def natCast_ne_zero [IsLeftAddCancel α] [HasChar α 0] (n: ℕ) (h: n ≠ 0) : (n: α) ≠ 0 := by
  intro g
  rw [←natCast_zero] at g
  exact h (HasChar.natCast_inj g)

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply natCast_ne_zero <;> invert_tactic)
