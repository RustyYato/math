import LeanMath.Algebra.Field.Defs
import LeanMath.Algebra.Semiring.Char
import LeanMath.Data.Rational.Defs

class RatCast (α: Type*) where
  protected ratCast : ℚ -> α

attribute [simp] RatCast.ratCast

@[coe]
def Rational.cast [RatCast α] : ℚ -> α := RatCast.ratCast

@[coe]
def Rational.Fract.cast [RatCast α] : Fract -> α :=
  Rational.cast ∘ Rational.mk

instance {α} [RatCast α] : Coe ℚ α where
  coe := Rational.cast

instance [RatCast α] : Coe Rational.Fract α where
  coe := Rational.Fract.cast

def defaultRatCast [FieldOps α] [IsField α] [HasChar α 0] (q: ℚ) : α :=
  q.lift (fun q => (q.num: α) /? q.den) <| by
    intro a b h; dsimp
    rw [eq_div_iff_mul_eq, mul_comm, ←mul_div?_assoc]
    symm; rw [eq_div_iff_mul_eq, ←intCast_ofNat, ←intCast_ofNat b.den,
      ←intCast_mul, ←intCast_mul, mul_comm _ a.num, h]

class IsLawfulRatCast (α: Type*) [FieldOps α] [IsField α] [RatCast α] extends HasChar α 0 where
  protected ratCast_def (q: ℚ) : (q: α) = defaultRatCast q

def ratCast_def [FieldOps α] [IsField α] [RatCast α] [IsLawfulRatCast α] (q: ℚ) : (q: α) = defaultRatCast q :=
  IsLawfulRatCast.ratCast_def _

def defaultRatCast_mk [FieldOps α] [IsField α] [RatCast α] [HasChar α 0] (q: Rational.Fract) : defaultRatCast (Rational.mk q) = (q.num: α) /? q.den := by
  unfold defaultRatCast
  rw [Rational.lift_mk]

def ratCast_mk [FieldOps α] [IsField α] [RatCast α] [IsLawfulRatCast α] (q: Rational.Fract) : ((Rational.mk q): α) = (q.num: α) /? q.den := by
  rw [ratCast_def, defaultRatCast_mk]

class IsChar0Field (α: Type*) [FieldOps α] [RatCast α] extends IsField α, IsLawfulRatCast α where

instance : RatCast ℚ where
  ratCast := id

instance : IsChar0Field ℚ where
  ratCast_def q := by
    induction q using Rational.ind with | _ q =>
    simp only [Rational.cast, RatCast.ratCast, id_eq]
    unfold defaultRatCast
    rw [Rational.lift_mk, eq_div_iff_mul_eq]
    simp [←Rational.mk_intCast, ←Rational.mk_natCast, Rational.mk_mul]
    apply Rational.sound; show _ = _; simp

variable [FieldOps α] [RatCast α] [IsChar0Field α]

def ratCast_zero : Rational.cast 0 = (0: α) := by
  rw [ratCast_def]
  simp [defaultRatCast, Rational.mk_zero]
  rw [intCast_zero, div?_eq_mul_inv?, zero_mul]
def ratCast_one : Rational.cast 1 = (1: α) := by
  rw [ratCast_def]
  simp [defaultRatCast, Rational.mk_one]
  symm; rw [intCast_one, eq_div_iff_mul_eq, natCast_one, one_mul]
def ratCast_add (a b: ℚ) : Rational.cast (a + b) = (a + b: α) := by
  induction a with | mk a =>
  induction b with | mk b =>
  simp [ratCast_def, defaultRatCast]
  rw [div?_add_div?]
  congr
  simp [intCast_add, intCast_mul, intCast_ofNat]
  rw [natCast_mul]
def ratCast_mul (a b: ℚ) : Rational.cast (a * b) = (a * b: α) := by
  induction a with | mk a =>
  induction b with | mk b =>
  simp [ratCast_def, defaultRatCast]
  rw [div?_mul_div?]
  congr
  simp [intCast_mul]
  rw [natCast_mul]

def ratCastHom : ℚ →+* α where
  toFun := Rational.cast
  map_zero := ratCast_zero
  map_one := ratCast_one
  map_add := ratCast_add
  map_mul := ratCast_mul

@[simp] def apply_ratCastHom (q: ℚ) : ratCastHom q = (q: α) := rfl

def ratCast_intCast (a: ℤ) : Rational.cast (Int.cast a) = (Int.cast a: α) := by
  show ratCastHom _ = _; rw [map_intCast]
def ratCast_natCast (a: ℕ) : Rational.cast (Nat.cast a) = (Nat.cast a: α) := by
  show ratCastHom _ = _; rw [map_natCast]

def ratCast_ne_zero (q: ℚ) : q ≠ 0 -> (q: α) ≠ 0 := by
  intro h g
  rw [←ratCast_zero] at g
  exact h (inj (ratCastHom (α := α)) g)

macro_rules
| `(tactic|invert_tactic_trivial_low_priority) => `(tactic|apply ratCast_ne_zero <;> invert_tactic)

def ratCast_neg (q: ℚ) : (-q: ℚ) = (-q: α) := by
  rw [←apply_ratCastHom, map_neg]; rfl
def ratCast_sub (a b: ℚ) : (a - b: ℚ) = (a - b: α) := by
  rw [←apply_ratCastHom, map_sub]; rfl
def ratCast_inv? (a: ℚ) (h: a ≠ 0) : (a⁻¹?: ℚ) = (a⁻¹?: α) := by
  rw [←apply_ratCastHom, map_inv?]; rfl
def ratCast_div? (a b: ℚ) (h: b ≠ 0) : (a /? b: ℚ) = (a /? b: α) := by
  rw [←apply_ratCastHom, map_div?]; rfl
def ratCast_npow (a: ℚ) (n: ℕ) : (a ^ n: ℚ) = (a ^ n: α) := by
  rw [←apply_ratCastHom, map_npow]; rfl
def ratCast_zpow (a: ℚ) (n: ℤ) (h: 0 ≤ n ∨ a ≠ 0) : (a ^? n: ℚ) = (a ^? n: α) := by
  rw [←apply_ratCastHom, map_zpow?]; rfl
def ratCast_nsmul (a: ℚ) (n: ℕ) : (n • a: ℚ) = (n • a: α) := by
  rw [←apply_ratCastHom, map_nsmul]; rfl
def ratCast_zsmul (a: ℚ) (n: ℤ) : (n • a: ℚ) = (n • a: α) := by
  rw [←apply_ratCastHom, map_zsmul]; rfl
