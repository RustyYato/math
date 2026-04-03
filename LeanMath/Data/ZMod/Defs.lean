import LeanMath.Tactic.TypeStar

@[ext]
structure ZMod (n: ℕ) where
  val: ℤ
  mod_eq_self: val % n = val := by exact Int.emod_emod _ _

instance : Zero (ZMod n) where
  zero := {
    val := 0
    mod_eq_self := by rw [Int.zero_emod]
  }

instance : One (ZMod n) where
  one := {
    val := match n with
      | 1 => 0
      | 0 | n + 2 => 1
    mod_eq_self := by
      match n with | 1 | 0 | n + 2 => rfl
  }

instance : NatCast (ZMod n) where
  natCast x := { val := x % n }

instance : IntCast (ZMod n) where
  intCast x := { val := x % n }

instance : Add (ZMod n) where
  add a b := { val := (a.val + b.val) % n }

instance : Mul (ZMod n) where
  mul a b := { val := (a.val * b.val) % n }

instance : Neg (ZMod n) where
  neg a := { val := (-a.val) % n }

instance : Sub (ZMod n) where
  sub a b := { val := (a.val - b.val) % n }

instance : SMul ℕ (ZMod n) where
  smul a b := { val := (a * b.val) % n }

instance : SMul ℤ (ZMod n) where
  smul a b := { val := (a * b.val) % n }

instance : Pow (ZMod n) ℕ where
  pow a b := { val := (a.val ^ b) % n }

namespace ZMod

variable {n: ℕ}

@[simp] def zero_val : (0: ZMod n).val = 0 := rfl
@[simp] def one_val : (1: ZMod n).val = 1 % n :=
  match n with | 1 | 0 | _ + 2 => rfl
@[simp] def natCast_val (x: ℕ) : (x: ZMod n).val = x % n := rfl
@[simp] def intCast_val (x: ℤ) : (x: ZMod n).val = x % n := rfl
@[simp] def add_val (a b: ZMod n) : (a + b).val = (a.val + b.val) % n := rfl
@[simp] def mul_val (a b: ZMod n) : (a * b).val = (a.val * b.val) % n := rfl
@[simp] def neg_val (a: ZMod n) : (-a).val = (-a.val) % n := rfl
@[simp] def sub_val (a b: ZMod n) : (a - b).val = (a.val - b.val) % n := rfl
@[simp] def nsmul_val (a: ℕ) (b: ZMod n) : (a • b).val = (a * b.val) % n := rfl
@[simp] def zsmul_val (a: ℤ) (b: ZMod n) : (a • b).val = (a * b.val) % n := rfl
@[simp] def npow_val (a: ℕ) (b: ZMod n) : (b ^ a).val = (b.val ^ a) % n := rfl

@[simp] def val_inj {a b: ZMod n} : a.val = b.val ↔ a = b := by
  apply Iff.intro
  intro h; cases a;cases b; cases h; rfl
  apply ZMod.mk.inj

def intCast_eq_emod (m: ℤ) (n: ℕ) : (m: ZMod n) = (m % n: ℤ) := by
  apply ZMod.val_inj.mp
  dsimp; rw [Int.emod_emod]

def natCast_eq_mod (m n: ℕ) : (m: ZMod n) = (m % n: ℕ) := by
  apply intCast_eq_emod

def natCast_degree (n: ℕ) : (n: ZMod n) = 0 := by
  rw [natCast_eq_mod, Nat.mod_self]; rfl

def exists_intCast (x: ZMod n) : ∃y: ℤ, x = y := by
  exists x.val
  apply ZMod.val_inj.mp
  exact x.mod_eq_self.symm

def nsmul_eq_natCast_mul (m: ℕ) (x: ZMod n) : m • x = m * x := by
  apply ZMod.val_inj.mp
  simp
  rw [Int.mul_emod, x.mod_eq_self]

end ZMod
