module

public import Math.Algebra.Ring.Defs.Basic
public import Math.Algebra.Semiring.Char

import Math.Algebra.Ring.Defs.Lemmas

namespace Math

@[ext]
public structure ZMod (n: ℕ) where
  val: ℤ
  spec: val % n = val

namespace ZMod

instance : Repr (ZMod n) where
  reprPrec a := reprPrec a.val

attribute [coe] ZMod.val
public instance : CoeOut (ZMod n) ℤ where
  coe := ZMod.val

public instance : IntCast (ZMod n) where
  intCast z := {
    val := z % n
    spec := Int.emod_emod _ _
  }

public instance : NatCast (ZMod n) where
  natCast z := (z: ℤ)

public instance : OfNat (ZMod n) k := ⟨k⟩

public instance : One (ZMod n) where
  one := (1: ℤ)
public instance : Mul (ZMod n) where
  mul a b := a.val * b.val

public instance : SMul ℕ (ZMod n) where
  smul a b := (a: ZMod n) * b

public instance : SMul ℤ (ZMod n) where
  smul a b := (a: ZMod n) * b

public instance : AddGroupOps (ZMod n) where
  zero := (0: ℤ)
  neg a := (-a.val: ℤ)
  add a b := a.val + b.val
  sub a b := a.val - b.val
  toNSMul := inferInstance
  toZSMul := inferInstance

@[expose] public def intCastHom : ℤ →+* ZMod n where
  toFun z := z
  map_zero := rfl
  map_one := rfl
  map_add a b := by
    ext; show (a + b) % n = (a % n + b % n) % n
    rw [Int.add_emod]
  map_mul a b := by
    ext; show (a * b) % n = ((a % n) * (b % n)) % n
    rw [Int.mul_emod]

public theorem intCastHom_val (z: ZMod n) : intCastHom z = z := by
  ext; apply z.spec
public theorem intCast_val (z: ZMod n) : ((z: ℤ): ZMod n) = z :=
  intCastHom_val z

public instance : IsLawfulOne (ZMod n) where
  mul_one a := by rw [←intCastHom_val a, ←map_one intCastHom, ←map_mul, mul_one]
  one_mul a := by rw [←intCastHom_val a, ←map_one intCastHom, ←map_mul, one_mul]
public instance : IsSemigroup (ZMod n) where
  mul_assoc a b c := by
    rw [←intCastHom_val a, ←intCastHom_val b, ←intCastHom_val c]
    simp [←map_mul, mul_assoc]
public instance : IsComm (ZMod n) where
  mul_comm a b := by
    rw [←intCastHom_val a, ←intCastHom_val b]
    simp [←map_mul, mul_comm]

public instance : Pow (ZMod n) ℕ :=
  DefaultPowN.instPowNat
instance : IsLawfulPowN (ZMod n) :=
  DefaultPowN.instIsLawfulPowN

public instance : RingOps (ZMod n) where
  toPowN := inferInstance

instance : IsLawfulZeroMul (ZMod n) where
  mul_zero a := by rw [←intCastHom_val a, ←map_zero intCastHom, ←map_mul, mul_zero]
  zero_mul a := by rw [←intCastHom_val a, ←map_zero intCastHom, ←map_mul, zero_mul]
instance : IsLeftDistrib (ZMod n) where
  mul_add k a b := by
    rw [←intCastHom_val a, ←intCastHom_val b, ←intCastHom_val k]
    simp [←mul_add, ←map_mul, ←map_add]
instance : IsRightDistrib (ZMod n) where
  add_mul a b k := by
    rw [←intCastHom_val a, ←intCastHom_val b, ←intCastHom_val k]
    simp [←add_mul, ←map_mul, ←map_add]

instance : IsLawfulNatCast (ZMod n) where
  natCast_zero := map_zero intCastHom
  natCast_succ k := by
    ext; show _ % _ = (_ % _ + _ % _) % _
    simp

instance : IsLawfulIntCast (ZMod n) where
  intCast_ofNat _ := rfl
  intCast_negSucc k := by
    ext; apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    rw [Int.sub_neg, Int.negSucc_eq]
    show _ ∣ -((k + 1: ℕ): ℤ) + (_ % n: ℤ)
    rw [←neg_neg (_ + _), ←neg_add_neg, neg_neg,
      ←sub_eq_add_neg]
    apply Int.dvd_neg.mpr
    exact Int.dvd_self_sub_emod

theorem emod_neg_emod (a: ℤ) (n: ℕ): (-(a % n)) % n = -a % n := by
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  rw [Int.sub_neg, add_comm, ←sub_eq_add_neg,
    Int.sub_emod_emod, sub_self, Int.zero_emod]

public instance : IsRing (ZMod n) where
  add_assoc a b c := by
    rw [←intCastHom_val a, ←intCastHom_val b, ←intCastHom_val c]
    simp [←map_add, add_assoc]
  add_comm a b := by
    rw [←intCastHom_val a, ←intCastHom_val b]
    simp [←map_add, add_comm]
  sub_eq_add_neg a b := by
    ext; show (a - b: ℤ) % n = (a + (-b % n): ℤ) % n
    simp
    rw [sub_eq_add_neg]
  neg_add_cancel a := by
    ext; show ((-a % n) + a: ℤ) % n = 0
    simp [neg_add_cancel]
  add_zero a := by rw [←intCastHom_val a, ←map_zero intCastHom, ←map_add, add_zero]
  zero_add a := by rw [←intCastHom_val a, ←map_zero intCastHom, ←map_add, zero_add]
  zero_nsmul _ := zero_mul _
  succ_nsmul a k := by
    show ((k + 1: ℕ): ZMod n) * a = k * a + a
    rw [natCast_succ, add_mul, one_mul]
  ofNat_zsmul a k := rfl
  negSucc_zsmul a k := by
    show _ * _ = -(_ * _)
    rw [intCast_negSucc]
    ext; show ((((-(_ % n)) % n) * _) % n: ℤ) = (-((_ % n * _) % n) % n: ℤ)
    rw [Int.mul_emod  ((k + 1: ℕ) % _) a,
      Int.emod_emod, ←Int.mul_emod]
    rw [emod_neg_emod, Int.mul_emod, Int.emod_emod, ←Int.mul_emod,
      ←neg_mul_left, emod_neg_emod]

public instance : HasChar (ZMod n) n := by
  apply HasChar.of_natCast_eq_zero
  · ext; apply Int.emod_self
  · intro m hm
    replace hm : m % n = (0 % n: ℤ) := congrArg ZMod.val hm
    rw [Int.zero_emod] at hm
    exact Int.ofNat_dvd.mp (Int.dvd_of_emod_eq_zero hm)
