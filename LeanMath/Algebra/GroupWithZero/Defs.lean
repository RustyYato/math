import LeanMath.Algebra.Group.Defs
import LeanMath.Algebra.MonoidWithZero.Defs
import LeanMath.Logic.Checked
import LeanMath.Logic.Nontrivial

class GroupWithZeroOps (α: Type*) extends
  MonoidOps α, Zero α, CheckedInv? α, CheckedDiv? α, CheckedZPow? α where

instance (priority := 1100)
  [MonoidOps α] [Zero α] [CheckedInv? α] [CheckedDiv? α] [CheckedZPow? α]
  : GroupWithZeroOps α where

def defaultPowZ? [Zero α] [Pow α ℕ] [CheckedInv? α] : CheckedZPow? α where
  checked_pow
  | a, .ofNat n, _ => a ^ n
  | a, .negSucc n, h => a⁻¹? ^ (n + 1)

def defaultDiv? [Zero α] [Mul α] [CheckedInv? α] : CheckedDiv? α where
  checked_div a b h := a * b⁻¹?

class IsLawfulDiv? (α: Type*) [Zero α] [Mul α] [CheckedInv? α] [CheckedDiv? α] where
  protected div?_eq_mul_inv? (a b: α) (h: b ≠ 0) : a /? b = a * b⁻¹?

def div?_eq_mul_inv? [Zero α] [Mul α] [CheckedInv? α] [CheckedDiv? α] [IsLawfulDiv? α] (a b: α) (h: b ≠ 0) : a /? b = a * b⁻¹? :=
  IsLawfulDiv?.div?_eq_mul_inv? _ _ _

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply zero_ne_one)
macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|symm; apply zero_ne_one)

class IsLawfulOneInv? (α: Type*) [Zero α] [One α] [CheckedInv? α] : Prop extends IsZeroNeOne α where
  protected one_inv? : (1: α)⁻¹? = 1

def one_inv? [Zero α] [One α] [CheckedInv? α] [IsLawfulOneInv? α] : (1: α)⁻¹? = 1 :=
  IsLawfulOneInv?.one_inv?

class IsLawfulZPow? (α: Type*) [Zero α] [Pow α ℕ] [CheckedZPow? α] [CheckedInv? α] : Prop where
  protected zpow?_ofNat (a: α) (n: ℕ) : a ^? (n: ℤ) = a ^ n
  protected zpow?_negSucc (a: α) (n: ℕ) (h: a ≠ 0) : a ^? (Int.negSucc n) = a⁻¹? ^ (n + 1)

section

variable [Zero α] [Pow α ℕ] [CheckedZPow? α] [CheckedInv? α] [IsLawfulZPow? α]

def zpow?_ofNat  (a: α) (n: ℕ) : a ^? (n: ℤ) = a ^ n := IsLawfulZPow?.zpow?_ofNat _ _
def zpow?_negSucc  (a: α) (n: ℕ) (h: a ≠ 0) : a ^? (Int.negSucc n) = a⁻¹? ^ (n + 1) :=
  IsLawfulZPow?.zpow?_negSucc _ _ _

end

class IsGroupWithZero (α: Type*) [GroupWithZeroOps α] : Prop
  extends IsMonoidWithZero α, IsLawfulDiv? α, IsLawfulZPow? α, IsZeroNeOne α where
  protected mul_inv?_cancel (a: α) (h: a ≠ 0) : a * a⁻¹? = 1

variable [GroupWithZeroOps α] [IsGroupWithZero α]
   [GroupWithZeroOps β] [IsGroupWithZero β]

def mul_inv?_cancel (a: α) (h: a ≠ 0) : a * a⁻¹? = 1 :=
  IsGroupWithZero.mul_inv?_cancel _ _

def of_mul_ne_zero {a b: α} (h: a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 := by
  apply And.intro
  · intro rfl
    rw [zero_mul] at h
    contradiction
  · intro rfl
    rw [mul_zero] at h
    contradiction

macro_rules
| `(tactic|invert_tactic_trivial_low_priority) => `(tactic|first|apply (of_mul_ne_zero (by assumption)).left|apply (of_mul_ne_zero (by assumption)).right)

instance [DecidableEq α] : NoZeroDivisors α where
  of_mul_eq_zero {a b} h := by
    apply Decidable.or_iff_not_imp_right.mpr
    intro g
    have : (a * b) * b⁻¹? = 0 := by rw [h, zero_mul]
    rw [mul_assoc, mul_inv?_cancel, mul_one] at this
    assumption

variable [NoZeroDivisors α]

def mul_ne_zero {a b: α} (ha: a ≠ 0) (hb: b ≠ 0) : a * b ≠ 0 := by
  intro g
  cases of_mul_eq_zero g <;> contradiction

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|first|apply mul_ne_zero <;> invert_tactic)

def inv_ne_zero {a: α} (h: a ≠ 0) : a⁻¹? ≠ 0 := by
  intro g
  have : a * a⁻¹? = 0 := by rw [g, mul_zero]
  rw [mul_inv?_cancel] at this
  contradiction

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|first|apply mul_ne_zero <;> invert_tactic)

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|first|apply inv_ne_zero <;> invert_tactic)

def inv?_mul_cancel (a: α) (h: a ≠ 0) : a⁻¹? * a = 1 := by
  rw (occs := [2]) [←mul_one a]
  rw (occs := [1]) [←mul_inv?_cancel (a⁻¹?)]
  rw [←mul_assoc a, mul_inv?_cancel, one_mul, mul_inv?_cancel]
  apply inv_ne_zero

def Units.of_nonzero [GroupWithZeroOps α] [IsGroupWithZero α] : { a: α // a ≠ 0 } ↪ Units α where
  toFun | ⟨a, ha⟩ => {
    val := a
    inv := a⁻¹?
    val_mul_inv := mul_inv?_cancel _ _
    inv_mul_val := inv?_mul_cancel _ _
  }
  inj := by
    intro a b h
    dsimp at h
    have := (Units.mk.inj h).left
    apply Embedding.subtype_val.inj
    assumption

instance [GroupWithZeroOps α] [IsGroupWithZero α] (a: α) [NeZero a] : IsUnit a where
  exists_eq_unit := ⟨Units.of_nonzero ⟨a, NeZero.ne _⟩, rfl⟩

def div?_ne_zero {a b: α} (ha: a ≠ 0) (hb: b ≠ 0) : a /? b ≠ 0 := by
  rw [div?_eq_mul_inv?]
  invert_tactic

def npow_ne_zero {a: α} {n: ℕ} (ha: a ≠ 0) : a ^ n ≠ 0 := by
  induction n with
  | zero =>
    rw [npow_zero]
    invert_tactic
  | succ n =>
    rw [npow_succ]
    apply mul_ne_zero
    assumption
    assumption

def zpow?_ne_zero {a: α} {n: ℤ} (ha: a ≠ 0) : a ^? n ≠ 0 := by
  cases n with
  | ofNat n =>
    rw [zpow?_ofNat]
    apply npow_ne_zero
    assumption
  | negSucc n =>
    rw [zpow?_negSucc]
    apply npow_ne_zero
    invert_tactic
    invert_tactic

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|first|apply div?_ne_zero <;> invert_tactic)

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|first|apply npow_ne_zero <;> invert_tactic)

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|first|apply zpow?_ne_zero <;> invert_tactic)

def eq_inv?_of_mul (a b: α) (h: a * b = 1) : a = b⁻¹?~(by
  intro g; rw [g, mul_zero] at h
  contradiction) := by
  have : b ≠ 0 := by
    intro g; rw [g, mul_zero] at h
    contradiction
  rw [←one_mul (b⁻¹?), ←h, mul_assoc, mul_inv?_cancel, mul_one]

instance : IsLawfulOneInv? α where
  one_inv? := by
    symm; apply eq_inv?_of_mul
    rw [mul_one]

def div?_self (a: α) (h: a ≠ 0) : a /? a = 1 := by
  rw [div?_eq_mul_inv?, mul_inv?_cancel]

variable
  [EmbeddingLike F α β] [IsMulHom F α β] [IsOneHom F α β] [IsZeroHom F α β]

def map_ne_zero (f: F) (x: α) (h: x ≠ 0) : f x ≠ 0 := by
  rw [←map_zero f]
  intro g; exact h (inj f g)

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply map_ne_zero; invert_tactic)

def map_ne_zero' (f: F) (n: ℤ) (x: α) (h: 0 ≤ n ∨ x ≠ 0) : 0 ≤ n ∨ f x ≠ 0 := by
  pow_tactic_from_invert

def map_inv? (f: F) (x: α) (h: x ≠ 0) : f (x⁻¹?) = (f x)⁻¹? := by
  apply eq_inv?_of_mul
  rw [←map_mul, inv?_mul_cancel, map_one]

def map_div? (f: F) (a b: α) (h: b ≠ 0) : f (a /? b) = f a /? f b := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, map_mul, map_inv?]

def map_zpow? (f: F) (a: α) (z: ℤ) (h: 0 ≤ z ∨ a ≠ 0) : f (a ^? z) = f a ^? z := by
  cases z <;> rename_i z
  rw [zpow?_ofNat, zpow?_ofNat, map_npow]
  rw [zpow?_negSucc, zpow?_negSucc, map_npow, map_inv?]
  invert_tactic

variable [RelLike R α] [IsMulCon R] (r: R)

def resp_inv? (r: R) (a b: α) (ha: a ≠ 0) (hb: b ≠ 0) : r a b -> r a⁻¹? b⁻¹? := by
  intro h
  have raa : r a⁻¹? a⁻¹? := (IsCon.eqv _).refl _
  have rbb : r b⁻¹? b⁻¹? := (IsCon.eqv _).refl _
  have := resp_mul r (resp_mul r raa h) rbb
  rw [inv?_mul_cancel a, mul_assoc, mul_inv?_cancel, mul_one, one_mul] at this
  apply (IsCon.eqv _).symm
  assumption

def resp_div? (r: R) (a b c d: α) (hb: b ≠ 0) (hd: d ≠ 0) : r a c -> r b d -> r (a /? b) (c /? d) := by
  intro h g
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?]
  apply resp_mul
  assumption
  apply resp_inv?
  assumption

def resp_zpow? (r: R) (z: ℤ) (a b: α) (ha: 0 ≤ z ∨ a ≠ 0) (hb: 0 ≤ z ∨ b ≠ 0) : r a b  -> r (a ^? z) (b ^? z) := by
  intro h
  cases z <;> rename_i z
  rw [zpow?_ofNat, zpow?_ofNat]
  apply resp_npow
  assumption
  rw [zpow?_negSucc, zpow?_negSucc]
  apply resp_npow
  apply resp_inv?
  assumption
  invert_tactic
  invert_tactic

instance : IsLeftCancel₀ α where
  of_mul_left₀ {k a b: α} hk h := by
    rw [←one_mul a, ←one_mul b, ←inv?_mul_cancel k,
      mul_assoc, mul_assoc, h]
    assumption

instance : IsRightCancel₀ α where
  of_mul_right₀ {k a b: α} hk h := by
    rw [←mul_one a, ←mul_one b, ←mul_inv?_cancel k,
      ←mul_assoc, ←mul_assoc, h]
    assumption

instance (a b: α) (h: a ≠ 0) [IsCommAt a b] : IsCommAt a⁻¹? b where
  mul_comm := by
    apply of_mul_left₀ (k := a)
    assumption
    rw [←mul_assoc, ←mul_assoc, mul_inv?_cancel, one_mul,
      mul_comm a, mul_assoc, mul_inv?_cancel, mul_one]

instance (a b: α) (h: a ≠ 0) [IsCommAt a b] : IsCommAt b a⁻¹? := inferInstance

def inv?_mul_rev (a b: α) (h: a * b ≠ 0) : (a * b)⁻¹? = b⁻¹? * a⁻¹? := by
  symm; apply eq_inv?_of_mul
  rw [mul_assoc, ←mul_assoc _ a, inv?_mul_cancel, one_mul, inv?_mul_cancel]

def inv?_inv? (a: α) (h: a ≠ 0) : a⁻¹?⁻¹? = a := by
  symm; apply eq_inv?_of_mul
  rw [mul_inv?_cancel]

def inv?_div? (a b: α) (ha: a ≠ 0) (hb: b ≠ 0) : (a /? b)⁻¹? = b /? a := by
  symm; apply eq_inv?_of_mul
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, ←mul_assoc,
    mul_assoc b, inv?_mul_cancel, mul_one, mul_inv?_cancel]

def mul_div?_assoc (a b c: α) (h: c ≠ 0) : (a * b) /? c = a * (b /? c) := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, mul_assoc]

def div?_mul (a b c: α) (h: b * c ≠ 0) : a /? (b * c) = a /? c /? b := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, div?_eq_mul_inv?,
    inv?_mul_rev, mul_assoc]

def div?_div? (a b c: α) (hb: b ≠ 0) (hc: c ≠ 0) : a /? c /? b = a /? (b * c) := by
  rw [div?_mul]

def mul_div?_comm (a b c: α) [IsCommAt b c] (h: b ≠ 0) : a * c /? b = a /? b * c := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?,
    mul_assoc, mul_assoc, mul_comm _ c]

def div?_mul_cancel (a b: α) (h: b ≠ 0) : a /? b * b = a := by
  rw [div?_eq_mul_inv?, mul_assoc, inv?_mul_cancel, mul_one]

def div?_one (a: α) : a /? 1 = a := by
  rw [div?_eq_mul_inv?, one_inv?, mul_one]

def one_zpow? (z: ℤ) : (1: α) ^? z = 1 := by
  cases z
  rw [zpow?_ofNat, one_npow]
  rw [zpow?_negSucc, one_inv?, one_npow]
  invert_tactic

def inv?_npow (a: α) (n: ℕ) (h: a ≠ 0) : (a⁻¹?) ^ n = (a ^ n)⁻¹? := by
  apply eq_inv?_of_mul
  rw [←mul_npow, inv?_mul_cancel, one_npow]

def mul_zpow? (a b: α) (z: ℤ) (h: 0 ≤ z ∨ a * b ≠ 0) [IsCommAt a b] : (a * b) ^? z = a ^? z * b ^? z := by
  cases z
  iterate 3 rw [zpow?_ofNat]
  rw [mul_npow]
  iterate 3 rw [zpow?_negSucc, inv?_npow]
  rw [←inv?_mul_rev]; congr
  rw [←mul_npow, mul_comm]
  all_goals
    cases h; contradiction
    invert_tactic

def zpow?_zero (a: α) : a ^? 0 = 1 := by
  apply Eq.trans
  apply zpow?_ofNat
  rw [npow_zero]

def zpow?_one (a: α) : a ^? 1 = a := by
  apply Eq.trans
  apply zpow?_ofNat
  rw [npow_one]

def zpow?_neg_one (a: α) (h: a ≠ 0) : a ^? (-1) = a⁻¹? := by
  apply Eq.trans
  apply zpow?_negSucc
  assumption
  rw [npow_one]

def inv?_zpow? (a: α) (n: ℤ) (h: a ≠ 0) : a⁻¹? ^? n = a ^? (-n) := by
  cases n <;> rename_i n
  rw [zpow?_ofNat]
  cases n
  rw [npow_zero, Int.ofNat_zero, Int.neg_zero, zpow?_zero]
  erw [←Int.negSucc_eq]
  rw [zpow?_negSucc]
  cases n; simp
  rw [zpow?_neg_one, inv?_inv?, zpow?_one]
  invert_tactic; simp
  rw [zpow?_negSucc, inv?_inv?]
  show _ = a ^? (Nat.cast (_ + 1 + 1))
  rw [zpow?_ofNat]
  invert_tactic

def zpow?_succ (a: α) (n: ℤ) (h: a ≠ 0) : a ^? (n + 1) = a ^? n * a := by
  cases n
  erw [Int.ofNat_add_ofNat]; rw [zpow?_ofNat, zpow?_ofNat, npow_succ]
  rename_i n
  cases n
  simp; rw [zpow?_zero, zpow?_neg_one]
  rw [inv?_mul_cancel]
  assumption
  erw [Int.negSucc_add_ofNat, zpow?_negSucc, zpow?_negSucc]
  rename_i n
  symm; rw [inv?_npow, inv?_npow]; apply eq_inv?_of_mul
  rw [mul_assoc, mul_comm a, ←npow_succ, inv?_mul_cancel]
  assumption
  assumption

def zpow?_pred (a: α) (n: ℤ) (h: a ≠ 0) : a ^? (n - 1) = a ^? n * a⁻¹? := by
  have := zpow?_succ (a⁻¹?) (-n) (by invert_tactic)
  repeat rw [inv?_zpow?] at this
  rwa [Int.neg_neg, Int.neg_add, Int.neg_neg, ←sub_eq_add_neg] at this

def zpow?_add (a: α) (n m: ℤ) (h: a ≠ 0) : a ^? (n + m) = a ^? n * a ^? m := by
  induction m using Int.succ_pred_induction with
  | zero => rw [add_zero, zpow?_zero, mul_one]
  | succ m ih => rw [←add_assoc, zpow?_succ, zpow?_succ, ih, mul_assoc]; repeat assumption
  | pred m ih => rw [←Int.add_sub_assoc, zpow?_pred, zpow?_pred, ih, mul_assoc]; repeat assumption

def zpow?_sub (a: α) (n m: ℤ) (h: a ≠ 0) : a ^? (n - m) = a ^? n /? a ^? m := by
  rw [div?_eq_mul_inv?, sub_eq_add_neg, zpow?_add]
  congr
  apply eq_inv?_of_mul
  rw [←zpow?_add, neg_add_cancel, zpow?_zero]
  repeat assumption

def zpow?AtHom (a: α) (h: a ≠ 0) : ℤ →ₐ* α where
  toFun z := a ^? z
  map_zero_to_one := by rw [zpow?_zero]
  map_add_to_mul n m := by rw [zpow?_add]; assumption

def zpow?_mul (a: α) (n m: ℤ) (h: a ≠ 0) : a ^? (n * m) = (a ^? n) ^? m := by
  induction m using Int.succ_pred_induction with
  | zero => rw [Int.mul_zero, zpow?_zero, zpow?_zero]
  | succ m ih => rw [Int.mul_add, mul_one, zpow?_add, zpow?_succ, ih]; repeat invert_tactic
  | pred m ih => rw [Int.mul_sub, mul_one, zpow?_sub, zpow?_pred, ih, div?_eq_mul_inv?]; repeat invert_tactic

def zpow?_neg (a: α) (n: ℤ) (h: a ≠ 0) : a ^? (-n) = (a ^? n)⁻¹? := by
  apply eq_inv?_of_mul
  rw [←zpow?_add, neg_add_cancel, zpow?_zero]
  assumption
