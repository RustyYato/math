import LeanMath.Tactic.AxiomBlame
import LeanMath.Data.Nat.Div

private def Bool.and_eq_true_iff' {x y : Bool} : (x && y) = true ↔ x = true ∧ y = true := by decide +revert

inductive BitInt.Bits where
-- nil true = -1
-- nil false = 0
| nil (b: Bool)
-- 2 * bs + b
| cons (b: Bool) (bs: Bits)

namespace BitInt.Bits

def testBit : Bits -> Nat -> Bool
| .nil a, _ => a
| .cons a as, n =>
  match n with
  | 0 => a
  | n + 1 => as.testBit n

def head := (testBit · 0)
def tail : Bits -> Bits
| .nil a => .nil a
| .cons _ as => as

instance : Setoid Bits where
  r a b := ∀i, a.testBit i = b.testBit i
  iseqv := {
    refl _ _ := rfl
    symm h n := (h n).symm
    trans h g n := (h n).trans (g n)
  }

@[refl] def refl (a: Bits) : a ≈ a := instSetoid.iseqv.refl _
@[symm] def symm {a b: Bits} : a ≈ b -> b ≈ a := instSetoid.iseqv.symm
def trans {a b c: Bits} : a ≈ b -> b ≈ c -> a ≈ c := instSetoid.iseqv.trans

def equiv_nil  : nil a ≈ nil a := refl _
def equiv_nil_cons  : nil a ≈ as ↔ nil a ≈ cons a as := by
  apply Iff.intro
  intro h n
  cases n; rfl
  rename_i n
  exact h n
  intro h n
  exact h (n + 1)
def equiv_cons_nil  : as ≈ nil a ↔ cons a as ≈ nil a := by
  apply Iff.intro
  intro h n
  cases n; rfl
  rename_i n
  exact h n
  intro h n
  exact h (n + 1)
def of_equiv_cons  : cons a as ≈ cons b bs -> as ≈ bs := by
  intro h n
  apply h (n + 1)
def equiv_cons  : as ≈ bs ↔ cons a as ≈ cons a bs := by
  apply Iff.intro
  intro h n
  cases n; rfl
  rename_i n
  exact h n
  intro h n
  exact h (n + 1)

private def nil_beq (a: Bool) : Bits -> Bool
| .nil b => a == b
| .cons b bs => a == b && nil_beq a bs

private def beq : Bits -> Bits -> Bool
| .nil a, bs => nil_beq a bs
| as, .nil b => nil_beq b as
| .cons a as, .cons b bs => a == b && beq as bs

instance : BEq Bits where
  beq := beq

private def nil_beq_iff_nil_equiv (a: Bool) (bs: Bits) : nil_beq a bs ↔ nil a ≈ bs := by
  induction bs with
  | nil b =>
    unfold nil_beq
    apply Iff.trans beq_iff_eq
    apply Iff.intro; intro h
    rw [congrArg nil h]
    intro h
    exact h 0
  | cons b bs ih =>
    show (_ && _) ↔ _
    apply Iff.trans Bool.and_eq_true_iff'
    apply Iff.intro
    intro ⟨h, g⟩
    replace h := eq_of_beq h; subst h
    apply equiv_nil_cons.mp
    apply ih.mp
    assumption
    intro h
    apply And.intro
    rw [show a = b from h 0]
    clear h; decide +revert
    apply ih.mpr
    intro n
    apply h (n + 1)

def beq_iff_equiv (as bs: Bits) : as == bs ↔ as ≈ bs := by
  induction as generalizing bs with
  | nil a => apply nil_beq_iff_nil_equiv
  | cons a as ih =>
    cases bs with
    | nil b =>
      apply Iff.trans
      apply nil_beq_iff_nil_equiv
      apply Iff.intro <;> apply symm
    | cons b bs =>
      show (_ && as == bs) ↔ _
      apply Iff.trans Bool.and_eq_true_iff'
      apply Iff.intro
      intro ⟨h, g⟩
      cases eq_of_beq h
      apply equiv_cons.mp
      apply (ih _).mp
      assumption
      intro h
      cases h 0
      apply And.intro
      cases a <;> rfl
      apply (ih _).mpr
      intro n
      apply h (n + 1)

instance (a b: Bits) : Decidable (a ≈ b) := decidable_of_bool (a == b) (beq_iff_equiv _ _)

def equiv_cons_head_tail (as: Bits) : as ≈ cons as.head as.tail := by
  cases as with
  | nil a => decide +revert
  | cons a as => rfl

instance : ReflBEq Bits where
  rfl := by
    intro a
    apply (beq_iff_equiv _ _).mpr
    rfl

def length : Bits -> Nat
| nil _ => 0
| cons _ as => as.length + 1

def IsMinimal (as: Bits) : Prop := ∀bs, as ≈ bs -> as.length ≤ bs.length

def eq_of_equiv_length_eq (as bs: Bits) (h: as ≈ bs) (g: as.length = bs.length) : as = bs := by
  induction as generalizing bs with
  | nil a =>
    cases bs
    cases h 0
    rfl
    contradiction
  | cons a as ih =>
    cases bs
    contradiction
    cases h 0
    congr
    apply ih
    apply equiv_cons.mpr
    assumption
    apply Nat.succ.inj
    assumption
def eq_of_is_minimal (as bs: Bits) (ha: IsMinimal as) (hb: IsMinimal bs) (h: as ≈ bs) : as = bs := by
  apply eq_of_equiv_length_eq
  assumption
  apply Nat.le_antisymm
  apply ha
  assumption
  apply hb; symm
  assumption

def push_bit (a: Bool) : Bits -> Bits
| .nil b => if a = b then .nil b else .cons a (.nil b)
| .cons b bs => .cons a (.cons b bs)

def push_bit_equiv_cons (a: Bool) (as: Bits) : as.push_bit a ≈ .cons a as := by
  cases as with
  | nil a' =>
    unfold push_bit
    dsimp
    split
    subst a'
    apply equiv_nil_cons.mp
    rfl
    rfl
  | cons a as =>
    rfl

def push_bit_is_minimal (a: Bool) (as: Bits) (h: as.IsMinimal) : (as.push_bit a).IsMinimal := by
  cases as with
  | nil a' =>
    unfold push_bit
    dsimp
    split; subst a
    assumption
    clear h; intro bs h
    show 1 ≤ _
    cases bs with
    | nil b =>
      have : a = b := h 0
      have : a' = b := h 1
      subst this
      contradiction
    | cons _ _ =>
      apply Nat.succ_le_succ
      apply Nat.zero_le
  | cons a' as =>
    unfold push_bit
    dsimp
    intro bs g
    cases bs with
    | nil b =>
      cases g 0
      replace g := equiv_cons_nil.mpr g
      have := h _ g
      contradiction
    | cons b bs =>
    cases bs with
    | nil b' =>
      cases g 0
      cases g 1
      replace g := equiv_cons.mpr g
      have := h _ g
      contradiction
    | cons b' bs =>
      apply Nat.succ_le_succ
      apply h
      cases g 0
      exact equiv_cons.mpr g

def minimize : Bits -> Bits
| .nil a => .nil a
| .cons a as => as.minimize.push_bit a

def minimize_equiv (as: Bits) : as.minimize ≈ as := by
  induction as with
  | nil a => rfl
  | cons a as ih =>
    apply trans (push_bit_equiv_cons _ _)
    apply equiv_cons.mp
    assumption

def minimize_is_minimal (as: Bits) : as.minimize.IsMinimal := by
  induction as with
  | nil a => intro bs h; apply Nat.zero_le
  | cons a as ih =>
    apply push_bit_is_minimal
    assumption

def bitwise_unary (f: Bool -> Bool) : Bits -> Bits
| .nil a => .nil (f a)
| .cons a as => .cons (f a) (as.bitwise_unary f)

def bitwise_binary (f: Bool -> Bool -> Bool) : Bits -> Bits -> Bits
| .nil a, bs => bs.bitwise_unary (f a)
| as, .nil b => as.bitwise_unary (f · b)
| .cons a as, .cons b bs => .cons (f a b) (bitwise_binary f as bs)

def testBit_bitwise_unary (f: Bool -> Bool) (as: Bits) : testBit (as.bitwise_unary f) n = f (testBit as n) := by
  induction as generalizing n with
  | nil a => rfl
  | cons a as ih =>
    cases n with
    | zero => rfl
    | succ n => apply ih

def testBit_bitwise_binary (f: Bool -> Bool -> Bool) (as bs: Bits) : testBit (bitwise_binary f as bs) n = f (testBit as n) (testBit bs n) := by
  induction as generalizing n bs with
  | nil a =>
    unfold bitwise_binary
    rw [testBit_bitwise_unary]
    rfl
  | cons a as ih =>
    cases bs with
    | nil =>
      unfold bitwise_binary
      rw [testBit_bitwise_unary]
      rfl
    | cons b bs =>
      cases n with
      | zero => rfl
      | succ n => apply ih

def ofNat : Nat -> Bits :=
  nat_div2_rec (motive := fun _ => Bits)
     (base := .nil false)
     (fun n _ ih => .cons (n % 2 == 1) ih)

instance : OfNat Bits n := ⟨ofNat n⟩

def ofNat_0 : ofNat 0 = .nil false := rfl
def ofNat_ind (n: Nat) (h: n ≠ 0) : ofNat n = .cons (n % 2 == 1) (ofNat (n / 2)) :=
  nat_div2_rec_ind _ _ _ h

def of_ofNat_equiv_nil_false : ofNat n ≈ nil false -> n = 0 := by
  intro h
  induction n using nat_div2_rec with
  | base => rfl
  | ind n g ih =>
    rw [ofNat_ind _ g] at h
    have : (n % 2 == 1) = false := h 0
    cases Or.symm (nat_mod2_eq_zero_or_one n) <;> rename_i hn
    · rw [hn] at this
      contradiction
    · clear this
      rw [hn] at h
      have hn' := ih (equiv_cons_nil.mpr h)
      rw [←nat_div_add_mod n 2, hn, hn']

def ofNat_not_equiv_nil_true : ¬ofNat n ≈ nil true := by
  induction n using nat_div2_rec with
  | base => decide
  | ind n g ih =>
    rw [ofNat_ind _ g]
    intro h
    have : (n % 2 == 1) = true := h 0
    cases nat_mod2_eq_zero_or_one n <;> rename_i hn
    · rw [hn] at this
      contradiction
    · clear this
      rw [hn] at h
      exact ih (equiv_cons_nil.mpr h)

def ofNat_minimal (n: Nat) : (ofNat n).IsMinimal := by
  induction n using nat_div2_rec with
  | base =>
    rw [ofNat_0]
    intro _ _
    apply Nat.zero_le
  | ind n h ih =>
    rw [ofNat_ind _ h]
    intro bs h
    cases bs with
    | cons b bs =>
      apply Nat.succ_le_succ
      apply ih
      have : (n % 2 == 1) = b := h 0
      subst b
      exact equiv_cons.mpr h
    | nil b =>
      exfalso
      rename_i n_ne_zero
      apply n_ne_zero
      have : (n % 2 == 1) = b := h 0
      subst b
      cases nat_mod2_eq_zero_or_one n <;> rename_i hn
      · rw [hn] at h
        simp at h
        have := of_ofNat_equiv_nil_false (equiv_cons_nil.mpr h)
        have h' := equiv_cons_nil.mpr h
        rw [←nat_div_add_mod n 2, hn, this]
      · exfalso
        rw [hn] at h
        replace h : _ ≈ nil true := equiv_cons_nil.mpr h
        exact ofNat_not_equiv_nil_true h

def toInt : Bits -> Int
| .nil a => if a then -1 else 0
| .cons a b => 2 * b.toInt + if a then 1 else 0

def toInt_rec (bs: Bits) : bs.toInt = 2 * bs.tail.toInt + if bs.head then 1 else 0 := by
  cases bs with
  | nil b => decide +revert
  | cons b bs => rfl

def toInt_spec (a b: Bits) : a ≈ b -> a.toInt = b.toInt := by
  intro h
  induction a generalizing b with
  | nil a =>
    cases a
    · show 0 = _
      replace h (n: Nat) : b.testBit n = false := (h n).symm
      induction b with
      | nil =>
        cases h 0
        rfl
      | cons b bs ih =>
        cases h 0
        unfold toInt
        dsimp; rw [←ih]
        rfl
        intro
        apply h (_ + 1)
    · show -1 = _
      replace h (n: Nat) : b.testBit n = true := (h n).symm
      induction b with
      | nil =>
        cases h 0
        rfl
      | cons b bs ih =>
        cases h 0
        unfold toInt
        dsimp; rw [←ih]
        rfl
        intro
        apply h (_ + 1)
  | cons a as ih =>
    rw [toInt_rec b, toInt]
    congr 1
    · congr 1
      apply ih
      replace h := trans h (equiv_cons_head_tail _)
      exact of_equiv_cons h
    · split; subst a
      rw [if_pos]
      exact (h 0).symm
      rw [if_neg]
      intro g
      replace h := trans h (equiv_cons_head_tail _)
      have : a = b.head := h 0
      rw [←this] at g
      contradiction

end BitInt.Bits

structure BitInt where
  val: BitInt.Bits
  min: val.IsMinimal

namespace BitInt

def ofBits (bs: Bits) : BitInt where
  val := bs.minimize
  min := Bits.minimize_is_minimal _

def sound (as bs: Bits) : as ≈ bs -> ofBits as = ofBits bs := by
  intro h
  simp [ofBits]
  apply Bits.eq_of_is_minimal
  apply Bits.minimize_is_minimal
  apply Bits.minimize_is_minimal
  apply Bits.trans _ (Bits.trans h (Bits.symm _))
  apply Bits.minimize_equiv
  apply Bits.minimize_equiv

def exact (as bs: Bits) : ofBits as = ofBits bs -> as ≈ bs := by
  intro h
  dsimp [ofBits] at h
  replace h := BitInt.mk.inj h
  apply Bits.trans (Bits.symm (Bits.minimize_equiv _))
  rw [h]; apply Bits.minimize_equiv

@[irreducible]
def lift (f: Bits -> α) (_h: ∀a b, a ≈ b -> f a = f b) (bs: BitInt) : α := f bs.val

@[irreducible]
def lift₂ (f: Bits -> Bits -> α) (_h: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (as bs: BitInt) : α := f as.val bs.val

def lift_ofBits (f: Bits -> α) (h) (bs: Bits) : lift f h (ofBits bs) = f bs := by
  unfold lift
  apply h
  apply Bits.minimize_equiv

def lift₂_ofBits (f: Bits -> Bits -> α) (h) (as bs: Bits) : lift₂ f h (ofBits as) (ofBits bs) = f as bs := by
  unfold lift₂
  apply h
  apply Bits.minimize_equiv
  apply Bits.minimize_equiv

def recOnSubsingleton {motive: BitInt -> Sort u} [∀b, Subsingleton (motive b)]
  (ofBits: ∀x, motive (ofBits x)) (bs: BitInt) : motive bs :=
  flip cast (ofBits bs.val) <| by
    congr
    obtain ⟨bs, _⟩ := bs
    unfold BitInt.ofBits
    dsimp
    congr
    apply Bits.eq_of_is_minimal
    apply Bits.minimize_is_minimal
    assumption
    apply Bits.minimize_equiv

@[induction_eliminator]
def ind {motive: BitInt -> Prop} (ofBits: ∀x, motive (ofBits x)) (bs: BitInt) : motive bs := by
  apply recOnSubsingleton
  assumption

def bitwise_unary (f: Bool -> Bool) : BitInt -> BitInt := lift (ofBits ∘ (Bits.bitwise_unary f)) <| by
  intro a b h
  apply sound
  intro n
  rw [Bits.testBit_bitwise_unary, Bits.testBit_bitwise_unary, h]

def bitwise_binary (f: Bool -> Bool -> Bool) : BitInt -> BitInt -> BitInt := lift₂ (fun a b => ofBits (Bits.bitwise_binary f a b)) <| by
  intro a b c d h g
  apply sound
  intro n
  rw [Bits.testBit_bitwise_binary, Bits.testBit_bitwise_binary, h, g]

instance : SDiff BitInt where
  sdiff := bitwise_binary fun a b => a && !b

instance : AndOp BitInt where
  and := bitwise_binary Bool.and

instance : OrOp BitInt where
  or := bitwise_binary Bool.or

instance : XorOp BitInt where
  xor := bitwise_binary Bool.xor

instance : Complement BitInt where
  complement := bitwise_unary Bool.not

instance : NatCast BitInt := ⟨fun n => ⟨.ofNat n, Bits.ofNat_minimal _⟩⟩
instance : OfNat BitInt n := ⟨n⟩

def toInt : BitInt -> Int := lift Bits.toInt Bits.toInt_spec

end BitInt
