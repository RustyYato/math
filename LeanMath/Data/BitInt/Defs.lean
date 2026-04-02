import LeanMath.Tactic.AxiomBlame
import LeanMath.Tactic.TypeStar
import LeanMath.Data.Nat.Div

inductive Integer.Bits where
| nil (rep: Bool)
| cons (msb: Bits) (lsb: Bool)
deriving DecidableEq, Repr

namespace Integer.Bits

def get : Bits -> Nat -> Bool
| .nil a => fun _ => a
| .cons as a => fun i =>
  match i with
  | 0 => a
  | i + 1 => as.get i

instance : GetElem Bits ℕ Bool (fun _ _ => True) where
  getElem as i _ := as.get i

def lsb : Bits -> Bool := (get · 0)

def msb : Bits -> Bits
| nil a => nil a
| cons as _ => as

@[simp] def lsb_nil (a: Bool) : lsb (nil a) = a := rfl
@[simp] def lsb_cons (as: Bits) (a: Bool) : lsb (cons as a) = a := rfl
@[simp] def msb_nil (a: Bool) : msb (nil a) = nil a := rfl
@[simp] def msb_cons (as: Bits) (a: Bool) : msb (cons as a) = as := rfl

@[simp] def get_zero_eq_lsb (as: Bits) : as[0] = as.lsb := rfl
def get_succ_eq_get_msb (as: Bits) (i: ℕ) : as[i + 1] = as.msb[i] := by cases as <;> rfl

instance setoid : Setoid Bits where
  r a b := ∀i: ℕ, a[i] = b[i]
  iseqv := {
    refl _ _ := rfl
    symm h i := (h i).symm
    trans h g i := (h i).trans (g i)
  }

@[refl] def refl (as: Bits) : as ≈ as := setoid.refl _
@[symm] def symm {as bs: Bits} : as ≈ bs -> bs ≈ as := setoid.symm
def symm_iff {as bs: Bits} : as ≈ bs ↔ bs ≈ as := ⟨symm, symm⟩
def trans {as bs cs: Bits} : as ≈ bs -> bs ≈ cs -> as ≈ cs := setoid.trans

def eqv_cons {as bs: Bits} {x: Bool} : as.cons x ≈ bs.cons x ↔ as ≈ bs := by
  apply Iff.intro
  intro h i; apply h (i + 1)
  intro h i; cases i
  rfl; apply h

def eqv_cons_nil {as: Bits} {x: Bool} : as.cons x ≈ nil x ↔ as ≈ nil x := by
  apply Iff.intro
  intro h i; apply h (i + 1)
  intro h i; cases i
  rfl; apply h

def eqv_nil_cons {as: Bits} {x: Bool} : nil x ≈ as.cons x ↔ nil x ≈ as := by
  apply Iff.trans symm_iff
  apply Iff.trans _ symm_iff
  apply eqv_cons_nil

-- as == nil b
private def beq_nil (b: Bool) : Bits -> Bool
| nil a => a == b
| cons as a => a == b && as.beq_nil b

def beq : Bits -> Bits -> Bool
| nil a => beq_nil a
| cons as a => fun
  | nil b => beq_nil b (cons as a)
  | cons bs b => a == b && beq as bs

instance : BEq Bits := ⟨beq⟩

private def bool_and_eq_true_iff {a b: Bool} : (a && b) ↔ (a ∧ b) := by decide +revert

private def beq_nil_iff_eqv {as: Bits} {b: Bool} : beq_nil b as ↔ as ≈ nil b := by
  induction as with
  | nil a =>
    unfold beq_nil
    apply Iff.trans beq_iff_eq
    apply Iff.intro
    intro rfl; rfl
    intro h; exact h 0
  | cons as a ih =>
    apply Iff.trans bool_and_eq_true_iff
    apply Iff.intro
    · intro ⟨h, g⟩
      cases LawfulBEq.eq_of_beq h
      apply eqv_cons_nil.mpr
      apply ih.mp; assumption
    · intro h; cases h 0
      apply And.intro
      apply LawfulBEq.toReflBEq.rfl
      apply ih.mpr
      apply eqv_cons_nil.mp
      assumption

def beq_iff_eqv {as bs: Bits} : as == bs ↔ as ≈ bs := by
  induction as generalizing bs with
  | nil a =>
    apply Iff.trans _ symm_iff
    apply beq_nil_iff_eqv
  | cons as a ih =>
    cases bs with
    | nil b => apply beq_nil_iff_eqv
    | cons bs b =>
      apply Iff.trans bool_and_eq_true_iff
      apply Iff.intro
      intro ⟨h, g⟩; cases eq_of_beq h
      apply eqv_cons.mpr
      apply ih.mp; assumption
      intro h; cases h 0
      apply And.intro
      apply LawfulBEq.toReflBEq.rfl
      apply ih.mpr
      apply eqv_cons.mp
      assumption

instance {as bs: Bits} : Decidable (as ≈ bs) := decidable_of_bool (as == bs) beq_iff_eqv

inductive IsReducedPartition : Bits -> Bool -> Prop where
| nil (a: Bool) : IsReducedPartition (nil a) (!a)
| cons (as: Bits) (a x: Bool) : IsReducedPartition (cons as a) x

inductive IsReduced : Bits -> Prop where
| nil (a: Bool) : IsReduced (nil a)
| cons (as: Bits) (a: Bool) : IsReducedPartition as a -> IsReduced as -> IsReduced (cons as a)

private def IsReduced_spec' {a: Bool} {bs: Bits} (hb: bs.IsReduced) (h: nil a ≈ bs) : nil a = bs := by
  induction hb with
  | nil b => cases h 0; rfl
  | cons bs b hpart hb ih =>
    cases h 0
    have := ih (eqv_nil_cons.mp h)
    subst bs
    cases a <;> nomatch hpart

def IsReduced_spec {as bs: Bits} (ha: as.IsReduced) (hb: bs.IsReduced) (h: as ≈ bs) : as = bs := by
  induction ha generalizing bs with
  | nil a =>
    apply IsReduced_spec'
    assumption
    assumption
  | cons as a hpart ha ih =>
    cases hb with
    | nil b =>
      symm; apply IsReduced_spec'
      apply IsReduced.cons <;> assumption
      symm; assumption
    | cons =>
      cases h 0; congr; apply ih
      assumption
      apply eqv_cons.mp
      assumption

def is_reduced_part : Bits -> Bool -> Bool
| .nil a, b => a ^^ b
| .cons _ _, _ => true

def is_reduced : Bits -> Bool
| .nil _ => true
| .cons as a => as.is_reduced_part a && as.is_reduced

def is_red_part_spec {as: Bits} {x: Bool} : as.is_reduced_part x ↔ IsReducedPartition as x := by
  apply Iff.intro
  intro h
  cases as with
  | nil a =>
    have : x = !a := by decide +revert
    subst x; apply IsReducedPartition.nil
  | cons as a => apply IsReducedPartition.cons
  intro h; cases h <;> unfold is_reduced_part; dsimp
  rw [Bool.xor_not_self]
  rfl

def is_red_part_eq_false_spec {as: Bits} {x: Bool} : as.is_reduced_part x = false ↔ ¬IsReducedPartition as x := by
  apply Iff.intro
  intro h g
  rw [is_red_part_spec.mpr g] at h
  contradiction
  intro h
  apply Bool.eq_false_iff.mpr
  intro g
  exact h (is_red_part_spec.mp g)

instance {as: Bits} {x: Bool} : Decidable (IsReducedPartition as x) := decidable_of_bool (is_reduced_part as x) is_red_part_spec

def is_reduced_spec {as: Bits} : as.is_reduced ↔ as.IsReduced := by
  induction as with
  | nil a =>
    apply Iff.intro
    intro h; apply IsReduced.nil
    intro; rfl
  | cons as a ih =>
    apply Iff.trans bool_and_eq_true_iff
    apply Iff.intro
    intro ⟨h, g⟩
    apply IsReduced.cons
    apply is_red_part_spec.mp
    assumption
    apply ih.mp; assumption
    intro h; cases h
    apply And.intro
    apply is_red_part_spec.mpr
    assumption
    apply ih.mpr; assumption

instance {as: Bits} : Decidable (IsReduced as) := decidable_of_bool (is_reduced as) is_reduced_spec

def push_bit (b: Bool) : Bits -> Bits
| nil a => bif a == b then nil a else cons (nil a) b
| cons as a => cons (cons as a) b

def get_push_bit_zero (b: Bool) (as: Bits) : (as.push_bit b)[0] = b := by
  cases as with
  | nil a => decide +revert
  | cons as a => rfl

def get_push_bit_succ (b: Bool) (as: Bits) (n: ℕ) : (as.push_bit b)[n + 1] = as[n] := by
  cases as with
  | nil a => cases a <;> cases b <;> rfl
  | cons as a => rfl

def push_bit_spec (b: Bool) (as: Bits) : as.push_bit b ≈ as.cons b := by
  cases as with
  | nil a => decide +revert
  | cons as a => rfl

def reduced_push_bit (b: Bool) (as: Bits) (h: as.IsReduced) : (as.push_bit b).IsReduced := by
  cases as with
  | nil a => decide +revert
  | cons as a =>
    apply IsReduced.cons
    apply IsReducedPartition.cons
    assumption

def eqv_push_bit_cons {as bs: Bits} {x: Bool} : as.push_bit x ≈ bs.cons x ↔ as ≈ bs := by
  apply Iff.intro
  intro h
  exact eqv_cons.mp <| trans (symm (push_bit_spec x as)) h
  intro h
  apply trans (push_bit_spec _ _)
  apply eqv_cons.mpr
  assumption

def eqv_cons_push_bit {as bs: Bits} {x: Bool} : as.cons x ≈ bs.push_bit x ↔ as ≈ bs := by
  apply Iff.trans symm_iff
  apply Iff.trans _ symm_iff
  apply eqv_push_bit_cons

def eqv_push_bit {as bs: Bits} {x: Bool} : as.push_bit x ≈ bs.push_bit x ↔ as ≈ bs := by
  apply Iff.intro
  intro h
  exact eqv_cons.mp <| trans (trans (symm (push_bit_spec _ _)) h) (push_bit_spec _ _)
  intro h
  apply trans <| trans (push_bit_spec x _) (eqv_cons.mpr h)
  symm; apply push_bit_spec

def eqv_push_bit_nil {as: Bits} {x: Bool} : as.push_bit x ≈ nil x ↔ as ≈ nil x := by
  apply Iff.intro
  intro h
  exact eqv_cons_nil.mp <| trans (symm (push_bit_spec _ _)) h
  intro h
  apply trans (push_bit_spec _ _)
  apply eqv_cons_nil.mpr
  assumption

def eqv_nil_push_bit {as: Bits} {x: Bool} : nil x ≈ as.push_bit x ↔ nil x ≈ as := by
  apply Iff.trans symm_iff
  apply Iff.trans _ symm_iff
  apply eqv_push_bit_nil

def reduce : Bits -> Bits
| nil a => nil a
| cons as a => as.reduce.push_bit a

def reduce_eqv (as: Bits) : as.reduce ≈ as := by
  induction as with
  | nil => rfl
  | cons as a ih =>
    unfold reduce
    apply eqv_push_bit_cons.mpr
    assumption

def reduced_reduce (as: Bits) :as.reduce.IsReduced := by
  induction as with
  | nil a => apply IsReduced.nil
  | cons a as ih =>
    apply reduced_push_bit
    assumption

end Integer.Bits

structure Integer where
  ofBits ::
  bits : Integer.Bits
  reduced: bits.IsReduced

namespace Integer

section Defs

def mk (as: Bits) : Integer where
  bits := as.reduce
  reduced := as.reduced_reduce

@[ext] def ext (as bs: Integer) (h: as.bits ≈ bs.bits) : as = bs := by
  obtain ⟨as, ha⟩ := as
  obtain ⟨bs, hb⟩ := bs
  congr; apply Bits.IsReduced_spec
  assumption
  assumption
  assumption

@[simp] def mk_bits (as: Integer) : mk as.bits = as := by
  ext; apply Bits.reduce_eqv

def sound {as bs: Bits} : as ≈ bs -> mk as = mk bs := by
  intro h; ext
  apply Bits.trans (Bits.reduce_eqv _)
  apply Bits.trans h; symm
  exact Bits.reduce_eqv _

def exact {as bs: Bits} : mk as = mk bs -> as ≈ bs := by
  intro h
  apply Bits.trans _ (Bits.reduce_eqv _)
  rw [show bs.reduce = as.reduce from congrArg Integer.bits h.symm]
  symm; exact Bits.reduce_eqv _

def quot_rec {motive: Integer -> Sort u}
  (mk: ∀x, motive (mk x))
  (_: ∀x y: Bits, x ≈ y -> mk x ≍ mk y)
  (a: Integer) : motive a :=
  cast (by rw [mk_bits]) (mk a.bits)

def cases {motive: Integer -> Prop}
  (mk: ∀x, motive (mk x))
  (a: Integer) : motive a :=
  quot_rec mk (fun _ _ h => Subsingleton.helim (by rw [sound h]) _ _) a

def lift (f: Bits -> α) (h: ∀x y, x ≈ y -> f x = f y) := quot_rec (motive := fun _ => α) f (by
  intro x y eqv; apply heq_of_eq
  apply h x y eqv)

def lift₂ (f: Bits -> Bits -> α) (_: ∀as bs cs ds, as ≈ cs -> bs ≈ ds -> f as bs = f cs ds) (as bs: Integer) := f as.bits bs.bits

@[simp] def quot_rec_mk {motive: Integer -> Sort u} {f: ∀x, motive (mk x)} {h} {as: Bits} : quot_rec f h (mk as) = f as := by
  unfold quot_rec
  apply eq_of_heq
  apply HEq.trans (cast_heq _ _)
  apply h
  apply Bits.reduce_eqv

@[simp] def lift_mk {f: Bits -> α} {h} {as: Bits} : lift f h (mk as) = f as := quot_rec_mk
@[simp] def lift₂_mk {f: Bits -> Bits -> α} {h} {as bs: Bits} : lift₂ f h (mk as) (mk bs) = f as bs := by
  unfold lift₂; apply h
  apply Bits.reduce_eqv
  apply Bits.reduce_eqv

def map_reduced (f: Bits -> Bits) (_: ∀x y, x ≈ y -> f x ≈ f y) (hf: ∀x: Bits, x.IsReduced -> (f x).IsReduced) (x: Integer) : Integer where
  bits := f x.bits
  reduced := by
    apply hf
    exact x.reduced

def map₂_reduced (f: Bits -> Bits -> Bits) (_: ∀as bs cs ds, as ≈ cs -> bs ≈ ds -> f as bs ≈ f cs ds) (hf: ∀as bs: Bits, as.IsReduced -> bs.IsReduced -> (f as bs).IsReduced) (as bs: Integer) : Integer where
  bits := f as.bits bs.bits
  reduced := by
    apply hf
    exact as.reduced
    exact bs.reduced

def map_reduced_eq_lift (f: Bits -> Bits) (h) (hf) (x: Integer) : map_reduced f h hf x = lift (mk ∘ f) (by
  intro x y _; apply sound
  apply h; assumption) x := by
  unfold map_reduced lift quot_rec
  symm; apply mk_bits {
    bits := _
    reduced := _
  }

def map₂_reduced_eq_lift₂ (f: Bits -> Bits -> Bits) (h) (hf) (x y: Integer) : map₂_reduced f h hf x y = lift₂ (fun a b => mk (f a b)) (by
  intro _ _ _ _ _ _; apply sound
  apply h; assumption; assumption) x y := by
  unfold map₂_reduced lift₂
  symm; apply mk_bits {
    bits := _
    reduced := _
  }

def map_reduced_mk {f: Bits -> Bits} {h hf} {x: Bits} : map_reduced f h hf (mk x) = mk (f x) := by
  rw [map_reduced_eq_lift, lift_mk]; rfl

def map₂_reduced_mk {f: Bits -> Bits -> Bits} {h} {hf} {x y: Bits} : map₂_reduced f h hf (mk x) (mk y) = mk (f x y) := by
  rw [map₂_reduced_eq_lift₂, lift₂_mk]

def nil (a: Bool) : Integer where
  bits := .nil a
  reduced := .nil _

def cons (as: Integer) (a: Bool) : Integer :=
  as.map_reduced (.push_bit a) (by
    intro as bs h
    apply Bits.eqv_push_bit.mpr
    assumption) (by
    intro as has
    apply Bits.reduced_push_bit
    assumption)

@[simp] def mk_nil (a: Bool) : nil a = mk (.nil a) := rfl

@[simp] def mk_cons (as: Bits) (a: Bool) : cons (mk as) a = mk (.cons as a) := by
  apply Eq.trans map_reduced_mk
  apply sound
  apply Bits.eqv_push_bit_cons.mpr
  rfl

def bits_induction
  {motive: Integer -> Prop}
  (nil: ∀x, motive (nil x))
  (cons: ∀as a, motive as -> motive (cons as a))
  (x: Integer) : motive x := by
  cases x using cases with | mk as =>
  induction as with
  | nil a => rw [←mk_nil]; apply nil
  | cons as a ih =>
    rw [←mk_cons]
    apply cons
    assumption

end Defs

section BitOps

def Bits.not : Bits -> Bits
| .nil a => .nil (!a)
| .cons as a => .cons as.not (!a)

def Bits.not_step (as: Bits) : as.not ≈ as.msb.not.cons (!as.lsb) := by
  cases as with
  | nil a => decide +revert
  | cons as a => rfl

def Bits.get_not (as: Bits) (n: ℕ) : (as.not)[n] = !as[n] := by
  induction as generalizing n with
  | nil => rfl
  | cons as a hn =>
    cases n; rfl
    apply hn

def Bits.eqv_not {as bs: Bits} (h: as ≈ bs) : as.not ≈ bs.not := by
  intro i; rw [get_not, get_not, h]

def Bits.reduced_not {as: Bits} (h: as.IsReduced) : as.not.IsReduced := by
  induction h with
  | nil a => apply IsReduced.nil
  | cons as a hpart ha ih =>
    apply IsReduced.cons _ _ _ ih
    cases hpart
    apply IsReducedPartition.nil
    apply IsReducedPartition.cons

def not : Integer -> Integer :=
  map_reduced Bits.not (by
    intro x y h; apply Bits.eqv_not
    assumption) (fun _ => Bits.reduced_not)

@[simp] def mk_not (a: Bits) : (mk a).not = mk a.not := map_reduced_mk

@[simp] def not_step (as: Integer) (a: Bool) : not (cons as a) = cons (not as) (!a) := by
  cases as using cases
  rw [mk_cons, mk_not, mk_not, mk_cons]
  apply sound
  apply Bits.not_step

def Bits.bitwise (f: Bool -> Bool) : Bits -> Bits :=
  fun as =>
  match f false, f true with
  | false, true => as
  | false, false => .nil false
  | true, true => .nil true
  | true, false => as.not

def Bits.get_bitwise (f: Bool -> Bool) (as: Bits) (n: ℕ) : (as.bitwise f)[n] = f as[n] := by
  unfold bitwise
  symm; split;
  any_goals cases as[n] <;> assumption
  rw [get_not]
  cases as[n] <;> assumption

def Bits.bitwise_step (f: Bool -> Bool) (as: Bits) : as.bitwise f ≈ (as.msb.bitwise f).cons (f as.lsb) := by
  intro i; rw [get_bitwise]
  cases i; rfl
  iterate 2 rw [get_succ_eq_get_msb]
  dsimp; rw [get_bitwise]

def Bits.eqv_bitwise {f: Bool -> Bool} (as bs: Bits) (h: as ≈ bs) : as.bitwise f ≈ bs.bitwise f := by
  unfold bitwise
  split; assumption; rfl; rfl
  apply eqv_not
  assumption

def Bits.reduced_bitwise {f: Bool -> Bool} (as: Bits) (h: as.IsReduced) : (as.bitwise f).IsReduced := by
  unfold bitwise
  split
  assumption
  apply IsReduced.nil
  apply IsReduced.nil
  apply reduced_not
  assumption

def bitwise (f: Bool -> Bool) : Integer -> Integer :=
  map_reduced (Bits.bitwise f) (by
    intro x y h
    apply Bits.eqv_bitwise
    assumption) (by
    intro x hx
    apply Bits.reduced_bitwise
    assumption)

@[simp] def mk_bitwise (f: Bool -> Bool) (x: Bits) : (mk x).bitwise f = mk (x.bitwise f) := map_reduced_mk

@[simp] def bitwise_step (f: Bool -> Bool) (as: Integer) (a: Bool) : bitwise f (cons as a) = cons (bitwise f as) (f a) := by
  cases as using cases with | _ as =>
  rw [mk_cons, mk_bitwise, mk_bitwise, mk_cons]
  apply sound
  apply Bits.bitwise_step

def Bits.bitwise₂ (f: Bool -> Bool -> Bool) : Bits -> Bits -> Bits
| .nil a => bitwise (f a)
| .cons as a => fun
  | nil b => bitwise (f · b) (cons as a)
  | cons bs b => push_bit (f a b) (bitwise₂ f as bs)

def Bits.get_bitwise₂ {f: Bool -> Bool -> Bool} (as bs: Bits) (n: ℕ) : (bitwise₂ f as bs)[n] = f as[n] bs[n] := by
  induction as generalizing bs n with
  | nil a =>
    dsimp [bitwise₂]
    rw [get_bitwise]; rfl
  | cons as a ih =>
    dsimp [bitwise₂]
    cases bs <;> dsimp
    rw [get_bitwise]; rfl
    cases n
    rw [get_push_bit_zero]; rfl
    rw [get_push_bit_succ, get_succ_eq_get_msb, get_succ_eq_get_msb]
    apply ih

def Bits.bitwise₂_step (f: Bool -> Bool -> Bool) (as bs: Bits) : bitwise₂ f as bs ≈ (bitwise₂ f as.msb bs.msb).cons (f as.lsb bs.lsb) := by
  intro i; rw [get_bitwise₂]
  cases i; rfl
  iterate 3 rw [get_succ_eq_get_msb]
  dsimp; rw [get_bitwise₂]

def Bits.eqv_bitwise₂ {f: Bool -> Bool -> Bool} (as bs cs ds: Bits) (h: as ≈ cs) (g: bs ≈ ds) : bitwise₂ f as bs ≈ bitwise₂ f cs ds := by
  intro i
  rw [get_bitwise₂, get_bitwise₂, h, g]

def Bits.reduced_bitwise₂ {f: Bool -> Bool -> Bool} (as bs: Bits) (ha: as.IsReduced) (hb: bs.IsReduced) : (bitwise₂ f as bs).IsReduced := by
  induction ha generalizing bs with
  | nil a =>
    apply reduced_bitwise
    assumption
  | cons as a hpart ha ih =>
    cases bs with
    | nil b =>
      unfold bitwise₂
      apply reduced_bitwise
      apply IsReduced.cons <;>
      assumption
    | cons bs b =>
      apply reduced_push_bit
      apply ih
      cases hb
      assumption

def bitwise₂ (f: Bool -> Bool -> Bool) : Integer -> Integer -> Integer :=
  map₂_reduced (Bits.bitwise₂ f) (by
    intro as bs cs ds h g
    apply Bits.eqv_bitwise₂
    assumption
    assumption) (by
    intro as bs ha hb
    apply Bits.reduced_bitwise₂
    assumption
    assumption)

@[simp] def mk_bitwise₂ (f: Bool -> Bool -> Bool) (as bs: Bits) : bitwise₂ f (mk as) (mk bs) = mk (Bits.bitwise₂ f as bs) := map₂_reduced_mk

@[simp] def bitwise₂_nil_left (f: Bool -> Bool -> Bool) (as: Integer) (x: Bool) : bitwise₂ f (nil x) as = bitwise (f x) as := rfl

@[simp] def bitwise₂_nil_right (f: Bool -> Bool -> Bool) (as: Integer) (x: Bool) : bitwise₂ f as (nil x) = bitwise (f · x) as := by
  cases as using cases with | mk as =>
  rw [mk_nil, mk_bitwise₂, mk_bitwise]
  apply sound
  intro i
  rw [Bits.get_bitwise₂, Bits.get_bitwise]
  rfl

@[simp] def bitwise₂_step (f: Bool -> Bool -> Bool) (as bs: Integer) (a b: Bool) : bitwise₂ f (cons as a) (cons bs b) = cons (bitwise₂ f as bs) (f a b) := by
  cases as using cases with | _ as =>
  cases bs using cases with | _ bs =>
  rw [mk_cons, mk_cons, mk_bitwise₂, mk_bitwise₂, mk_cons]
  apply sound
  apply Bits.bitwise₂_step

def and := bitwise₂ Bool.and
def or := bitwise₂ Bool.or
def xor := bitwise₂ Bool.xor

end BitOps

section Arith

def Bits.toInt : Bits -> ℤ
| .nil a => bif a then -1 else 0
| cons as a => as.toInt * 2 + bif a then 1 else 0

-- #eval Bits.toInt (.cons (.cons (.cons (.cons (.nil false) true) false) true) true)

def Bits.toInt_step (as: Bits) : as.toInt = as.msb.toInt * 2 + bif as.lsb then 1 else 0 := by
  cases as with
  | nil a => decide +revert
  | cons as as => rfl

def Bits.eqv_toInt {as bs: Bits} (h: as ≈ bs) : as.toInt = bs.toInt := by
  induction as generalizing bs with
  | nil a =>
    induction bs with
    | nil b => decide +revert
    | cons bs b ih =>
      rw [Bits.toInt_step (bs.cons b)]
      dsimp; cases h 0
      replace ih := ih (eqv_nil_cons.mp h)
      cases a
      replace ih : 0 = bs.toInt := ih
      dsimp; rw [←ih]; rfl
      replace ih : -1 = bs.toInt := ih
      dsimp; rw [←ih]; rfl
  | cons as a ih =>
    rw [toInt_step, toInt_step bs]; dsimp
    congr 2
    apply ih
    intro i
    have := h (i + 1)
    rwa [get_succ_eq_get_msb, get_succ_eq_get_msb] at this
    exact h 0

def toInt : Integer -> ℤ := lift Bits.toInt (fun _ _ => Bits.eqv_toInt)

@[simp] def mk_toInt (as: Bits) : (mk as).toInt = as.toInt := lift_mk

@[simp] def toInt_nil_false : toInt (nil false) = 0 := rfl
@[simp] def toInt_nil_true : toInt (nil true) = -1 := rfl
@[simp] def toInt_cons : toInt (cons as a) = toInt as * 2 + bif a then 1 else 0 := by
  cases as using cases with | _ as =>
  rw [mk_cons, mk_toInt, mk_toInt]
  rfl

def Bits.eqv_of_eq (a b: Bits) (h: a = b) : a ≈ b := by subst h; rfl

def Bits.ofNat : ℕ -> Bits :=
  Nat.strongRec (fun n ih =>
    match h:n with
  | 0 => .nil false
  | _ + 1 =>
    .cons (ih (n / 2) (by
    subst h
    apply nat_div2_rec_lemma
    nofun)) (n % 2 != 0))

def Bits.ofNat_step_ne_zero (n: ℕ) (hn: n ≠ 0) : Bits.ofNat n = cons (Bits.ofNat (n / 2)) (n % 2 != 0) := by
  cases n; contradiction
  apply Nat.strongRec_step
  rename_i n; clear n hn
  intro x f g h
  cases x <;> dsimp
  congr
  apply h

def Bits.ofNat_step (n: ℕ) : Bits.ofNat n ≈ cons (Bits.ofNat (n / 2)) (n % 2 != 0) := by
  cases n; decide
  rw [Bits.ofNat_step_ne_zero]
  nofun

def Bits.of_ofNat_eq_nil (n: ℕ) : Bits.ofNat n = nil x -> n = 0 ∧ x = false := by
  cases n; intro h; apply And.intro rfl
  cases h; rfl
  rename_i n; intro h
  exfalso
  rw [ofNat_step_ne_zero (n + 1) nofun] at h
  contradiction

def Bits.reduced_ofNat (n: ℕ) : (Bits.ofNat n).IsReduced := by
  induction n using Nat.strongRec with
  | ind n ih =>
    cases n with
    | zero => apply IsReduced.nil
    | succ n =>
    -- | succ n ih =>
    rw [Bits.ofNat_step_ne_zero (n + 1) nofun]
    apply IsReduced.cons _ _ _ (ih _ (by
      apply nat_div2_rec_lemma
      nofun))
    generalize hm₀:(n + 1) / 2 = m₀
    generalize hm₁:((n + 1) % 2) = m₁
    cases h:ofNat m₀
    · obtain ⟨rfl, rfl⟩ := Bits.of_ofNat_eq_nil _ h
      clear h
      match m₁ with
      | 0 =>
        dsimp
        have := nat_div_add_mod (n + 1) 2
        rw [hm₀, hm₁] at this
        nomatch this
      | 1 =>
        apply IsReducedPartition.nil
      | _ + 2 =>
        have := Nat.mod_lt (n + 1) (y := 2) (by decide)
        rw [hm₁] at this
        nomatch Nat.not_le_of_lt this (Nat.le_add_left _ _)
    · apply IsReducedPartition.cons

def ofNat (n: ℕ) : Integer where
  bits := Bits.ofNat n
  reduced := Bits.reduced_ofNat n

instance : NatCast Integer := ⟨ofNat⟩
instance : OfNat Integer n := ⟨n⟩

def Bits.neg : Bits -> Bits
| .nil a =>
  match a with
  | false => .nil false
  | true => .cons (.nil false) true
| .cons as a =>
  .push_bit a <| bif a then as.not else as.neg

def Bits.neg_step (as: Bits) : as.neg ≈ cons (bif as.lsb then as.msb.not else as.msb.neg) as.lsb := by
  cases as with
  | nil a => decide +revert
  | cons as a => apply push_bit_spec

def Bits.eqv_neg {as bs: Bits} (h: as ≈ bs) : neg as ≈ neg bs := by
  induction as generalizing bs with
  | nil a =>
    induction bs with
    | nil b => decide +revert
    | cons bs b ih =>
      cases h 0;
      symm; apply trans (neg_step _); symm
      dsimp
      cases a <;> dsimp [neg]
      apply eqv_nil_cons.mpr
      apply ih; apply eqv_nil_cons.mp
      assumption; apply eqv_cons.mpr
      apply eqv_not (eqv_nil_cons.mp h)
  | cons as a ih =>
    cases bs with
    | nil b =>
      cases b <;> dsimp [neg]
      cases h 0; apply eqv_push_bit_nil.mpr
      dsimp; apply trans (ih (eqv_cons_nil.mp h))
      rfl; cases h 0; apply eqv_push_bit_cons.mpr
      dsimp; apply trans (eqv_not (eqv_cons_nil.mp h))
      rfl
    | cons bs b =>
      dsimp [neg]; cases h 0
      apply eqv_push_bit.mpr
      cases a <;> dsimp
      apply ih; exact eqv_cons.mp h
      apply eqv_not; exact eqv_cons.mp h

def Bits.reduced_neg (as: Bits) (ha: as.IsReduced) : IsReduced (neg as) := by
  induction ha with
  | nil a => decide +revert
  | cons as a hpart ha ih =>
    apply reduced_push_bit
    cases a <;> dsimp
    apply ih
    apply reduced_not
    assumption

def neg : Integer -> Integer :=
  map_reduced Bits.neg (by
    intro a b h
    apply Bits.eqv_neg
    assumption) (by
    intro a ha
    apply Bits.reduced_neg
    assumption)

@[simp] def mk_neg (as: Bits) : (mk as).neg = mk as.neg := map_reduced_mk

instance : Neg Integer := ⟨neg⟩

end Arith

end Integer
