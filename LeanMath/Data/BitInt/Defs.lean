import LeanMath.Tactic.AxiomBlame
import LeanMath.Tactic.TypeStar
import LeanMath.Data.Nat.Div
import LeanMath.Algebra.Ring.Defs

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

def msb_cons_lsb (as: Bits) : as.msb.cons as.lsb ≈ as := by
  intro i; cases i
  rw [get_zero_eq_lsb, get_zero_eq_lsb, lsb_cons]
  rw [get_succ_eq_get_msb, get_succ_eq_get_msb, msb_cons]

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
deriving DecidableEq

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

def mk_nil (a: Bool) : nil a = mk (.nil a) := rfl

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

def Bits.eqv_msb {as bs: Bits} : as ≈ bs -> as.msb ≈ bs.msb := by
  intro h
  intro i; rw [←get_succ_eq_get_msb, ←get_succ_eq_get_msb]
  apply h (i + 1)

def Bits.eqv_of_step
  (f: α -> Bits -> Bits)
  (g: α -> Bits -> Bool -> Bits)
  (step: ∀x (as: Bits), f x as ≈ g x as.msb as.lsb)
  (cong: ∀as bs: Bits, as ≈ bs -> (∀x, f x as.msb ≈ f x bs.msb) -> ∀x, g x as.msb as.lsb ≈ g x bs.msb bs.lsb)
  : ∀x as bs, as ≈ bs -> f x as ≈ f x bs := by
  intro x as bs h
  induction as generalizing bs x with
  | nil a =>
    induction bs generalizing x with
    | nil b => cases h 0; rfl
    | cons bs b ih =>
      cases h 0
      apply trans _ (symm (step _ _))
      apply trans (step _ _)
      apply cong
      assumption
      dsimp; intro x; apply ih
      apply eqv_nil_cons.mp
      assumption
  | cons as a ih =>
    apply trans _ (symm (step _ _))
    apply trans (step _ _)
    apply cong
    assumption
    dsimp; intro x; apply ih
    apply eqv_cons.mp
    apply trans h; symm
    rw [show a = bs.lsb from ?_]
    apply msb_cons_lsb
    apply h 0

def Bits.eqv_of_step₂
  (f: α -> Bits -> Bits -> Bits)
  (g: α -> Bits -> Bool -> Bits -> Bool -> Bits)
  (step: ∀(x: α) (as bs: Bits), f x as bs ≈ g x as.msb as.lsb bs.msb bs.lsb)
  (cong: ∀as bs cs ds: Bits, as ≈ cs -> bs ≈ ds -> (∀x, f x as.msb bs.msb ≈ f x cs.msb ds.msb) -> ∀x, g x as.msb as.lsb bs.msb bs.lsb ≈ g x cs.msb cs.lsb ds.msb ds.lsb)
  : ∀x as bs cs ds, as ≈ cs -> bs ≈ ds -> f x as bs ≈ f x cs ds := by
  intro x as bs cs ds ac bd
  induction as generalizing bs cs ds x with
  | nil a =>
    induction cs generalizing bs ds x with
    | nil c =>
      cases ac 0
      apply eqv_of_step (fun x bs => f x (nil a) bs) (fun x bs b => g x (nil a) a bs b)
      intro bs; apply step
      intro bs₀ bs₁ h₀ h₁
      apply cong (nil a) _ (nil a)
      rfl; assumption
      assumption
      assumption
    | cons cs c ih =>
      apply trans (step _ (nil _) bs)
      apply trans _ (symm (step _ _ ds))
      apply cong; assumption
      assumption
      intro x
      apply ih
      apply eqv_nil_cons.mp
      cases ac 0; assumption
      apply Bits.eqv_msb
      assumption
  | cons as a ih =>
    apply trans (step _ _ bs)
    apply trans _ (symm (step _ _ ds))
    apply cong
    assumption; assumption
    dsimp; intro x; apply ih
    apply Bits.eqv_msb ac
    apply Bits.eqv_msb bd

def lsb : Integer -> Bool := lift Bits.lsb (fun _ _ h => h 0)

def msb : Integer -> Integer := map_reduced Bits.msb (fun _ _ => Bits.eqv_msb) <| by
  intro a h
  cases h; apply Bits.IsReduced.nil
  assumption

@[simp] def mk_lsb (as: Bits) : (mk as).lsb = as.lsb := lift_mk
@[simp] def mk_msb (as: Bits) : (mk as).msb = mk as.msb := map_reduced_mk

def msb_cons_lsb (as: Integer) : cons as.msb as.lsb = as := by
  cases as using cases with | mk as =>
  rw [mk_msb, mk_lsb, mk_cons]
  apply sound
  apply Bits.msb_cons_lsb

@[simp] def lsb_nil (a: Bool) : lsb (nil a) = a := rfl
@[simp] def lsb_cons (as: Integer) (a: Bool) : lsb (cons as a) = a := by
  cases as using cases; rw [mk_cons, mk_lsb, Bits.lsb_cons]
@[simp] def msb_nil (a: Bool) : msb (nil a) = nil a := rfl
@[simp] def msb_cons (as: Integer) (a: Bool) : msb (cons as a) = as := by
  cases as using cases; rw [mk_cons, mk_msb, Bits.msb_cons]

end Defs

section BitOps

def Bits.not : Bits -> Bits
| .nil a => .nil (!a)
| .cons as a => .cons as.not (!a)

def Bits.step_not (as: Bits) : as.not ≈ as.msb.not.cons (!as.lsb) := by
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

@[simp] def step_not (as: Integer) (a: Bool) : not (cons as a) = cons (not as) (!a) := by
  cases as using cases
  rw [mk_cons, mk_not, mk_not, mk_cons]
  apply sound
  apply Bits.step_not

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

def Bits.step_bitwise (f: Bool -> Bool) (as: Bits) : as.bitwise f ≈ (as.msb.bitwise f).cons (f as.lsb) := by
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

@[simp] def step_bitwise (f: Bool -> Bool) (as: Integer) (a: Bool) : bitwise f (cons as a) = cons (bitwise f as) (f a) := by
  cases as using cases with | _ as =>
  rw [mk_cons, mk_bitwise, mk_bitwise, mk_cons]
  apply sound
  apply Bits.step_bitwise

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

def Bits.step_toInt (as: Bits) : as.toInt = as.msb.toInt * 2 + bif as.lsb then 1 else 0 := by
  cases as with
  | nil a => decide +revert
  | cons as as => rfl

def Bits.eqv_toInt {as bs: Bits} (h: as ≈ bs) : as.toInt = bs.toInt := by
  induction as generalizing bs with
  | nil a =>
    induction bs with
    | nil b => decide +revert
    | cons bs b ih =>
      rw [Bits.step_toInt (bs.cons b)]
      dsimp; cases h 0
      replace ih := ih (eqv_nil_cons.mp h)
      cases a
      replace ih : 0 = bs.toInt := ih
      dsimp; rw [←ih]; rfl
      replace ih : -1 = bs.toInt := ih
      dsimp; rw [←ih]; rfl
  | cons as a ih =>
    rw [step_toInt, step_toInt bs]; dsimp
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

def Bits.step_ofNat_ne_zero (n: ℕ) (hn: n ≠ 0) : Bits.ofNat n = cons (Bits.ofNat (n / 2)) (n % 2 != 0) := by
  cases n; contradiction
  apply Nat.step_strongRec
  rename_i n; clear n hn
  intro x f g h
  cases x <;> dsimp
  congr
  apply h

def Bits.step_ofNat (n: ℕ) : Bits.ofNat n ≈ cons (Bits.ofNat (n / 2)) (n % 2 != 0) := by
  cases n; decide
  rw [Bits.step_ofNat_ne_zero]
  nofun

def Bits.of_ofNat_eq_nil (n: ℕ) : Bits.ofNat n = nil x -> n = 0 ∧ x = false := by
  cases n; intro h; apply And.intro rfl
  cases h; rfl
  rename_i n; intro h
  exfalso
  rw [step_ofNat_ne_zero (n + 1) nofun] at h
  contradiction

def Bits.reduced_ofNat (n: ℕ) : (Bits.ofNat n).IsReduced := by
  induction n using Nat.strongRec with
  | ind n ih =>
    cases n with
    | zero => apply IsReduced.nil
    | succ n =>
    -- | succ n ih =>
    rw [Bits.step_ofNat_ne_zero (n + 1) nofun]
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

instance : NatCast Bits := ⟨.ofNat⟩
instance : OfNat Bits n := ⟨n⟩

instance : NatCast Integer := ⟨ofNat⟩
instance : OfNat Integer n := ⟨n⟩

def mk_natCast (n: ℕ) : n = mk n := by
  ext; symm; apply Bits.reduce_eqv

def mk_OfNat (n: ℕ) : OfNat.ofNat n = mk (OfNat.ofNat n) := by
  ext; symm; apply Bits.reduce_eqv

def step_natCast (n: ℕ) : n = cons (n / 2: ℕ) (n % 2 != 0) := by
  rw [mk_natCast, mk_natCast, mk_cons]
  apply sound; apply Bits.step_ofNat n

def Bits.neg : Bits -> Bits
| .nil a =>
  match a with
  | false => .nil false
  | true => .cons (.nil false) true
| .cons as a =>
  .push_bit a <| bif a then as.not else as.neg

def Bits.step_neg (as: Bits) : as.neg ≈ cons (bif as.lsb then as.msb.not else as.msb.neg) as.lsb := by
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
      symm; apply trans (step_neg _); symm
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

instance : Neg Bits := ⟨.neg⟩
instance : Neg Integer := ⟨neg⟩

@[simp] def mk_neg (as: Bits) : -(mk as) = mk as.neg := by
  show neg _ = _
  exact map_reduced_mk

def step_neg (as: Integer) (a: Bool) : -(cons as a) = cons (bif a then as.not else -as) a := by
  cases as using cases with | mk as =>
  rw [mk_neg, mk_cons, mk_neg, mk_not]
  cases a
  all_goals
  dsimp; rw [mk_cons]; apply sound
  cases as with
  | nil a => decide +revert
  | cons as a =>
    apply Bits.eqv_push_bit_cons.mpr
    rfl

def Bits.inc : Bits -> Bits
| .nil a =>
  match a with
  | false => 1
  | true => 0
| .cons as a => .push_bit (!a) (bif a then as.inc else as)

def Bits.dec : Bits -> Bits
| .nil a =>
  match a with
  | false => -1
  | true => -2
| .cons as a => .push_bit (!a) (bif a then as else as.dec)

def Bits.step_inc (as: Bits) : as.inc ≈ .cons (bif as.lsb then as.msb.inc else as.msb) !as.lsb := by
  cases as with
  | nil a => decide +revert
  | cons as a =>
    apply eqv_push_bit_cons.mpr
    rfl

def Bits.step_dec (as: Bits) : as.dec ≈ .cons (bif as.lsb then as.msb else as.msb.dec) !as.lsb := by
  cases as with
  | nil a => decide +revert
  | cons as a =>
    apply eqv_push_bit_cons.mpr
    rfl

def Bits.eqv_inc {as bs: Bits} (h: as ≈ bs) : as.inc ≈ bs.inc := by
  induction as generalizing bs with
  | nil a =>
    induction bs with
    | nil b => decide +revert
    | cons bs b ih =>
      apply trans (Bits.step_inc _)
      apply trans _ (symm (Bits.step_inc _))
      cases h 0; cases a <;> dsimp
      apply eqv_cons.mpr; apply eqv_nil_cons.mp; assumption
      apply eqv_cons.mpr; apply ih; apply eqv_nil_cons.mp; assumption
  | cons as a ih =>
    apply trans (Bits.step_inc _)
    apply trans _ (symm (Bits.step_inc _))
    replace h := trans h (symm (msb_cons_lsb bs))
    revert h; generalize bs.msb = msb; generalize bs.lsb = lsb
    intro h; cases h 0
    cases a <;> dsimp
    apply eqv_cons.mpr
    apply eqv_cons.mp
    assumption
    apply eqv_cons.mpr
    apply ih
    apply eqv_cons.mp
    assumption

def Bits.eqv_dec {as bs: Bits} (h: as ≈ bs) : as.dec ≈ bs.dec := by
  induction as generalizing bs with
  | nil a =>
    induction bs with
    | nil b => decide +revert
    | cons bs b ih =>
      apply trans (Bits.step_dec _)
      apply trans _ (symm (Bits.step_dec _))
      cases h 0; cases a <;> dsimp
      apply eqv_cons.mpr; apply ih; apply eqv_nil_cons.mp; assumption
      apply eqv_cons.mpr; apply eqv_nil_cons.mp; assumption
  | cons as a ih =>
    apply trans (Bits.step_dec _)
    apply trans _ (symm (Bits.step_dec _))
    replace h := trans h (symm (msb_cons_lsb bs))
    revert h; generalize bs.msb = msb; generalize bs.lsb = lsb
    intro h; cases h 0
    cases a <;> dsimp
    apply eqv_cons.mpr
    apply ih
    apply eqv_cons.mp
    assumption
    apply eqv_cons.mpr
    apply eqv_cons.mp
    assumption

def Bits.reduced_inc (as: Bits) (h: as.IsReduced) : as.inc.IsReduced := by
  induction h with
  | nil a => decide +revert
  | cons as a hpart h ih =>
    apply reduced_push_bit
    cases a <;> assumption

def Bits.reduced_dec (as: Bits) (h: as.IsReduced) : as.dec.IsReduced := by
  induction h with
  | nil a => decide +revert
  | cons as a hpart h ih =>
    apply reduced_push_bit
    cases a <;> assumption

def inc : Integer -> Integer := map_reduced Bits.inc (fun _ _ => Bits.eqv_inc) Bits.reduced_inc
def dec : Integer -> Integer := map_reduced Bits.dec (fun _ _ => Bits.eqv_dec) Bits.reduced_dec

@[simp] def mk_inc (as: Bits) : (mk as).inc = mk as.inc := map_reduced_mk
@[simp] def mk_dec (as: Bits) : (mk as).dec = mk as.dec := map_reduced_mk

@[simp] def inc_nil_false : inc (nil false) = 1 := rfl
@[simp] def inc_nil_true : inc (nil true) = 0 := rfl
@[simp] def dec_nil_false : dec (nil false) = -1 := rfl
@[simp] def dec_nil_true : dec (nil true) = -2 := rfl
@[simp] def step_inc (as: Integer) (a: Bool) : inc (cons as a) = cons (bif a then as.inc else as) (!a) := by
  cases as using cases with | mk as =>
  rw [mk_cons, mk_inc]
  apply Eq.trans; apply sound
  apply Bits.step_inc
  dsimp
  cases a <;> dsimp
  rw [mk_cons]
  rw [mk_inc, mk_cons]
@[simp] def step_dec (as: Integer) (a: Bool) : dec (cons as a) = cons (bif a then as else as.dec) (!a) := by
  cases as using cases with | mk as =>
  rw [mk_cons, mk_dec]
  apply Eq.trans; apply sound
  apply Bits.step_dec
  dsimp
  cases a <;> dsimp
  rw [mk_dec, mk_cons]
  rw [mk_cons]

def inc_dec (as: Integer) : as.inc.dec = as := by
  induction as using bits_induction with
  | nil a => decide +revert
  | cons a as ih =>
    rw [step_inc, step_dec]
    rw [Bool.not_not]; congr
    cases as <;> dsimp [Bool.not]
    rw [ih]

def dec_inc (as: Integer) : as.dec.inc = as := by
  induction as using bits_induction with
  | nil a => decide +revert
  | cons a as ih =>
    rw [step_dec, step_inc]
    rw [Bool.not_not]; congr
    cases as <;> dsimp [Bool.not]
    rw [ih]

def inc_inj {as bs: Integer} : as.inc = bs.inc ↔ as = bs := by
  apply Iff.intro; intro h
  rw [←inc_dec as, ←inc_dec bs, h]
  apply congrArg inc
def dec_inj {as bs: Integer} : as.dec = bs.dec ↔ as = bs := by
  apply Iff.intro; intro h
  rw [←dec_inc as, ←dec_inc bs, h]
  apply congrArg dec

def Bits.any_two_bits : Bool -> Bool -> Bool -> Bool
| false, a, b => a && b
| true, a, b => a || b

@[simp] def Bits.any_two_bits₀ (a b: Bool) : any_two_bits false a b = (a && b) := rfl
@[simp] def Bits.any_two_bits₁ (a b: Bool) : any_two_bits true a b = (a || b) := rfl
@[simp] def Bits.any_two_bits₂ (a b: Bool) : any_two_bits a false b = (a && b) := by decide +revert
@[simp] def Bits.any_two_bits₃ (a b: Bool) : any_two_bits a true b = (a || b) := by decide +revert
@[simp] def Bits.any_two_bits₄ (a b: Bool) : any_two_bits a b false = (a && b) := by decide +revert
@[simp] def Bits.any_two_bits₅ (a b: Bool) : any_two_bits a b true = (a || b) := by decide +revert

def Bits.nil_add (as: Bits) : Bool -> Bool -> Bits
-- carry = 0, and nil = 0
| false, false => as
-- carry = 1, and nil = 0
| true, false => as.inc
-- carry = 0, and nil = -1
| false, true => as.dec
-- carry = 1, and nil = -1
| true, true => as

@[simp] def Bits.nil_add_ff (as: Bits) : nil_add as false false = as := rfl
@[simp] def Bits.nil_add_tf (as: Bits) : nil_add as true false = as.inc := rfl
@[simp] def Bits.nil_add_ft (as: Bits) : nil_add as false true = as.dec := rfl
@[simp] def Bits.nil_add_tt (as: Bits) : nil_add as true true = as := rfl

def Bits.add_with_carry (carry: Bool) (as bs: Bits) : Bits :=
  match as with
  | .nil a => nil_add bs carry a
  | .cons as a =>
    match bs with
    | .nil b => nil_add (cons as a) carry b
    | .cons bs b => push_bit (carry ^^ a ^^ b) (add_with_carry (any_two_bits carry a b) as bs)

def Bits.step_nil_add (bs: Bits) (carry a: Bool) : nil_add bs carry a ≈ (bs.msb.nil_add (any_two_bits carry a bs.lsb) a).cons (carry ^^ a ^^ bs.lsb) := by
  cases bs with
  | nil b => decide +revert
  | cons bs b =>
    cases carry <;> cases a
    all_goals dsimp [Bool.and, Bool.or]
    all_goals repeat first|rw [Bool.false_xor]|rw [Bool.true_xor]|rw [Bool.not_true]|rw [Bool.not_false]
    cases b <;> dsimp
    apply step_dec
    apply step_dec
    cases b <;> dsimp
    apply step_inc
    apply step_inc

def Bits.step_add_with_carry (carry: Bool) (as bs: Bits) : add_with_carry carry as bs ≈ cons (add_with_carry (any_two_bits carry as.lsb bs.lsb) as.msb bs.msb) (carry ^^ as.lsb ^^ bs.lsb) := by
  cases as with
  | nil a => apply step_nil_add
  | cons as a =>
    cases bs with
    | cons bs b =>
      apply eqv_push_bit_cons.mpr
      rfl
    | nil b =>
      apply trans
      apply step_nil_add
      dsimp
      cases as with
      | nil =>
        unfold add_with_carry
        decide +revert
      | cons as a' =>
        unfold add_with_carry
        dsimp
        rw [Bool.xor_assoc, Bool.xor_comm b, Bool.xor_assoc]
        rw [show any_two_bits carry b a = any_two_bits carry a b from ?_]
        decide +revert

def Bits.eqv_add_with_carry (carry: Bool) (as bs cs ds: Bits) :
  as ≈ cs -> bs ≈ ds ->
  add_with_carry carry as bs ≈ add_with_carry carry cs ds := by
  revert carry as bs cs ds
  apply eqv_of_step₂ _ (fun carry as a bs b => cons (add_with_carry (any_two_bits carry a b) as bs) (carry ^^ a ^^ b))
  apply step_add_with_carry
  intro as bs cs ds ac bd h
  iterate 4 rw [←get_zero_eq_lsb]
  rw [ac 0, bd 0]
  intro carry
  apply eqv_cons.mpr
  apply h

def Bits.reduced_nil_add (carry: Bool) (a: Bool) (bs: Bits) (hb: bs.IsReduced) : (nil_add bs carry a).IsReduced := by
  unfold nil_add
  split
  assumption
  apply reduced_inc
  assumption
  apply reduced_dec
  assumption
  assumption

def Bits.reduced_add_with_carry (carry: Bool) (as bs: Bits) (ha: as.IsReduced) (hb: bs.IsReduced) : (add_with_carry carry as bs).IsReduced := by
  induction ha generalizing carry bs with
  | nil =>
    apply Bits.reduced_nil_add
    assumption
  | cons as a hpart ha ih =>
    cases hb with
    | nil =>
      apply Bits.reduced_nil_add
      apply IsReduced.cons <;> assumption
    | cons =>
      apply reduced_push_bit
      apply ih
      assumption

def add_with_carry (carry: Bool) : Integer -> Integer -> Integer := map₂_reduced (Bits.add_with_carry carry) (Bits.eqv_add_with_carry _) (Bits.reduced_add_with_carry _)

instance : Add Bits := ⟨Bits.add_with_carry false⟩
instance : Add Integer := ⟨add_with_carry false⟩

def mk_add_with_carry (carry: Bool) (as bs: Bits) : add_with_carry carry (mk as) (mk bs) = mk (.add_with_carry carry as bs) := map₂_reduced_mk
def mk_add (as bs: Bits) : (mk as) + (mk bs) = mk (as + bs) := mk_add_with_carry false _ _

def step_add_with_carry (carry: Bool) (as bs: Integer) (a b: Bool) : add_with_carry carry (cons as a) (cons bs b) = cons (add_with_carry (Bits.any_two_bits carry a b) as bs) (carry ^^ a ^^ b) := by
  cases as using cases with | _ as =>
  cases bs using cases with | _ bs =>
  rw [mk_cons, mk_add_with_carry, mk_cons, mk_add_with_carry]
  rw [sound (Bits.step_add_with_carry _ _ _)]
  rfl

def add_eq_add_with_carry (as bs: Integer) : as + bs = add_with_carry false as bs := rfl

instance : Sub Integer where
  sub as bs := as + -bs

def add_with_carry_comm (as bs: Integer) : add_with_carry carry as bs = add_with_carry carry bs as := by
  induction as using bits_induction generalizing bs carry with
  | nil a =>
    induction bs using bits_induction with
    | nil b => decide +revert
    | cons bs b ih =>
      cases bs using cases with | mk bs =>
      rw [mk_cons, mk_nil, mk_add_with_carry, mk_add_with_carry]
      apply sound
      rfl
  | cons as a ih =>
    induction bs using bits_induction with
    | nil b =>
      cases as using cases with | mk as =>
      rw [mk_cons, mk_nil, mk_add_with_carry, mk_add_with_carry]
      apply sound
      rfl
    | cons bs b ih =>
      clear ih; rw [step_add_with_carry, step_add_with_carry]
      congr 1
      rw [show Bits.any_two_bits _ _ _ = Bits.any_two_bits _ _ _ from ?_]
      apply ih
      decide +revert
      decide +revert

instance : IsAddComm Integer where
  add_comm := add_with_carry_comm

instance : IsLawfulZeroAdd Integer where
  zero_add _ := rfl
  add_zero a := by rw [add_comm]; rfl

def add_with_carry_true (as bs: Integer) : add_with_carry true as bs = (as + bs).inc := by
  show _ = inc (add_with_carry _ _ _)
  induction as using bits_induction generalizing bs with
  | nil a =>
    induction bs using bits_induction with
    | nil => decide +revert
    | cons bs b ih =>
      rw [←msb_cons_lsb (nil a)]; dsimp
      rw [step_add_with_carry, step_add_with_carry]
      dsimp
      rw [Bool.true_xor, Bool.false_xor, step_inc]
      cases a <;> cases b <;> dsimp [Bool.and, Bool.or, Bool.not]
      all_goals repeat first|rw [Bool.false_xor]|rw [Bool.true_xor]|dsimp [Bool.not]
      congr
      congr
  | cons as a ih =>
    rw [←msb_cons_lsb bs, step_add_with_carry, step_add_with_carry]
    dsimp
    rw [Bool.true_xor, Bool.false_xor, step_inc]
    cases a <;> cases bs.lsb <;> dsimp [Bool.and, Bool.or, Bool.not]
    all_goals repeat first|rw [Bool.false_xor]|rw [Bool.true_xor]|dsimp [Bool.not]
    congr; apply ih
    congr; apply ih

def inc_eq_add_one (as: Integer) : as.inc = as + 1 := by
  induction as using bits_induction with
  | nil a => decide +revert
  | cons as a ih =>
    show _ = _ + cons (nil false) true
    rw [add_eq_add_with_carry, step_add_with_carry, step_inc]
    rw [Bool.false_xor, Bool.xor_true]
    congr; cases a <;> dsimp [Bool.and]
    · show _ = as + 0
      rw [add_zero]
    · show _ = add_with_carry true as 0
      rw [add_with_carry_true, add_zero]

def dec_eq_sub_one (as: Integer) : as.dec = as - 1 := by
  show _ = _ + -1
  induction as using bits_induction with
  | nil a => decide +revert
  | cons as a ih =>
    show _ = _ + nil true
    rw [←msb_cons_lsb (nil true), add_eq_add_with_carry, step_add_with_carry, step_dec]
    dsimp; rw [Bool.false_xor, Bool.xor_true]
    congr; cases a <;> dsimp [Bool.and]
    · apply ih
    · show _ = add_with_carry _ _ (-1)
      rw [add_with_carry_true, ←ih, dec_inc]

def Bits.not_not (as: Bits) : as.not.not ≈ as := by
  intro i; rw [get_not, get_not, Bool.not_not]

def not_not (as: Integer) : as.not.not = as := by
  cases as using cases with | mk as =>
  rw [mk_not, mk_not]; apply sound
  apply Bits.not_not

def neg_neg (as: Integer) : - -as = as := by
  induction as using bits_induction with
  | nil => decide +revert
  | cons as a ih =>
    rw [step_neg]; cases a <;> dsimp
    rw [step_neg]; dsimp; rw [ih]
    rw [step_neg]; dsimp; rw [not_not]

def neg_inj {as bs: Integer} : -as = -bs ↔ as = bs := by
  apply Iff.intro
  intro h; rw [←neg_neg as, ←neg_neg bs, h]
  apply congrArg

def neg_inc_eq_not (as: Integer) : -as.inc = as.not := by
  induction as using bits_induction with
  | nil => decide +revert
  | cons as a ih =>
    rw [step_inc]; cases a <;> dsimp
    all_goals
      rw [step_neg]; dsimp [Bool.not]
      rw [step_not]; dsimp [Bool.not]
    rw [ih]

def dec_neg_eq_not (as: Integer) : (-as).dec = as.not := by
  induction as using bits_induction with
  | nil => decide +revert
  | cons as a ih =>
    rw [step_neg]; cases a <;> dsimp
    all_goals
      rw [step_dec]; dsimp [Bool.not]
      rw [step_not]; dsimp [Bool.not]
    rw [ih]

def neg_inc_eq_dec_neg (as: Integer) : -as.inc = (-as).dec := by
  rw [neg_inc_eq_not, dec_neg_eq_not]

def inc_cons_false (a: Integer) : (cons a false).inc = cons a true := by
  apply step_inc
def inc_cons_true (a: Integer) : (cons a true).inc = cons a.inc false := by
  apply step_inc

def natCast_succ (n: ℕ) : (n + 1: ℕ) = (n + 1: Integer) := by
  induction n using nat_div2_rec with
  | base => rfl
  | ind n h ih =>
    rw [step_natCast, step_natCast n, ←inc_eq_add_one]
    rcases nat_mod2_eq_zero_or_one n with h | h
    · rw [h, nat_add_mod, h]; dsimp
      rw [inc_cons_false]; congr 2
      obtain ⟨k, rfl⟩ : 2 ∣ n := by rw [←nat_div_add_mod n 2, h, Nat.add_zero]; apply Nat.dvd_mul_right
      rw [nat_mul_add_div (by decide), Nat.mul_comm, nat_mul_div_left]; rfl
      decide
    · rw [h, nat_add_mod, h]; dsimp
      rw [inc_cons_true, inc_eq_add_one, ←ih]; congr
      rw [Nat.add_comm (n / 2) 1, ←nat_mul_add_div,
        Nat.two_mul, Nat.add_comm _ n, ←Nat.add_assoc]
      obtain ⟨k, hk⟩ : 2 ∣ n + 1 := by rw [←nat_div_add_mod n 2, h,
        Nat.add_assoc, ←Nat.two_mul, ←Nat.mul_add]; apply Nat.dvd_mul_right
      rw [hk, nat_mul_add_div (by decide), Nat.mul_comm, nat_mul_div_left]; rfl
      decide
      decide

instance : IsLawfulNegZero Integer where
  neg_zero := rfl

end Arith

section Order

inductive Bits.IsNonneg : Bits -> Prop where
| nil : IsNonneg (nil false)
| cons (as a) : IsNonneg as -> IsNonneg (cons as a)

inductive Bits.IsNeg : Bits -> Prop where
| nil : IsNeg (nil true)
| cons (as a) : IsNeg as -> IsNeg (cons as a)

def Bits.is_nonneg : Bits -> Bool
| nil a => a == false
| cons as _ => as.is_nonneg

def Bits.is_neg : Bits -> Bool
| nil a => a == true
| cons as _ => as.is_neg

def Bits.is_nonneg_spec {as: Bits} : as.is_nonneg ↔ as.IsNonneg := by
  induction as with
  | nil a =>
    cases a <;> apply Iff.intro
    intro h; apply IsNonneg.nil
    intro; rfl
    nofun; nofun
  | cons as a ih =>
    apply Iff.trans ih
    apply Iff.intro
    apply IsNonneg.cons
    intro h; cases h
    assumption

def Bits.is_neg_spec {as: Bits} : as.is_neg ↔ as.IsNeg := by
  induction as with
  | nil a =>
    cases a <;> apply Iff.intro
    nofun; nofun
    intro h; apply IsNeg.nil
    intro; rfl
  | cons as a ih =>
    apply Iff.trans ih
    apply Iff.intro
    apply IsNeg.cons
    intro h; cases h
    assumption

def IsNonneg (x: Integer) := x.bits.IsNonneg
def IsNeg (x: Integer) := x.bits.IsNeg

instance : Decidable (Bits.IsNonneg a) :=
  decidable_of_bool a.is_nonneg Bits.is_nonneg_spec
instance : Decidable (Bits.IsNeg a) :=
  decidable_of_bool a.is_neg Bits.is_neg_spec

instance : Decidable (IsNonneg a) :=
  inferInstanceAs (Decidable (Bits.IsNonneg _))
instance : Decidable (IsNeg a) :=
  inferInstanceAs (Decidable (Bits.IsNeg _))

private def Bits.eqv_IsNonneg' {as bs: Bits} (h: as ≈ bs) : as.IsNonneg -> bs.IsNonneg := by
  intro g
  induction g generalizing bs with
  | nil =>
    induction bs with
    | nil => cases h 0; apply IsNonneg.nil
    | cons bs b ih =>
      apply IsNonneg.cons
      apply ih
      cases h 0
      apply eqv_nil_cons.mp; assumption
  | cons as a _ ih =>
    cases bs with
    | nil b =>
      cases h 0
      exact ih (eqv_cons_nil.mp h)
    | cons bs b =>
      apply IsNonneg.cons
      apply ih
      cases h 0
      apply eqv_cons.mp; assumption
private def Bits.eqv_IsNeg' {as bs: Bits} (h: as ≈ bs) : as.IsNeg -> bs.IsNeg := by
  intro g
  induction g generalizing bs with
  | nil =>
    induction bs with
    | nil => cases h 0; apply IsNeg.nil
    | cons bs b ih =>
      apply IsNeg.cons
      apply ih
      cases h 0
      apply eqv_nil_cons.mp; assumption
  | cons as a _ ih =>
    cases bs with
    | nil b =>
      cases h 0
      exact ih (eqv_cons_nil.mp h)
    | cons bs b =>
      apply IsNeg.cons
      apply ih
      cases h 0
      apply eqv_cons.mp; assumption
def Bits.eqv_IsNonneg {as bs: Bits} (h: as ≈ bs) : as.IsNonneg ↔ bs.IsNonneg := by
  apply Iff.intro
  apply Bits.eqv_IsNonneg'; assumption
  apply Bits.eqv_IsNonneg'; symm; assumption
def Bits.eqv_IsNeg {as bs: Bits} (h: as ≈ bs) : as.IsNeg ↔ bs.IsNeg := by
  apply Iff.intro
  apply Bits.eqv_IsNeg'; assumption
  apply Bits.eqv_IsNeg'; symm; assumption
def mk_isnonneg (a: Bits) : (mk a).IsNonneg ↔ a.IsNonneg := by
  apply Bits.eqv_IsNonneg
  apply Bits.reduce_eqv
def mk_isneg (a: Bits) : (mk a).IsNeg ↔ a.IsNeg := by
  apply Bits.eqv_IsNeg
  apply Bits.reduce_eqv

def Bits.not_nonneg_and_neg (a: Bits) : a.IsNonneg -> a.IsNeg -> False := by
  intro h g
  induction h with
  | nil => nomatch g
  | cons as a h ih =>
    cases g; apply ih; assumption

def Bits.nonneg_or_neg (a: Bits) : a.IsNonneg ∨ a.IsNeg := by
  induction a with
  | nil a =>
    cases a
    left; apply IsNonneg.nil
    right; apply IsNeg.nil
  | cons as a ih =>
    rcases ih with h | h
    left; apply IsNonneg.cons; assumption
    right; apply IsNeg.cons; assumption

def Bits.nonneg_cons {as: Bits} {a: Bool} : (as.cons a).IsNonneg ↔ as.IsNonneg := by
  apply Iff.intro
  intro h; cases h; assumption
  apply IsNonneg.cons

def Bits.neg_cons {as: Bits} {a: Bool} : (as.cons a).IsNeg ↔ as.IsNeg := by
  apply Iff.intro
  intro h; cases h; assumption
  apply IsNeg.cons

def Bits.not_nonneg_iff_neg {a: Bits} : a.not.IsNonneg ↔ a.IsNeg := by
  induction a with
  | nil a => decide +revert
  | cons as a ih =>
    apply Iff.trans (Bits.eqv_IsNonneg (step_not _))
    dsimp; apply Iff.trans Bits.nonneg_cons
    apply Iff.trans _ Bits.neg_cons.symm
    assumption

def Bits.not_neg_iff_nonneg {a: Bits} : a.not.IsNeg ↔ a.IsNonneg := by
  apply Iff.trans Bits.not_nonneg_iff_neg.symm
  apply Bits.eqv_IsNonneg
  apply Bits.not_not

def Bits.nonpos_of_neg (a: Bits) : a.IsNeg -> (-a).IsNonneg := by
  induction a with
  | nil a => decide +revert
  | cons as a ih =>
    intro h
    apply Bits.eqv_IsNonneg'
    symm; apply step_neg
    cases a <;> dsimp
    apply IsNonneg.cons
    apply ih; cases h; assumption
    apply IsNonneg.cons
    apply not_nonneg_iff_neg.mpr
    cases h; assumption

def nonneg_nil : IsNonneg (nil a) ↔ a = false := by decide +revert
def nonneg_cons : IsNonneg (cons as a) ↔ IsNonneg as := by
  cases as using cases with | mk as =>
  rw [mk_cons]
  apply Iff.trans (mk_isnonneg _)
  apply Iff.trans _ (mk_isnonneg _).symm
  exact Bits.nonneg_cons

instance : LE Integer where
  le a b := IsNonneg (b - a)
instance : LT Integer where
  lt a b := IsNeg (b - a)

def nonneg_or_nonpos (as: Integer) : as.IsNonneg ∨ (-as).IsNonneg := by
  cases as using cases with | mk as =>
  rcases Bits.nonneg_or_neg as with h | h
  left; apply (mk_isnonneg _).mpr; assumption
  right; rw [mk_neg]; apply (mk_isnonneg _).mpr
  apply Bits.nonpos_of_neg
  assumption

def exists_ofNat_of_nonneg (x: Integer) (hx: x.IsNonneg) : ∃n: ℕ, x = n := by
  induction x using bits_induction with
  | nil =>
    cases nonneg_nil.mp hx
    exists 0
  | cons as a ih =>
    obtain ⟨n, rfl⟩ := ih (nonneg_cons.mp hx)
    cases a
    exists n * 2
    rw [step_natCast (n * 2)]
    rw [nat_mul_mod_left, nat_mul_div_left n]
    rfl; decide
    exists n * 2 + 1
    rw [step_natCast (n * 2 + 1)]
    rw [nat_add_mod, nat_mul_mod_left, Nat.zero_add, Nat.mul_comm, nat_mul_add_div]
    rfl; decide

def Bits.nonneg_inc (as: Bits) : as.IsNonneg -> as.inc.IsNonneg := by
  intro h
  induction h with
  | nil =>
    apply IsNonneg.cons
    apply IsNonneg.nil
  | cons as a ih =>
    apply (eqv_IsNonneg (push_bit_spec _ _)).mpr
    apply IsNonneg.cons
    cases a <;> dsimp
    assumption
    assumption
def nonneg_inc (as: Integer) : as.IsNonneg -> as.inc.IsNonneg := Bits.nonneg_inc _

def natCast_nonneg (n: ℕ) : IsNonneg n := by
  induction n using nat_div2_rec with
  | base => apply Bits.IsNonneg.nil
  | ind =>
    rw [step_natCast]
    rw [mk_natCast, mk_cons]
    apply (mk_isnonneg _).mpr
    apply Bits.IsNonneg.cons
    assumption

private def nonneg_induction {motive: ∀as: Integer, as.IsNonneg -> Prop}
  (zero: motive 0 (by decide))
  (inc: ∀(as: Integer) (ha: as.IsNonneg), motive as ha -> motive as.inc (nonneg_inc _ ha))
  (as: Integer) (ha: as.IsNonneg) : motive as ha := by
  obtain ⟨n, rfl⟩ := exists_ofNat_of_nonneg _ ha
  show motive _ (natCast_nonneg _)
  clear ha
  induction n with
  | zero => apply zero
  | succ n ih =>
    conv => { lhs; rw [natCast_succ, ←inc_eq_add_one] }
    apply inc
    assumption

def induction {motive: Integer -> Prop}
  (zero: motive 0)
  (inc: ∀(as: Integer), motive as -> motive as.inc)
  (dec: ∀(as: Integer), motive as -> motive as.dec)
  (x: Integer) : motive x := by
  rcases nonneg_or_nonpos x with h | h
  apply nonneg_induction (motive := fun n _ => motive n)
  apply zero
  intro as h; apply inc
  assumption
  have := nonneg_induction (motive := fun n _ => motive (-n)) (as := -x) ?_ ?_ h
  rwa [neg_neg] at this
  dsimp; rwa [neg_zero]
  intro as ha dsimp
  rw [neg_inc_eq_dec_neg]
  apply dec
  assumption

end Order

end Integer
