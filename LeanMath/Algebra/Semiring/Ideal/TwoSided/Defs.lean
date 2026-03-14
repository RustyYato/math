import LeanMath.Algebra.Semiring.Set
import LeanMath.Algebra.Semiring.Ideal.Defs

structure Ideal (α: Type*) [SemiringOps α] [IsSemiring α] extends AddSubMonoid α, SubLeftMul α, SubRightMul α, SubZero α where

variable [SemiringOps α] [SemiringOps β] [IsSemiring α] [IsSemiring β]

instance : SetLike (Ideal α) α where
instance : IsMemAdd (Ideal α) α where
instance : IsMemLeftMul (Ideal α) α where
instance : IsMemRightMul (Ideal α) α where
instance : IsMemZero (Ideal α) α where

namespace Ideal

@[ext] def ext (a b: Ideal α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext a b

inductive Closure (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure U a
| zero : Closure U 0
| add ⦃a b: α⦄ : Closure U a -> Closure U b -> Closure U (a + b)
| mul_left ⦃a: α⦄ (k: α) : Closure U a -> Closure U (k * a)
| mul_right ⦃a: α⦄ (k: α) : Closure U a -> Closure U (a * k)

def closure (U: Set α) : Ideal α where
  toSet := Set.ofMem (Closure U)
  mem_zero := Closure.zero
  mem_add := Closure.add
  mem_left_mul := Closure.mul_left
  mem_right_mul := Closure.mul_right

def sub_closure (U: Set α) : U ⊆ closure U := by
  intro a
  apply Closure.of

def of_mem_closure [SetLike S α] [IsMemLeftMul S α] [IsMemRightMul S α] [IsMemAdd S α] [IsMemZero S α] (U: Set α) (s: S)
  : (∀{a}, a ∈ U -> a ∈ s) -> ∀{a}, a ∈ closure U -> a ∈ s := by
  intro g a h
  induction h with
  | of =>
    apply g
    assumption
  | zero => apply mem_zero
  | add a b iha ihb =>
    apply mem_add <;> assumption
  | mul_left a iha =>
    apply mem_left_mul <;> assumption
  | mul_right a iha =>
    apply mem_right_mul <;> assumption

instance : Top (Ideal α) where
  top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_add _ _ _ _ := True.intro
    mem_left_mul _ _ _ := True.intro
    mem_right_mul _ _ _ := True.intro
  }

instance : Bot (Ideal α) where
  bot := {
    toSet := {0}
    mem_zero := rfl
    mem_add := by
      rintro _ _ rfl rfl
      rw [add_zero]; rfl
    mem_left_mul := by
      rintro x _ rfl
      rw [mul_zero]; rfl
    mem_right_mul := by
      rintro x _ rfl
      rw [zero_mul]; rfl
  }

def mem_top (a: α) : a ∈ (⊤: Ideal α) := True.intro
def sub_top (a: Ideal α) : a ⊆ ⊤ := fun _ _ => True.intro
def bot_sub (a: Ideal α) : ⊥ ⊆ a := by
  rintro x rfl
  apply mem_zero a

@[simp] def closure_bot_eq_bot : closure (α := α) ⊥ = ⊥ := by
  symm; apply SetLike.ext
  intro a
  apply Iff.intro
  apply bot_sub
  intro h
  apply of_mem_closure _ _ _ h
  nofun

def preimage (f: RingHom α β) (U: Ideal β) : Ideal α where
  toSet := Set.preimage f U
  mem_zero := MemZero.preimage f _
  mem_add := MemAdd.preimage f _
  mem_left_mul := MemLeftMul.preimage f _
  mem_right_mul := MemRightMul.preimage f _

def kernel (f: α →+* β) : Ideal α := preimage f ⊥

end Ideal

private inductive Ideal.Add (A B: Set α) : α -> Prop where
| intro (a b: α) (ha: a ∈ A) (hb: b ∈ B) : Add A B (a + b)

private inductive Ideal.Mul (A B: Set α) : α -> Prop where
| mul (a b: α) (ha: a ∈ A) (hb: b ∈ B) : Mul A B (a * b)
| add (a b: α) : Mul A B a -> Mul A B b -> Mul A B (a + b)

instance : Zero (Ideal α) where
  zero := ⊥
instance : One (Ideal α) where
  one := ⊤

instance : NatCast (Ideal α) where
  natCast
  | 0 => 0
  | _ + 1 => 1

instance : Add (Ideal α) where
  add A B := {
    toSet := { Mem := Ideal.Add A B }
    mem_zero := by
      rw [←zero_add 0]
      apply Ideal.Add.intro
      apply mem_zero A
      apply mem_zero B
    mem_add := by
      rintro _ _ ⟨xa, xb, hxa, hxb⟩ ⟨ya, yb, hya, hyb⟩
      rw [←add_assoc, add_assoc xa, add_comm xb,
        ←add_assoc, add_assoc (_ + _)]
      apply Ideal.Add.intro
      apply mem_add A <;> assumption
      apply mem_add B <;> assumption
    mem_left_mul := by
      rintro a k ⟨a, b, ha, hb⟩
      rw [mul_add]
      apply Ideal.Add.intro
      apply mem_left_mul A <;> assumption
      apply mem_left_mul B <;> assumption
    mem_right_mul := by
      rintro a k ⟨a, b, ha, hb⟩
      rw [add_mul]
      apply Ideal.Add.intro
      apply mem_right_mul A <;> assumption
      apply mem_right_mul B <;> assumption
  }

instance : Mul (Ideal α) where
  mul A B := {
    toSet := { Mem := Ideal.Mul A B }
    mem_zero := by
      rw [←mul_zero 0]
      apply Ideal.Mul.mul
      apply mem_zero A
      apply mem_zero B
    mem_add := by apply Ideal.Mul.add
    mem_left_mul := by
      rintro a k ha
      induction ha with
      | mul =>
        rw [←mul_assoc]
        apply Ideal.Mul.mul
        apply mem_left_mul A
        assumption
        assumption
      | add =>
        rw [mul_add]
        apply Ideal.Mul.add
        assumption
        assumption
    mem_right_mul := by
      rintro a k ha
      induction ha with
      | mul =>
        rw [mul_assoc]
        apply Ideal.Mul.mul
        assumption
        apply mem_right_mul B
        assumption
      | add =>
        rw [add_mul]
        apply Ideal.Mul.add
        assumption
        assumption
  }

instance : SMul ℕ (Ideal α) where
  smul n A := n * A

instance : Pow (Ideal α) ℕ := defaultPowN

instance : IsLawfulZeroAdd (Ideal α) where
  zero_add a := by
    ext x
    apply Iff.intro
    · intro h
      induction h with
      | intro a b ha hb =>
      cases ha; rw [zero_add]
      assumption
    · intro h
      rw [←zero_add x]
      apply Ideal.Add.intro
      apply mem_zero (0: Ideal α)
      assumption
  add_zero a := by
    ext x
    apply Iff.intro
    · intro h
      induction h with
      | intro a b ha hb =>
      cases hb; rw [add_zero]
      assumption
    · intro h
      rw [←add_zero x]
      apply Ideal.Add.intro
      assumption
      apply mem_zero (0: Ideal α)

instance : IsLawfulNatCast (Ideal α) where
  natCast_zero := rfl
  natCast_one := rfl
  natCast_succ n := by
    cases n with
    | zero => symm; apply zero_add
    | succ n =>
      show 1 = 1 + 1
      have (x: α) : x ∈ (1: Ideal α) := True.intro
      apply SetLike.ext
      intro x; simp [this]
      rw [←add_zero x]
      apply Ideal.Add.intro
      apply this
      apply this

instance : IsAddComm (Ideal α) where
  add_comm a b := by
    ext x
    apply Iff.intro
    iterate 2
      intro h
      induction h with
      | intro x y hx hy =>
      rw [add_comm x]
      apply Ideal.Add.intro
      assumption
      assumption
instance [IsComm α] : IsComm (Ideal α) where
  mul_comm a b := by
    ext x
    apply Iff.intro
    iterate 2
      intro h
      induction h with
      | mul x y hx hy =>
        rw [mul_comm x]
        apply Ideal.Mul.mul
        assumption
        assumption
      | add x y hx hy ihx ihy =>
        apply Ideal.Mul.add
        assumption
        assumption

instance : IsMonoid (Ideal α) where
  mul_assoc A B C := by
    ext x
    apply Iff.intro
    · intro h
      induction h with
      | add =>
        apply Ideal.Mul.add
        assumption
        assumption
      | mul a b ha hb =>
        induction ha  with
        | add _ _ _ _ iha ihb =>
          rw [add_mul]
          apply Ideal.Mul.add
          assumption
          assumption
        | mul =>
          rw [mul_assoc]
          apply Ideal.Mul.mul
          assumption
          apply Ideal.Mul.mul
          assumption
          assumption
    · intro h
      induction h with
      | add a b _ _ iha ihb =>
         apply Ideal.Mul.add
         assumption
         assumption
      | mul a b ha hb =>
        induction hb with
        | add _ _ _ _ iha ihb =>
          rw [mul_add]
          apply Ideal.Mul.add
          assumption
          assumption
        | mul =>
          rw [←mul_assoc]
          apply Ideal.Mul.mul
          apply Ideal.Mul.mul
          iterate 3 assumption
  one_mul A := by
    symm; ext x
    apply Iff.intro
    intro h
    rw [←one_mul x]
    apply Ideal.Mul.mul
    trivial
    assumption
    intro h
    induction h with
    | add a b _ _ iha ihb => apply mem_add A <;> assumption
    | mul =>
      apply mem_left_mul A
      assumption
  mul_one A := by
    symm; ext x
    apply Iff.intro
    intro h
    rw [←mul_one x]
    apply Ideal.Mul.mul
    assumption
    trivial
    intro h
    induction h with
    | add a b _ _ iha ihb => apply mem_add A <;> assumption
    | mul =>
      apply mem_right_mul A
      assumption

instance : IsLeftDistrib (Ideal α) where
  mul_add K A B := by
    ext x
    apply Iff.intro
    · intro h
      induction h with
      | add =>
        apply mem_add
        assumption
        assumption
      | mul k x hk hx =>
        cases hx with | intro a b ha hb  =>
        rw [mul_add]
        apply Ideal.Add.intro
        apply Ideal.Mul.mul
        assumption
        assumption
        apply Ideal.Mul.mul
        assumption
        assumption
    · intro h
      cases h with | intro a b ka kb =>
      suffices ∀(A B: Ideal α) (a: α), a ∈ K * A -> a ∈ K * (A + B) by
        apply Ideal.Mul.add
        apply this
        assumption
        rw [add_comm A B]
        apply this
        assumption
      clear a b A B ka kb
      intro A B a ha
      induction ha with
      | add =>
        apply Ideal.Mul.add
        assumption
        assumption
      | mul k a =>
        apply Ideal.Mul.mul
        assumption
        rw [←add_zero a]
        apply Ideal.Add.intro
        assumption
        apply mem_zero B

instance : IsRightDistrib (Ideal α) where
  add_mul A B K := by
    ext x
    apply Iff.intro
    · intro h
      induction h with
      | add =>
        apply mem_add
        assumption
        assumption
      | mul x k hx hk =>
        cases hx with | intro a b ha hb  =>
        rw [add_mul]
        apply Ideal.Add.intro
        apply Ideal.Mul.mul
        assumption
        assumption
        apply Ideal.Mul.mul
        assumption
        assumption
    · intro h
      cases h with | intro a b ka kb =>
      suffices ∀(A B: Ideal α) (a: α), a ∈ A * K -> a ∈ (A + B) * K by
        apply Ideal.Mul.add
        apply this
        assumption
        rw [add_comm A B]
        apply this
        assumption
      clear a b A B ka kb
      intro A B a ha
      induction ha with
      | add =>
        apply Ideal.Mul.add
        assumption
        assumption
      | mul a k =>
        apply Ideal.Mul.mul
        rw [←add_zero a]
        apply Ideal.Add.intro
        assumption
        apply mem_zero B
        assumption

instance : IsLawfulZeroMul (Ideal α) where
  zero_mul A := by
    symm; ext x
    apply Iff.intro
    intro rfl
    apply mem_zero
    intro h
    induction h with
    | add => apply mem_add <;> assumption
    | mul a b ha hb =>
      subst a; rw [zero_mul]
      apply mem_zero
  mul_zero A := by
    symm; ext x
    apply Iff.intro
    intro rfl
    apply mem_zero
    intro h
    induction h with
    | add => apply mem_add <;> assumption
    | mul a b ha hb =>
      subst b; rw [mul_zero]
      apply mem_zero

instance : IsAddMonoid (Ideal α) where
  add_assoc A B C := by
    ext x
    apply Iff.intro
    · intro ⟨_, c, ⟨a, b, ha, hb⟩, hc⟩
      rw [add_assoc]
      apply Ideal.Add.intro
      assumption
      apply Ideal.Add.intro
      assumption
      assumption
    · intro ⟨a, _, ha, ⟨b, c, hb, hc⟩⟩
      rw [←add_assoc]
      apply Ideal.Add.intro
      apply Ideal.Add.intro
      assumption
      assumption
      assumption
  zero_nsmul := by apply zero_mul
  succ_nsmul n A := by
    show (n + 1: ℕ) * A = n * A + A
    rw [natCast_succ, add_mul, one_mul]

instance : IsSemiring (Ideal α) where
