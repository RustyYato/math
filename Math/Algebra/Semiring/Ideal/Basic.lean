module

public import Math.Algebra.Semiring.Ideal.Defs
public import Math.Algebra.DirectSum.Defs

namespace Math

namespace Ideal

variable [AddMonoidOps α] [Mul α] [IsNonUnitalSemiring α]

inductive IdealAdd (A B: Set α) : α -> Prop where
| add {a b: α} : a ∈ A -> b ∈ B -> IdealAdd A B (a + b)

public def multiplier (A B: Ideal α) : FreeAddMonoid (A × B) →+ α :=
  FreeAddMonoid.lift fun i => i.fst.val * i.snd.val

@[simp] public theorem multiplier_ι (A B: Ideal α) (x: A × B) :
  multiplier A B (FreeAddMonoid.ι x) = x.fst.val * x.snd.val := by
  unfold multiplier
  rw [FreeAddMonoid.lift_ι]

public instance : Zero (Ideal α) where
  zero := ⊥
public instance : One (Ideal α) where
  one := ⊤
public instance : NatCast (Ideal α) where
  natCast
  | 0 => ⊥
  | _ + 1 => ⊤

public def add (A B: Ideal α) : Ideal α where
  toSet := { Mem := IdealAdd A B }
  mem_zero := by
    show IdealAdd A B (0: α)
    rw [←add_zero 0]; apply IdealAdd.add
    exact mem_zero A
    exact mem_zero B
  mem_add := by
    intro a b ha hb
    cases ha; cases hb
    rename_i a b _ _ c d _ _
    rw [add_assoc, ←add_assoc b, add_comm b, add_assoc, ←add_assoc]
    apply IdealAdd.add
    apply mem_add A <;> assumption
    apply mem_add B <;> assumption
  mem_mul_left := by
    intro k b hb; cases hb
    rename_i a b _ _
    rw [mul_add]; apply IdealAdd.add
    apply mem_mul_left A; assumption
    apply mem_mul_left B; assumption
  mem_mul_right := by
    intro k b hb; cases hb
    rename_i a b _ _
    rw [add_mul]; apply IdealAdd.add
    apply mem_mul_right A; assumption
    apply mem_mul_right B; assumption

public def mul (A B: Ideal α) : Ideal α where
  toSet := Set.range (multiplier A B)
  mem_zero := by
    apply Set.mem_range.mpr
    exists 0
    rw [map_zero]
  mem_add := by
    intro a b ha hb; simp at ha hb
    obtain ⟨as, rfl⟩ := ha
    obtain ⟨bs, rfl⟩ := hb
    rw [←map_add]
    apply Set.mem_range'
  mem_mul_left := by
    intro k a ha; simp at *
    obtain ⟨as, rfl⟩ := ha
    exists as.map (fun (a, b) => (⟨k * a, mem_mul_left A _ a.property⟩, b))
    dsimp; induction as with
    | zero => simp [map_zero, mul_zero]
    | ι => simp [mul_assoc]
    | add a b ha hb => simp [map_add, ha, hb, mul_add]
  mem_mul_right := by
    intro k a ha; simp at *
    obtain ⟨as, rfl⟩ := ha
    exists as.map (fun (a, b) => (a, ⟨b * k, mem_mul_right B _ b.property⟩))
    dsimp; induction as with
    | zero => simp [map_zero, zero_mul]
    | ι => simp [mul_assoc]
    | add a b ha hb => simp [map_add, ha, hb, add_mul]

public instance : Add (Ideal α) where
  add := add
public instance : Mul (Ideal α) where
  mul := mul

public theorem mem_ideal_add {A B: Ideal α} : ∀x, x ∈ A + B ↔ ∃a b, a ∈ A ∧ b ∈ B ∧ x = a + b := by
  intro x; apply Iff.intro
  intro ⟨ha, hb⟩
  refine ⟨_, _, ha, hb, rfl⟩
  rintro ⟨a, b, ha, hb, rfl⟩
  apply IdealAdd.add <;> assumption
public theorem mem_ideal_add' {A B: Ideal α} : a ∈ A -> b ∈ B -> a + b ∈ A + B := IdealAdd.add
public theorem mem_ideal_mul {A B: Ideal α} : ∀x, x ∈ A * B ↔ x ∈ Set.range (multiplier A B) := by
  intro; rfl
public theorem mem_ideal_mul' {A B: Ideal α} : a ∈ A -> b ∈ B -> a * b ∈ A * B := by
  intro ha hb
  simp [mem_ideal_mul]
  exists FreeAddMonoid.ι (⟨a, ha⟩, ⟨b, hb⟩)
  simp
@[simp] public theorem mem_ideal_zero : ∀x, x ∈ (0: Ideal α) ↔ x = 0 := by
  intro; apply Iff.intro <;> apply Eq.symm
@[simp] public theorem mem_ideal_one : ∀x, x ∈ (1: Ideal α) := by
  intro; trivial

public instance : IsLawfulZero (Ideal α) where
  add_zero A := by ext x; simp [add_zero, mem_ideal_add]
  zero_add A := by ext x; simp [zero_add, mem_ideal_add]

public instance : IsAddComm (Ideal α) where
  add_comm a b := by
    ext x; simp [mem_ideal_add]
    apply Iff.intro
    iterate 2
    rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨b, hb, a, ha, ?_⟩
    rw [add_comm]
public instance : IsAddSemigroup (Ideal α) where
  add_assoc A B C := by
    ext x; simp [mem_ideal_add]
    apply Iff.intro
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
      refine ⟨a, ha, _, ⟨b, hb, c, hc, rfl⟩, ?_⟩
      rw [add_assoc]
    · rintro ⟨a, ha, _, ⟨b, hb, c, hc, rfl⟩, rfl⟩
      refine ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, ?_⟩
      rw [add_assoc]

public instance : SMul ℕ (Ideal α) :=
  DefaultNSMul.instSMulNat_math
public instance : IsLawfulNSMul (Ideal α) :=
  DefaultNSMul.instIsLawfulNSMul
public instance : IsAddMonoidWithOne (Ideal α) where
  natCast_zero := rfl
  natCast_succ n := by
    ext x; simp [mem_ideal_add]
    show True ↔ _
    simp
    exists 0; apply And.intro; apply mem_zero
    exists x; rw [zero_add]

public instance : IsLeftDistrib (Ideal α) where
  mul_add K A B := by
    ext x
    apply Iff.intro
    · intro h; simp [mem_ideal_mul] at h; obtain ⟨xs, rfl⟩ := h
      induction xs with
      | zero =>
        rw [map_zero, ←add_zero 0]
        apply mem_ideal_add' <;> apply mem_zero
      | add a b ha hb =>
        rw [map_add]
        apply mem_add <;> assumption
      | ι x =>
        rw [multiplier_ι]
        obtain ⟨⟨k, hk⟩, x, hx⟩ := x
        dsimp; obtain ⟨a, b, ha, hb, rfl⟩ := (mem_ideal_add _).mp hx
        rw [mul_add]
        apply mem_ideal_add'
        <;> apply mem_ideal_mul'
        <;> assumption
    · intro ⟨ha, hb⟩; rename_i a b
      replace ha := (mem_ideal_mul _).mp ha; simp at ha; obtain ⟨as, rfl⟩ := ha
      replace hb := (mem_ideal_mul _).mp hb; simp at hb; obtain ⟨bs, rfl⟩ := hb
      have multiplier_mem (A B: Ideal α) (x) : K.multiplier B x ∈ K * (A + B) := by
        induction x with
        | zero => rw [map_zero]; apply mem_zero
        | add => rw [map_add]; apply mem_add <;> assumption
        | ι x =>
          simp
          apply mem_ideal_mul'
          apply Subtype.property
          rw [←zero_add x.snd.val]
          apply mem_ideal_add'
          apply mem_zero
          apply Subtype.property
      apply mem_add
      rw [add_comm A B]
      apply multiplier_mem B A
      apply multiplier_mem
public instance : IsRightDistrib (Ideal α) where
  add_mul A B K := by
    ext x
    apply Iff.intro
    · intro h; simp [mem_ideal_mul] at h; obtain ⟨xs, rfl⟩ := h
      induction xs with
      | zero =>
        rw [map_zero, ←add_zero 0]
        apply mem_ideal_add' <;> apply mem_zero
      | add a b ha hb =>
        rw [map_add]
        apply mem_add <;> assumption
      | ι x =>
        rw [multiplier_ι]
        obtain ⟨⟨x, hx⟩, k, hk⟩ := x
        dsimp; obtain ⟨a, b, ha, hb, rfl⟩ := (mem_ideal_add _).mp hx
        rw [add_mul]
        apply mem_ideal_add'
        <;> apply mem_ideal_mul'
        <;> assumption
    · intro ⟨ha, hb⟩; rename_i a b
      replace ha := (mem_ideal_mul _).mp ha; simp at ha; obtain ⟨as, rfl⟩ := ha
      replace hb := (mem_ideal_mul _).mp hb; simp at hb; obtain ⟨bs, rfl⟩ := hb
      have multiplier_mem (A B: Ideal α) (x) : B.multiplier K x ∈ (A + B) * K := by
        induction x with
        | zero => rw [map_zero]; apply mem_zero
        | add => rw [map_add]; apply mem_add <;> assumption
        | ι x =>
          simp
          apply mem_ideal_mul'
          rw [←zero_add x.fst.val]
          apply mem_ideal_add'
          apply mem_zero
          apply Subtype.property
          apply Subtype.property
      apply mem_add
      rw [add_comm A B]
      apply multiplier_mem B A
      apply multiplier_mem

public instance : IsLawfulZeroMul (Ideal α) where
  zero_mul A := by
    ext x; simp [mem_ideal_mul]
    symm; apply Iff.intro
    · intro rfl; exists 0; rw [map_zero]
    · rintro ⟨as, rfl⟩
      induction as with
      | zero => rw [map_zero]
      | add _ _ iha ihb => rw [map_add, iha, ihb, add_zero]
      | ι x =>
        obtain ⟨⟨a, ha⟩, b, hb⟩ := x
        simp; rw [←ha, zero_mul]
  mul_zero A := by
    ext x; simp [mem_ideal_mul]
    symm; apply Iff.intro
    · intro rfl; exists 0; rw [map_zero]
    · rintro ⟨as, rfl⟩
      induction as with
      | zero => rw [map_zero]
      | add _ _ iha ihb => rw [map_add, iha, ihb, add_zero]
      | ι x =>
        obtain ⟨⟨a, ha⟩, b, hb⟩ := x
        simp; rw [←hb, mul_zero]

public instance : IsSemigroup (Ideal α) where
  mul_assoc A B C := by
    ext x; apply Iff.intro <;> (intro h; simp [mem_ideal_mul] at h)
    · obtain ⟨as, rfl⟩ := h
      induction as with
      | zero => rw [map_zero]; apply mem_zero
      | add a b iha ihb =>  rw [map_add]; apply mem_add <;> assumption
      | ι x =>
        simp; obtain ⟨⟨x, h⟩, c, hc⟩ := x
        replace h : x ∈ A * B := h
        dsimp; simp [mem_ideal_mul] at h
        obtain ⟨as, rfl⟩ := h; clear h
        induction as with
        | zero => rw [map_zero, zero_mul]; apply mem_zero
        | add => rw [map_add, add_mul]; apply mem_add <;> assumption
        | ι x =>
          simp; obtain ⟨⟨a, ha⟩, b, hb⟩ := x
          dsimp; rw [mul_assoc]
          apply mem_ideal_mul'
          assumption
          apply mem_ideal_mul'
          assumption
          assumption
    · obtain ⟨as, rfl⟩ := h
      induction as with
      | zero => rw [map_zero]; apply mem_zero
      | add a b iha ihb =>  rw [map_add]; apply mem_add <;> assumption
      | ι x =>
        simp; obtain ⟨⟨a, ha⟩, x, h⟩ := x
        replace h : x ∈ B * C := h
        dsimp; simp [mem_ideal_mul] at h
        obtain ⟨as, rfl⟩ := h; clear h
        induction as with
        | zero => rw [map_zero, mul_zero]; apply mem_zero
        | add => rw [map_add, mul_add]; apply mem_add <;> assumption
        | ι x =>
          simp; obtain ⟨⟨b, hb⟩, c, hc⟩ := x
          dsimp; rw [←mul_assoc]
          apply mem_ideal_mul'
          apply mem_ideal_mul'
          assumption
          assumption
          assumption

public instance : IsNonUnitalSemiring (Ideal α) where

variable [One α] [IsLawfulOne α]

public instance : IsLawfulOne (Ideal α) where
  mul_one A := by
    ext x; simp [mem_ideal_mul]
    symm; apply Iff.intro
    · intro hx
      let x' : Set.toType A := ⟨x, hx⟩
      exists FreeAddMonoid.ι (x', ⟨1, True.intro⟩)
      simp [mul_one]; rfl
    rintro ⟨ms, rfl⟩
    induction ms with
    | zero => simp [map_zero]; apply mem_zero
    | add => simp [map_add]; apply mem_add <;> assumption
    | ι =>
      simp
      apply mem_mul_right
      apply Subtype.property
  one_mul A := by
    ext x; simp [mem_ideal_mul]
    symm; apply Iff.intro
    · intro hx
      let x' : Set.toType A := ⟨x, hx⟩
      exists FreeAddMonoid.ι (⟨1, True.intro⟩, x')
      simp [one_mul]; rfl
    rintro ⟨ms, rfl⟩
    induction ms with
    | zero => simp [map_zero]; apply mem_zero
    | add => simp [map_add]; apply mem_add <;> assumption
    | ι =>
      simp
      apply mem_mul_left
      apply Subtype.property

public instance : Pow (Ideal α) ℕ := DefaultPowN.instPowNat
public instance : IsLawfulPowN (Ideal α) := DefaultPowN.instIsLawfulPowN
public instance : IsSemiring (Ideal α) where

end Ideal
