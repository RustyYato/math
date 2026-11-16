module

public import Math.Order.Defs

@[expose] section

namespace Math

public inductive Kind where
| sprop
| prop
| type
| param (id: ℕ)
| trunc (a: Kind)
| max (a b: Kind)

public inductive Level where
| zero
| param (id : ℕ)
| succ (l : Level)
| when (k: Kind) (l : Level)
| max (a b : Level)

public structure Universe where
  kind: Kind
  level: Level

public inductive ConcreteKind where
| sprop
| prop
| type
deriving DecidableEq

namespace ConcreteKind

public protected inductive LE : ConcreteKind -> ConcreteKind -> Prop where
| sprop : ConcreteKind.LE .sprop a
| prop : ConcreteKind.LE .prop .prop
| type : ConcreteKind.LE a .type

public protected inductive LT : ConcreteKind -> ConcreteKind -> Prop where
| sprop_prop : ConcreteKind.LT .sprop .prop
| sprop_type : ConcreteKind.LT .sprop .type
| prop_type : ConcreteKind.LT .prop .type

public instance : LE ConcreteKind where
  le := ConcreteKind.LE
public instance : LT ConcreteKind where
  lt := ConcreteKind.LT

public def ConcreteKind.any (f: ConcreteKind -> Bool) : Bool :=
  f .sprop || f .prop || f .type

public def ConcreteKind.all (f: ConcreteKind -> Bool) : Bool :=
  f .sprop && f .prop && f .type

theorem bool_or_eq_true_iff {a b: Bool} : a || b ↔ a ∨ b := by decide +revert

theorem bool_and_eq_true_iff {a b: Bool} : a && b ↔ a ∧ b := by decide +revert

public instance (P: ConcreteKind -> Prop) [DecidablePred P] : Decidable (∃c, P c) :=
  decidable_of_bool (ConcreteKind.any fun c => decide (P c)) <| by
    unfold ConcreteKind.any
    apply Iff.intro
    · intro h; dsimp at h
      rcases bool_or_eq_true_iff.mp h with h | h
      rcases bool_or_eq_true_iff.mp h with h | h
      all_goals replace h := of_decide_eq_true h
      exists .sprop
      exists .prop
      exists .type
    · intro ⟨c, p⟩; dsimp; cases c
      all_goals rw [decide_eq_true p]
      rfl; rw [Bool.or_true]; rfl
      rw [Bool.or_true]

public instance (P: ConcreteKind -> Prop) [DecidablePred P] : Decidable (∀c, P c) :=
  decidable_of_iff (ConcreteKind.all fun c => decide (P c)) <| by
    unfold ConcreteKind.all
    apply Iff.intro
    · intro h; dsimp at h
      have ⟨h, htype⟩ := bool_and_eq_true_iff.mp h
      have ⟨hsprop, hprop⟩ := bool_and_eq_true_iff.mp h
      intro c; cases c <;> (apply of_decide_eq_true; assumption)
    · intro h; dsimp
      apply bool_and_eq_true_iff.mpr; apply And.intro
      apply bool_and_eq_true_iff.mpr; apply And.intro
      all_goals
        apply decide_eq_true
        apply h

public def ble : ConcreteKind -> ConcreteKind -> Bool
| .sprop, _
| .prop, .prop
| _, .type => true
| .prop, .sprop
| .type, .sprop
| .type, .prop => false

public def blt : ConcreteKind -> ConcreteKind -> Bool
| .sprop, .prop
| .sprop, .type
| .prop, .type => true
| .sprop, .sprop
| .prop, .prop
| .type, .type
| .prop, .sprop
| .type, .sprop
| .type, .prop => false

public theorem ble_iff_le {a b: ConcreteKind} : a.ble b ↔ a ≤ b := by
  cases a <;> cases b
  any_goals
    apply Iff.intro
    intro; contradiction
    intro; contradiction
  any_goals apply Iff.intro (fun _ => ?_) (fun _ => rfl)
  any_goals apply ConcreteKind.LE.sprop
  any_goals apply ConcreteKind.LE.type
  apply ConcreteKind.LE.prop

public theorem blt_iff_lt {a b: ConcreteKind} : a.blt b ↔ a < b := by
  cases a <;> cases b
  any_goals
    apply Iff.intro
    intro; contradiction
    intro; contradiction
  any_goals apply Iff.intro (fun _ => ?_) (fun _ => rfl)
  apply ConcreteKind.LT.sprop_prop
  apply ConcreteKind.LT.sprop_type
  apply ConcreteKind.LT.prop_type

public instance (a b: ConcreteKind) : Decidable (a ≤ b) :=
  decidable_of_bool (a.ble b) ble_iff_le

public instance (a b: ConcreteKind) : Decidable (a < b) :=
  decidable_of_bool (a.blt b) blt_iff_lt

public instance : IsPartialOrder ConcreteKind where
  lt_iff_le_and_not_ge := by decide
  refl := by decide
  htrans := by decide
  antisymm := by decide

public def trunc : ConcreteKind -> ConcreteKind
| .sprop => .sprop
| .prop | .type => .prop

public def max (a b: ConcreteKind) : ConcreteKind :=
  if a ≤ b then b else a

public instance : Max ConcreteKind where
  max := max

public instance : IsSupSemilattice ConcreteKind where
  left_le_max := by decide
  right_le_max := by decide
  max_le := by decide

public instance : Bot ConcreteKind where
  bot := .sprop
public instance : Top ConcreteKind where
  top := .type
public instance : IsLawfulBot ConcreteKind where
  bot_le _ := .sprop
public instance : IsLawfulTop ConcreteKind where
  le_top _ := .type

public theorem trunc_lt_type (c: ConcreteKind) : c.trunc < .type := by decide +revert
public theorem trunc_le_prop (c: ConcreteKind) : c.trunc ≤ .prop := by decide +revert
@[simp] public theorem max_type (a: ConcreteKind) : a ⊔ .type = .type := by decide +revert
@[simp] public theorem type_max (a: ConcreteKind) : .type ⊔ a = .type := by decide +revert
@[simp] public theorem max_sprop (a: ConcreteKind) : a ⊔ .sprop = a := by decide +revert
@[simp] public theorem sprop_max (a: ConcreteKind) : .sprop ⊔ a = a := by decide +revert
@[simp] public theorem max_self (a: ConcreteKind) : a ⊔ a = a := by decide +revert

end ConcreteKind

namespace Kind

public def eval (f: ℕ -> ConcreteKind) : Kind -> ConcreteKind
| .sprop => .sprop
| .prop => .prop
| .type => .type
| .param i => f i
| .trunc a => (a.eval f).trunc
| .max a b => (a.eval f).max (b.eval f)

/-- This is the grand truth, and every potential kind order
  must be a sub-relation of this one. However, this relation
  is extremely difficult to check in linear time, so
  it's not suitable for a theorem prover -/
public def eval_le (a b: Kind) : Prop :=
  ∀(f: ℕ -> ConcreteKind), a.eval f ≤ b.eval f

end Kind

namespace Level

public def eval (k: ℕ -> ConcreteKind) (f: ℕ -> ℕ) : Level -> ℕ
| .zero => 0
| .succ l => l.eval k f + 1
| .param i => f i
| .max a b => (a.eval k f).max (b.eval k f)
| .when a b =>
  match a.eval k with
  | .sprop | .prop => 0
  | .type => b.eval k f

/-- This is the grand truth, and every potential kind order
  must be a sub-relation of this one. However, this relation
  is extremely difficult to check in linear time, so
  it's not suitable for a theorem prover -/
public def eval_le (a b: Level) : Prop :=
  ∀(k: ℕ -> ConcreteKind) (f: ℕ -> ℕ), a.eval k f ≤ b.eval k f

end Level

namespace Universe

public def eval (k: ℕ -> ConcreteKind) (f: ℕ -> ℕ) (u: Universe) : ℕ :=
  match u.kind.eval k with
  | .sprop => 0
  | .prop => 1
  | .type  => u.level.eval k f + 2

/-- This is the grand truth, and every potential kind order
  must be a sub-relation of this one. However, this relation
  is extremely difficult to check in linear time, so
  it's not suitable for a theorem prover -/
public def eval_le (a b: Universe) : Prop :=
  ∀(k: ℕ -> ConcreteKind) (f: ℕ -> ℕ), a.eval k f ≤ b.eval k f

end Universe

end Math
