import LeanMath.Tactic.TypeStar

inductive POption (α: Sort u) where
| none
| some (a: α)

namespace POption

variable {α β1: Sort*}

def get (a: POption α) (h: a ≠ .none) : α :=
  match a with
  | .some x => x
  | .none => nomatch h rfl

def get_inj {a b: POption α} {ha: a ≠ .none} {hb: b ≠ .none} : a.get ha = b.get hb ↔ a = b := by
  cases a; contradiction
  cases b; contradiction
  rename_i a b
  show a = b ↔ _
  apply Iff.intro _ POption.some.inj
  apply congrArg

@[simp] def get_some (a: α) {h} : get (.some a) h = a := rfl

@[simp] def some_get (a: POption α) {h} : POption.some (get a h) = a := by cases a; contradiction; rfl

def isSome : POption α -> Bool
| .some _ => true
| .none => false

def and_then (f: α -> POption β) : POption α -> POption β
| .some a => f a
| .none => .none

@[simp] def and_then_none (f: α -> POption β) : and_then f .none = .none := rfl
@[simp] def and_then_some (f: α -> POption β) (a: α) : and_then f (.some a) = f a := rfl

instance: Monad POption where
  pure := .some
  bind := flip and_then

def map (f: α -> β) := and_then (.some ∘ f)

end POption
