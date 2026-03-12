import LeanMath.Tactic.TypeStar

inductive POption (α: Sort u) where
| none
| some (a: α)

namespace POption

variable {α: Sort*}

def get (a: POption α) (h: a ≠ .none) : α :=
  match a with
  | .some x => x
  | .none => nomatch h rfl

@[simp] def get_some (a: α) {h} : get (.some a) h = a := rfl

def isSome : POption α -> Bool
| .some _ => true
| .none => false

end POption
