import LeanMath.Tactic.TypeStar

class CheckedInv (α: Type*) (P: α -> Prop) where
  protected checked_inv (a: α) (p: P a) : α

class CheckedMod (α: Type*) (P: α -> Prop) where
  protected checked_mod (a b: α) (p: P b) : α

class CheckedDiv (α: Type*) (P: α -> Prop) where
  protected checked_div (a b: α) (p: P b) : α

class CheckedZPow (α: Type*) (P: α -> Prop) where
  protected checked_pow (a: α) (n: ℤ) (p: 0 ≤ n ∨ P a) : α

syntax "invert_tactic" : tactic
syntax "invert_tactic_trivial" : tactic
syntax "pow_tactic" : tactic
syntax "pow_tactic_from_invert" : tactic
syntax "pow_tactic_trivial" : tactic

def pow_from_invert_helper (P Q: α -> Prop) (n: ℕ) (a: α) (h: 0 ≤ n ∨ P a) (g: P a -> Q a) : 0 ≤ n ∨ Q a := by
  cases h
  left; assumption
  right; apply g
  assumption

macro_rules
| `(tactic|invert_tactic) => `(tactic|first|assumption|trivial|invert_tactic_trivial)
| `(tactic|pow_tactic) => `(tactic|first|assumption|trivial|pow_tactic_from_invert|pow_tactic_trivial)
| `(tactic|pow_tactic_from_invert) => `(tactic|apply pow_from_invert_helper; assumption; invert_tactic)

syntax:max term noWs "⁻¹?" : term
syntax:70 term:70 "%?" term:71 : term
syntax:70 term:70 "/?" term:71 : term
syntax:70 term:70 "^?" term:71 : term

syntax:max term noWs "⁻¹?" "~(" term ")" : term
syntax:70 term:70 "%?" term:71 "~(" term ")" : term
syntax:70 term:70 "/?" term:71 "~(" term ")" : term
syntax:70 term:70 "^?" term:71 "~(" term ")" : term

macro_rules
| `($x⁻¹?) => `(CheckedInv.checked_inv $x (by invert_tactic))
| `($x /? $y) => `(CheckedDiv.checked_div $x $y (by invert_tactic))
| `($x %? $y) => `(CheckedMod.checked_mod $x $y (by invert_tactic))
| `($x ^? $y) => `(CheckedZPow.checked_pow $x $y (by pow_tactic))

| `($x⁻¹? ~($prf)) => `(CheckedInv.checked_inv $x $prf)
| `($x /? $y ~($prf)) => `(CheckedDiv.checked_div $x $y $prf)
| `($x %? $y ~($prf)) => `(CheckedMod.checked_mod $x $y $prf)
| `($x ^? $y ~($prf)) => `(CheckedZPow.checked_pow $x $y $prf)
