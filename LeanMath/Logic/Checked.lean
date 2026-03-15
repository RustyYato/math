import LeanMath.Tactic.TypeStar

class CheckedInv (α: Type*) (P: outParam <| α -> Prop) where
  protected checked_inv (a: α) (p: P a) : α

class CheckedMod (α: Type*) (P: outParam <| α -> Prop) where
  protected checked_mod (a b: α) (p: P b) : α

class CheckedDiv (α: Type*) (P: outParam <| α -> Prop) where
  protected checked_div (a b: α) (p: P b) : α

class CheckedZPow (α: Type*) (P: outParam <| α -> Prop) where
  protected checked_pow (a: α) (n: ℤ) (p: 0 ≤ n ∨ P a) : α

abbrev CheckedInv? (α: Type*) [Zero α] := CheckedInv α (· ≠ 0)
abbrev CheckedDiv? (α: Type*) [Zero α] := CheckedDiv α (· ≠ 0)
abbrev CheckedMod? (α: Type*) [Zero α] := CheckedMod α (· ≠ 0)
abbrev CheckedZPow? (α: Type*) [Zero α] := CheckedZPow α (· ≠ 0)

syntax "invert_tactic" : tactic
syntax "invert_tactic_trivial" : tactic
syntax "invert_tactic_trivial_low_priority" : tactic
syntax "pow_tactic" : tactic
syntax "pow_tactic_from_invert" : tactic
syntax "pow_tactic_trivial" : tactic

def pow_from_invert_helper (P Q: Prop) (n: ℤ) (h: 0 ≤ n ∨ P) (g: P -> Q) : 0 ≤ n ∨ Q := by
  cases h
  left; assumption
  right; apply g
  assumption

def pow_from_invert (P: Prop) (n: ℤ) (h: P) : 0 ≤ n ∨ P := by
  right
  assumption

def inv_from_pow_negSucc (P: α -> Prop) (n: ℕ) (a: α) (h: 0 ≤ Int.negSucc n ∨ P a) : P a := by
  cases h
  contradiction
  assumption

def pow_of_natCast (P: α -> Prop) (n: ℕ) (a: α) : 0 ≤ (n: ℤ) ∨ P a := by
  left; apply Int.zero_le_ofNat

def pow_of_negSucc (P: α -> Prop) (n: ℕ) (a: α) (h: P a) : 0 ≤ (Int.negSucc n) ∨ P a := by
  right; assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply inv_from_pow_negSucc <;> assumption)
| `(tactic|invert_tactic_trivial_low_priority) => `(tactic|assumption)
| `(tactic|invert_tactic) => `(tactic|first|assumption|trivial|invert_tactic_trivial|invert_tactic_trivial_low_priority)
| `(tactic|pow_tactic) => `(tactic|first|assumption|trivial|pow_tactic_from_invert|pow_tactic_trivial)
| `(tactic|pow_tactic_from_invert) => `(tactic|
  apply pow_from_invert_helper;
  assumption;
  intro;
  invert_tactic)

macro_rules
| `(tactic|pow_tactic_trivial) => `(tactic|apply pow_from_invert <;> invert_tactic)
macro_rules
| `(tactic|pow_tactic_trivial) => `(tactic|apply pow_of_natCast)
macro_rules
| `(tactic|pow_tactic_trivial) => `(tactic|apply pow_of_negSucc; invert_tactic)

syntax:max term noWs "⁻¹?" : term
syntax:70 term:70 " %? " term:71 : term
syntax:70 term:70 " /? " term:71 : term
syntax:80 term:80 " ^? " term:81 : term

syntax:max term noWs "⁻¹?" "~(" term ")" : term
syntax:70 term:70 " %? " term:71 " ~(" term ")" : term
syntax:70 term:70 " /? " term:71 " ~(" term ")" : term
syntax:70 term:70 " ^? " term:71 " ~(" term ")" : term

macro_rules
| `($x⁻¹?) => `(CheckedInv.checked_inv $x (by invert_tactic))
| `($x /? $y) => `(CheckedDiv.checked_div $x $y (by invert_tactic))
| `($x %? $y) => `(CheckedMod.checked_mod $x $y (by invert_tactic))
| `($x ^? $y) => `(CheckedZPow.checked_pow $x $y (by pow_tactic))

| `($x⁻¹? ~($prf)) => `(CheckedInv.checked_inv $x $prf)
| `($x /? $y ~($prf)) => `(CheckedDiv.checked_div $x $y $prf)
| `($x %? $y ~($prf)) => `(CheckedMod.checked_mod $x $y $prf)
| `($x ^? $y ~($prf)) => `(CheckedZPow.checked_pow $x $y $prf)

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.CheckedDiv.checked_div]
def delab_checked_div : Delab := do
  let expr ← getExpr
  let #[_, _, _, x, y, _] := expr.getAppArgs | failure
  let x ← delab x
  let y ← delab y
  `($x /? $y)

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.CheckedMod.checked_mod]
def delab_checked_mod : Delab := do
  let expr ← getExpr
  let #[_, _, _, x, y, _] := expr.getAppArgs | failure
  let x ← delab x
  let y ← delab y
  `($x %? $y)

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.CheckedInv.checked_inv]
def delab_checked_invert : Delab := do
  let expr ← getExpr
  let #[_, _, _, x, _] := expr.getAppArgs | failure
  let x ← delab x
  `($x⁻¹?)

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.CheckedZPow.checked_pow]
def delab_checked_int_pow : Delab := do
  let expr ← getExpr
  let #[_, _, _, x, y, _] := expr.getAppArgs | failure
  let x ← delab x
  let y ← delab y
  `($x ^? $y)
