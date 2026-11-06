module

import Math.Tactic.TypeStar
public import Math.Tactic.Invert
public meta import Lean.PrettyPrinter.Delaborator.Basic

namespace Math

public class CheckedInv (α: Type*) (P: outParam <| α -> Prop) where
  protected checked_inv (a: α) (p: P a) : α

public class CheckedMod (α: Type*) (P: outParam <| α -> Prop) where
  protected checked_mod (a b: α) (p: P b) : α

public class CheckedDiv (α: Type*) (P: outParam <| α -> Prop) where
  protected checked_div (a b: α) (p: P b) : α

public class CheckedZPow (α: Type*) (P: outParam <| α -> Prop) where
  protected checked_pow (a: α) (n: ℤ) (p: 0 ≤ n ∨ P a) : α

public abbrev CheckedInv? (α: Type*) [Zero α] := CheckedInv α (· ≠ 0)
public abbrev CheckedDiv? (α: Type*) [Zero α] := CheckedDiv α (· ≠ 0)
public abbrev CheckedMod? (α: Type*) [Zero α] := CheckedMod α (· ≠ 0)
public abbrev CheckedZPow? (α: Type*) [Zero α] := CheckedZPow α (· ≠ 0)

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

open Lean Meta PrettyPrinter Delaborator SubExpr

@[app_delab CheckedDiv.checked_div]
public meta def delab_checked_div : Delab := do
  let expr ← getExpr
  let #[_, _, _, x, y, _] := expr.getAppArgs | failure
  let x ← delab x
  let y ← delab y
  `($x /? $y)

@[app_delab CheckedMod.checked_mod]
public meta def delab_checked_mod : Delab := do
  let expr ← getExpr
  let #[_, _, _, x, y, _] := expr.getAppArgs | failure
  let x ← delab x
  let y ← delab y
  `($x %? $y)

@[app_delab CheckedInv.checked_inv]
public meta def delab_checked_invert : Delab := do
  let expr ← getExpr
  let #[_, _, _, x, _] := expr.getAppArgs | failure
  let x ← delab x
  `($x⁻¹?)

@[app_delab CheckedZPow.checked_pow]
public meta def delab_checked_int_pow : Delab := do
  let expr ← getExpr
  let #[_, _, _, x, y, _] := expr.getAppArgs | failure
  let x ← delab x
  let y ← delab y
  `($x ^? $y)
