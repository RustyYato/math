module

public import Math.Data.Set.Defs
public import Math.Order.Defs
public import Math.Data.Set.Nonempty
import Math.Tactic.Basic

@[expose] section
namespace Math

public class SupSet (α: Type*) where
  sSup : Set α -> α
public class InfSet (α: Type*) where
  sInf : Set α -> α

prefix:100 "⨆ " => SupSet.sSup
prefix:100 "⨅ " => InfSet.sInf

namespace Set

public instance : SupSet (Set α) where
  sSup U := ⋃ U

public instance : InfSet (Set α) where
  sInf U := ⋂ U

@[simp] public theorem sSup_eq_sUnion (s: Set (Set α)) : ⨆ s = ⋃ s := rfl
@[simp] public theorem sInf_eq_sInter (s: Set (Set α)) : ⨅ s = ⋂ s := rfl

public def iSup [SupSet α] (s: ι -> α) : α := ⨆ (Set.range s)
public def iInf [InfSet α] (s: ι -> α) : α := ⨅ (Set.range s)

section Syntax

open Lean Meta PrettyPrinter TSyntax.Compat

macro (name := big_op_iSup) "⨆ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``iSup xs b
macro (name := big_op_iInf) "⨅ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``iInf xs b

@[app_unexpander iSup] public meta def unexpand_iSup : Unexpander
  | `($(_) fun $x:ident => ⨆ $xs:binderIdent*, $b) => `(⨆ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(⨆ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(⨆ ($x:ident : $t), $b)
  | _                                              => throw ()

@[app_unexpander iInf] public meta def unexpand_iInf : Unexpander
  | `($(_) fun $x:ident => ⨅ $xs:binderIdent*, $b) => `(⨅ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(⨅ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(⨅ ($x:ident : $t), $b)
  | _                                              => throw ()

end Syntax

@[simp] public theorem mem_iSup (f: ι -> Set α) : x ∈ ⨆i, f i ↔ ∃i, x ∈ f i := by
  simp [iSup]
  apply Iff.intro
  intro ⟨_, ⟨i, rfl⟩, _⟩
  exists i
  intro ⟨i, hi⟩
  exists f i
  apply And.intro _ hi
  exists i

@[simp] public theorem mem_iInf (f: ι -> Set α) : x ∈ ⨅i, f i ↔ ∀i, x ∈ f i := by
  simp [iInf]

variable [LE α]

public def upperBounds (U: Set α) : Set α where
  Mem a := ∀u ∈ U, u ≤ a
public def lowerBounds (U: Set α) : Set α where
  Mem a := ∀u ∈ U, a ≤ u

@[simp] public theorem mem_upperBounds (U: Set α) : ∀{x}, x ∈ U.upperBounds ↔ ∀u ∈ U, u ≤ x := Iff.rfl
@[simp] public theorem mem_lowerBounds (U: Set α) : ∀{x}, x ∈ U.lowerBounds ↔ ∀u ∈ U, x ≤ u := Iff.rfl

public def boundedAbove (U: Set α) := (upperBounds U).Nonempty
public def boundedBelow (U: Set α) := (lowerBounds U).Nonempty

public def isMax (a: α) (U: Set α) := a ∈ U ∩ U.upperBounds
public def isMin (a: α) (U: Set α) := a ∈ U ∩ U.lowerBounds

public def isGLB (a: α) (U: Set α) := U.lowerBounds.isMax a
public def isLUB (a: α) (U: Set α) := U.upperBounds.isMin a

variable [LT α]

public def Iio (a: α) : Set α where
  Mem x := x < a
public def Ioi (a: α) : Set α where
  Mem x := a < x
public def Iic (a: α) : Set α where
  Mem x := x ≤ a
public def Ici (a: α) : Set α where
  Mem x := a ≤ x
public def Ioo (a b: α) : Set α := Ioi a ∩ Iio b
public def Ioc (a b: α) : Set α := Ioi a ∩ Iic b
public def Ico (a b: α) : Set α := Ici a ∩ Iio b
public def Icc (a b: α) : Set α := Ici a ∩ Iic b

end Set

public class IsLawfulSup (α: Type*) [LE α] [SupSet α] where
  le_sSup (U: Set α) : ⨆ U ∈ U.upperBounds

public class IsLawfulInf (α: Type*) [LE α]  [InfSet α] where
  sInf_le (U: Set α) : ⨅ U ∈ U.lowerBounds

export IsLawfulSup (le_sSup)
export IsLawfulInf (sInf_le)

attribute [local irreducible] OrderOpp in
public instance [InfSet α] : SupSet αᵒᵖ where
  sSup U := .mk (⨅ (U.preimage .mk))
attribute [local irreducible] OrderOpp in
public instance [SupSet α] : InfSet αᵒᵖ where
  sInf U := .mk (⨆ (U.preimage .mk))
public instance [InfSet α] [LE α] [IsLawfulInf α] : IsLawfulSup αᵒᵖ where
  le_sSup := sInf_le (α := α)
public instance [SupSet α] [LE α] [IsLawfulSup α] : IsLawfulInf αᵒᵖ where
  sInf_le := le_sSup (α := α)

public instance : LE (Set α) where
  le := (· ⊆ ·)
public instance : LT (Set α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

public instance : Max (Set α) where
  max a b := a ∪ b
public instance : Min (Set α) where
  min a b := a ∩ b

public instance : IsLattice (Set α) where
  lt_iff_le_and_not_ge := Iff.rfl
  refl := Set.sub_refl
  htrans := Set.sub_trans
  antisymm _ _ := Set.sub_antisymm
  left_le_max a b x hx := by left; assumption
  right_le_max a b x hx := by right; assumption
  min_le_left a b _ := And.left
  min_le_right a b _ := And.right
  max_le ha hb := by
    intro x h; cases h
    apply ha; assumption
    apply hb; assumption
  le_min ha hb := by
    intro x hx
    apply And.intro
    apply ha; assumption
    apply hb; assumption

public instance : IsLawfulSup (Set α) where
  le_sSup U u hu := by
    intro x hx; apply Set.mem_sUnion.mpr
    exists u

public instance : IsLawfulInf (Set α) where
  sInf_le U u hu := by
    intro x hx;
    replace hx := Set.mem_sInter.mp hx
    apply hx; assumption

public instance : IsLawfulTop (Set α) where
  le_top _ _ _ := True.intro
public instance : IsLawfulBot (Set α) where
  bot_le := nofun
