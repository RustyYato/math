module

public meta import Lean.PrettyPrinter.Delaborator

public import Math.Order.TopBot.Defs
import Math.Tactic.Basic

namespace Math

public structure Set (α: Type*) where
  Mem : α -> Prop

public instance : Membership α (Set α) where
  mem s a := s.Mem a

public class SUnion (α: Type*) (β: outParam <| Type*) where
  sUnion : α -> β

public class SInter (α: Type*) (β: outParam <| Type*) where
  sInter : α -> β

public class SupSet (α: Type*) where
  sSup : Set α -> α
public class InfSet (α: Type*) where
  sInf : Set α -> α

prefix:100 "⋃ " => SUnion.sUnion
prefix:100 "⋂ " => SInter.sInter
postfix:max "ᶜ" => Complement.complement

prefix:100 "⨆ " => SupSet.sSup
prefix:100 "⨅ " => InfSet.sInf

public class IsLawfulSup (α: Type*) [LE α] [SupSet α] where
  protected le_sSup (U: Set α) (u: α) (hu: u ∈ U) : u ≤ ⨆ U

public class IsLawfulInf (α: Type*) [LE α]  [InfSet α] where
  protected sInf_le (U: Set α) (u: α) (hu: u ∈ U) : ⨅ U ≤ u

public theorem le_sSup [LE α] [SupSet α] [IsLawfulSup α] (U: Set α) (u: α) (hu: u ∈ U) : u ≤ ⨆ U :=
  IsLawfulSup.le_sSup _ _ hu

public theorem sInf_le [LE α] [InfSet α] [IsLawfulInf α] (U: Set α) (u: α) (hu: u ∈ U) : ⨅ U ≤ u :=
  IsLawfulInf.sInf_le _ _ hu

public class SetLike (S: Type*) (α: outParam Type*) where
  coeSet : S -> Set α := by intro s; exact s.toSet
  coeInj: Function.Injective coeSet := by
    intro a b h
    cases a; cases b
    dsimp at h
    congr
    try
      apply SetLike.coeInj
      assumption

namespace Set

public instance : HasSubset (Set α) where
  Subset a b := ∀x ∈ a, x ∈ b

@[coe] public abbrev toType (s: Set α) := { x // x ∈ s }

public instance : CoeSort (Set α) (Type u) where
  coe s := s.toType

@[coe] public abbrev coe [SetLike S α] (s: S) : Set α := SetLike.coeSet s
public theorem coe_inj [SetLike S α] : Function.Injective (Set.coe (S := S)) := SetLike.coeInj

public instance [SetLike S α] : CoeOut S (Set α) where
  coe := Set.coe

public instance (priority := 700) [SetLike S α] : Membership α S where
  mem S a := a ∈ (Set.coe S)

public instance (priority := 700) [SetLike S α] : HasSubset S where
  Subset a b := (a: Set α) ⊆ b

@[ext] public theorem ext (a b : Set α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := by
  intro h;
  cases a; cases b
  congr; ext; apply h

public theorem _root_.SetLike.ext [SetLike S α] (a b: S) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := by
  intro h
  apply SetLike.coeInj
  ext; apply h

@[refl] public theorem sub_refl (s: Set α) : s ⊆ s := fun _ => id
public theorem sub_trans {a b c: Set α} : a ⊆ b -> b ⊆ c -> a ⊆ c := fun ab bc _ h => bc _ (ab _ h)
public theorem sub_antisymm {a b: Set α} : a ⊆ b -> b ⊆ a -> a = b := by
  intro ab ba
  ext x
  apply Iff.intro
  apply ab
  apply ba

public instance : Bot (Set α) where
  bot := ⟨fun _ => False⟩
public instance : Top (Set α) where
  top := ⟨fun _ => True⟩
public instance : EmptyCollection (Set α) where
  emptyCollection := ⊥

public instance : Inhabited (Set α) := ⟨⊥⟩
public instance : Nonempty (Set α) := inferInstance

@[simp] public theorem not_mem_empty (a: α) : a ∉ (⊥: Set α) := nofun
@[simp] public theorem not_mem_bot (a: α) : a ∉ (⊥: Set α) := nofun
@[simp] public theorem mem_top (a: α) : a ∈ (⊤: Set α) := True.intro

@[simp] public theorem empty_sub (a: Set α) : ⊥ ⊆ a := nofun
@[simp] public theorem bot_sub (a: Set α) : ⊥ ⊆ a := nofun
@[simp] public theorem sub_top (a: Set α) : a ⊆ ⊤ := by intro _ _; trivial

public theorem ext_empty (a: Set α) : (∀x: α, ¬x ∈ a) -> a = ⊥ := by
  intro h
  ext x
  simp [h]
public theorem ext_univ (a: Set α) : (∀x: α, x ∈ a) -> a = ⊤ := by
  intro h
  ext x
  simp [h]

public instance : Singleton α (Set α) where
  singleton a := { Mem := (a = ·) }

@[simp] public theorem mem_singleton {a: α} : ∀{x}, x ∈ ({a}: Set α) ↔ a = x := Iff.rfl

public instance : Union (Set α) where
  union a b := { Mem x := x ∈ a ∨ x ∈ b }

@[simp] public theorem mem_union {a b: Set α} : ∀{x}, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := Iff.rfl

@[expose] public def sep (P: α -> Prop) (s: Set α) : Set α where
  Mem x := x ∈ s ∧ P x

@[simp] public theorem mem_sep {P: α -> Prop} {a: Set α} : ∀{x}, x ∈ a.sep P ↔ x ∈ a ∧ P x := Iff.rfl

public instance : Inter (Set α) where
  inter a b := a.sep (· ∈ b)

@[simp] public theorem mem_inter {a b: Set α} : ∀{x}, x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := Iff.rfl

public instance : Complement (Set α) where
  complement a := { Mem := (· ∉ a) }

@[simp] public theorem mem_scompl {a: Set α} : ∀{x}, x ∈ aᶜ ↔ x ∉ a := Iff.rfl

public instance : SDiff (Set α) where
  sdiff a b := a.sep (· ∉ b)

@[simp] public theorem mem_sdiff {a b: Set α} : ∀{x}, x ∈ a \ b ↔ x ∈ a ∧ x ∉ b := Iff.rfl

public instance : Insert α (Set α) where
  insert a x := {a} ∪ x

public theorem mem_insert {a: α} {s: Set α} : ∀{x}, x ∈ insert a s ↔ a = x ∨ x ∈ s := Iff.rfl
@[simp] public theorem mem_insert' {a: α} {s: Set α} : ∀{x}, x ∈ insert a s ↔ x = a ∨ x ∈ s := by
  intro x; apply Iff.intro
  iterate 2
  intro h; rcases h with rfl | h
  left; rfl; right; assumption

@[expose] public def preimage (f: α -> β) (s: Set β) : Set α where
  Mem x := f x ∈ s

@[simp] public theorem mem_preimage {s: Set β} {f: α -> β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl

public def image (f: ι -> α) (s: Set ι) : Set α where
  Mem a := ∃i ∈ s, f i = a

@[simp] public theorem mem_image {s: Set ι} {f: ι -> α} : ∀{x}, x ∈ s.image f ↔ ∃i ∈ s, f i = x := Iff.rfl

public theorem mem_image' {s: Set ι} {f: ι -> α} : x ∈ s -> f x ∈ s.image f := by
  intro h
  simp; exists x

public def range (f: ι -> α) : Set α where
  Mem a := ∃i, f i = a

@[simp] public theorem mem_range {f: ι -> α} : ∀{x}, x ∈ range f ↔ ∃i, f i = x := Iff.rfl

public theorem mem_range' {f: ι -> α} : f x ∈ range f := by simp

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

public instance : SUnion (Set (Set α)) (Set α) where
  sUnion U := { Mem x := ∃s ∈ U, x ∈ s }

public instance : SInter (Set (Set α)) (Set α) where
  sInter U := { Mem x := ∀s ∈ U, x ∈ s }

public instance : SupSet (Set α) where
  sSup U := ⋃ U

public instance : InfSet (Set α) where
  sInf U := ⋂ U

@[simp] public theorem sSup_eq_sUnion (s: Set (Set α)) : ⨆ s = ⋃ s := rfl
@[simp] public theorem sInf_eq_sInter (s: Set (Set α)) : ⨅ s = ⋂ s := rfl

@[simp] public theorem mem_sUnion {S: Set (Set α)} : ∀{x}, x ∈ ⋃ S ↔ ∃s ∈ S, x ∈ s := Iff.rfl
@[simp] public theorem mem_sInter {S: Set (Set α)} : ∀{x}, x ∈ ⋂ S ↔ ∀s ∈ S, x ∈ s := Iff.rfl

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

public def powerset (s: Set α) : Set (Set α) where
  Mem a := a ⊆ s

@[simp] public theorem mem_powerset {s: Set α} : ∀{x}, x ∈ s.powerset ↔ x ⊆ s := Iff.rfl

public def attach (s: Set α) : Set s := ⊤

@[simp] public theorem mem_attach {s: Set α} : ∀{x}, x ∈ s.attach := True.intro
