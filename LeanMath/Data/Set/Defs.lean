import LeanMath.Tactic.TypeStar
import LeanMath.Logic.LEM
import LeanMath.Logic.Small.Defs
import LeanMath.Data.TopBot.Defs
import LeanMath.Data.Equiv.Defs

structure Set (α: Type*) where
  ofMem :: Mem: α -> Prop

class SetLike (S: Type*) (α: outParam Type*) where
  coeSet : S -> Set α := by intro s; exact s.toSet
  coeInj: Function.Injective coeSet := by
    intro a b h
    cases a; cases b
    dsimp at h
    congr
    try
      apply SetLike.coeInj
      assumption

@[coe] abbrev Set.coe [SetLike S α] (s: S) : Set α := SetLike.coeSet s
def Set.coe_inj [SetLike S α] : Function.Injective (Set.coe (S := S)) := SetLike.coeInj

@[simp] def SetLike.coeSet_eq_Set_coe [SetLike S α] : SetLike.coeSet = Set.coe (S := S) (α := α) := rfl

instance : SetLike (Set α) α where
  coeSet x := x

instance [SetLike S α] : CoeOut S (Set α) where
  coe := Set.coe

class SUnion (α: Type*) (β: outParam <| Type*) where
  sUnion : α -> β

class SInter (α: Type*) (β: outParam <| Type*) where
  sInter : α -> β

class SetComplement (α: Type*) where
  scompl : α -> α

class SupSet (α: Type*) where
  sSup: Set α -> α

class InfSet (α: Type*) where
  sInf: Set α -> α

export SupSet (sSup)
export InfSet (sInf)

prefix:100 "⋃ " => SUnion.sUnion
prefix:100 "⋂ " => SInter.sInter
postfix:max "ᶜ" => SetComplement.scompl

prefix:100 "⨆ " => SupSet.sSup
prefix:100 "⨅ " => InfSet.sInf

namespace Set

section Defs

instance : Membership α (Set α) where
  mem := Set.Mem

instance : HasSubset (Set α) where
  Subset a b := ∀x ∈ a, x ∈ b

instance : HasSSubset (Set α) where
  SSubset a b := a ⊆ b ∧ ∃x ∈ b, ¬x ∈ a

instance (priority := 700) [SetLike S α] : Membership α S where
  mem S a := a ∈ (S: Set α)

instance (priority := 700) [SetLike S α] : HasSubset S where
  Subset a b := (a: Set α) ⊆ b

@[simp] def coe_id (x: Set α) : Set.coe x = x := rfl

@[simp] def ofMem_mem (P: α -> Prop) : ∀{x}, x ∈ ofMem P ↔ P x := by rfl

def sub_def (a b: Set α) : (a ⊆ b) = ∀x ∈ a, x ∈ b := rfl

@[simp] def mk_mem {P: α -> Prop} : ∀{x}, (x ∈ Set.ofMem P) = P x := rfl

@[ext] def ext (a b : Set α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := by
  intro h;
  cases a; cases b
  congr; ext; apply h

def _root_.SetLike.ext [SetLike S α] (a b: S) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := by
  intro h
  apply SetLike.coeInj
  ext; apply h

@[refl] def sub_refl (s: Set α) : s ⊆ s := fun _ => id
def sub_trans {a b c: Set α} : a ⊆ b -> b ⊆ c -> a ⊆ c := fun ab bc _ h => bc _ (ab _ h)
def sub_antisymm {a b: Set α} : a ⊆ b -> b ⊆ a -> a = b := by
  intro ab ba
  ext x
  apply Iff.intro
  apply ab
  apply ba

instance : Bot (Set α) where
  bot := ⟨fun _ => False⟩
instance : Top (Set α) where
  top := ⟨fun _ => True⟩
instance : EmptyCollection (Set α) where
  emptyCollection := ⊥

instance : Inhabited (Set α) := ⟨⊥⟩
instance : Nonempty (Set α) := inferInstance

@[simp] def not_mem_empty (a: α) : a ∉ (⊥: Set α) := nofun
@[simp] def not_mem_bot (a: α) : a ∉ (⊥: Set α) := nofun
@[simp] def mem_top (a: α) : a ∈ (⊤: Set α) := True.intro

@[simp] def empty_sub (a: Set α) : ⊥ ⊆ a := nofun
@[simp] def bot_sub (a: Set α) : ⊥ ⊆ a := nofun
@[simp] def sub_top (a: Set α) : a ⊆ ⊤ := by intro _ _; trivial

def ext_empty (a: Set α) : (∀x: α, ¬x ∈ a) -> a = ⊥ := by
  intro h
  ext x
  simp [h]
def ext_univ (a: Set α) : (∀x: α, x ∈ a) -> a = ⊤ := by
  intro h
  ext x
  simp [h]

instance : Singleton α (Set α) where
  singleton a := { Mem := (a = ·) }

@[simp] def mem_singleton {a: α} : ∀{x}, x ∈ ({a}: Set α) ↔ a = x := Iff.rfl

instance : Union (Set α) where
  union a b := { Mem x := x ∈ a ∨ x ∈ b }

@[simp] def mem_union {a b: Set α} : ∀{x}, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := Iff.rfl

def sep (P: α -> Prop) (s: Set α) : Set α where
  Mem x := x ∈ s ∧ P x

@[simp] def mem_sep {P: α -> Prop} {a: Set α} : ∀{x}, x ∈ a.sep P ↔ x ∈ a ∧ P x := Iff.rfl

instance : Inter (Set α) where
  inter a b := a.sep (· ∈ b)

@[simp] def mem_inter {a b: Set α} : ∀{x}, x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := Iff.rfl

instance : SetComplement (Set α) where
  scompl a := { Mem := (· ∉ a) }

@[simp] def mem_scompl {a: Set α} : ∀{x}, x ∈ aᶜ ↔ x ∉ a := Iff.rfl

instance : SDiff (Set α) where
  sdiff a b := a.sep (· ∉ b)

@[simp] def mem_sdiff {a b: Set α} : ∀{x}, x ∈ a \ b ↔ x ∈ a ∧ x ∉ b := Iff.rfl

instance : Insert α (Set α) where
  insert a x := {a} ∪ x

def mem_insert {a: α} {s: Set α} : ∀{x}, x ∈ insert a s ↔ a = x ∨ x ∈ s := Iff.rfl
@[simp] def mem_insert' {a: α} {s: Set α} : ∀{x}, x ∈ insert a s ↔ x = a ∨ x ∈ s := by
  intro x; apply Iff.intro
  iterate 2
  intro h; rcases h with rfl | h
  left; rfl; right; assumption

def preimage (f: α -> β) (s: Set β) : Set α where
  Mem x := f x ∈ s

@[simp] def mem_preimage {s: Set β} {f: α -> β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl

def image (f: ι -> α) (s: Set ι) : Set α where
  Mem a := ∃i ∈ s, f i = a

@[simp] def mem_image {s: Set ι} {f: ι -> α} : ∀{x}, x ∈ s.image f ↔ ∃i ∈ s, f i = x := Iff.rfl

def mem_image' {s: Set ι} {f: ι -> α} : x ∈ s -> f x ∈ s.image f := by
  intro h
  simp; exists x

def range (f: ι -> α) : Set α where
  Mem a := ∃i, f i = a

@[simp] def mem_range {f: ι -> α} : ∀{x}, x ∈ range f ↔ ∃i, f i = x := Iff.rfl

def mem_range' {f: ι -> α} : f x ∈ range f := by simp

def iSup [SupSet α] (s: ι -> α) : α := sSup (Set.range s)
def iInf [InfSet α] (s: ι -> α) : α := sInf (Set.range s)

section Syntax

open Lean Meta PrettyPrinter TSyntax.Compat

macro (name := big_op_iSup) "⨆ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``iSup xs b
macro (name := big_op_iInf) "⨅ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``iInf xs b

@[app_unexpander iSup] def unexpand_iSup : Unexpander
  | `($(_) fun $x:ident => ⨆ $xs:binderIdent*, $b) => `(⨆ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(⨆ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(⨆ ($x:ident : $t), $b)
  | _                                              => throw ()

@[app_unexpander iInf] def unexpand_iInf : Unexpander
  | `($(_) fun $x:ident => ⨅ $xs:binderIdent*, $b) => `(⨅ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(⨅ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(⨅ ($x:ident : $t), $b)
  | _                                              => throw ()

end Syntax

instance : SUnion (Set (Set α)) (Set α) where
  sUnion U := { Mem x := ∃s ∈ U, x ∈ s }

instance : SInter (Set (Set α)) (Set α) where
  sInter U := { Mem x := ∀s ∈ U, x ∈ s }

instance : SupSet (Set α) where
  sSup U := ⋃ U

instance : InfSet (Set α) where
  sInf U := ⋂ U

@[simp] def sSup_eq_sUnion (s: Set (Set α)) : ⨆ s = ⋃ s := rfl
@[simp] def sInf_eq_sInter (s: Set (Set α)) : ⨅ s = ⋂ s := rfl

@[simp] def mem_sUnion {S: Set (Set α)} : ∀{x}, x ∈ ⋃ S ↔ ∃s ∈ S, x ∈ s := Iff.rfl
@[simp] def mem_sInter {S: Set (Set α)} : ∀{x}, x ∈ ⋂ S ↔ ∀s ∈ S, x ∈ s := Iff.rfl

@[simp] def mem_iSup (f: ι -> Set α) : x ∈ ⨆i, f i ↔ ∃i, x ∈ f i := by
  simp [iSup]
  apply Iff.intro
  intro ⟨_, ⟨i, rfl⟩, _⟩
  exists i
  intro ⟨i, hi⟩
  exists f i
  apply And.intro _ hi
  exists i

@[simp] def mem_iInf (f: ι -> Set α) : x ∈ ⨅i, f i ↔ ∀i, x ∈ f i := by
  simp [iInf]

def powerset (s: Set α) : Set (Set α) where
  Mem a := a ⊆ s

@[simp] def mem_powerset {s: Set α} : ∀{x}, x ∈ s.powerset ↔ x ⊆ s := Iff.rfl

instance : CoeSort (Set α) (Sort _) where
  coe s := { x // x ∈ s }

def attach (s: Set α) : Set s := ⊤

@[simp] def mem_attach {s: Set α} : ∀{x}, x ∈ s.attach := True.intro

protected abbrev Nonempty (s: Set α) : Prop := Nonempty s

@[simp] def not_nonempty {a: Set α} : ¬a.Nonempty ↔ a = ⊥ := by
  apply Iff.intro
  intro h; ext x; simp
  intro g; apply h; exists x
  rintro rfl
  intro h
  obtain ⟨x, hx⟩ := h
  contradiction

@[simp] def eq_empty_iff {a: Set α} : a = ⊥ ↔ ∀x, x ∉ a := by
  apply Iff.intro
  intro rfl; nofun
  intro h
  ext a
  simp [h]

@[simp] def ne_empty [LEM] {a: Set α} : a ≠ ⊥ ↔ a.Nonempty := by
  apply LEM.not_iff_not.mp
  apply Iff.trans LEM.not_not
  exact not_nonempty.symm

def nonempty_iff_exists {s: Set α} : s.Nonempty ↔ ∃x, x ∈ s := by
  apply Iff.intro
  intro ⟨x, sh⟩
  exists x
  intro ⟨x, sh⟩
  exists x

def exists_elem (s: Set α) [s.Nonempty] : ∃x, x ∈ s := by
  rwa [←nonempty_iff_exists]

instance (a: α) : Set.Nonempty {a} := by exists a

instance : Inhabited ({a}: Set α) where
  default := ⟨a, rfl⟩

instance : Inhabited (insert a x: Set α) where
  default := ⟨a, by simp⟩

instance {a b: Set α} [h: Nonempty a] : Nonempty (a ∪ b: Set _) := by
    obtain ⟨x, h⟩ := h
    exact ⟨x, by simp [h]⟩

instance {a b: Set α} [h: Nonempty b] : Nonempty (a ∪ b: Set _) := by
    obtain ⟨x, h⟩ := h
    exact ⟨x, by simp [h]⟩

instance  [h : Nonempty ι] (f : ι → α) : (range f).Nonempty := by
  obtain ⟨x⟩ := h
  refine ⟨f x, by exists x⟩

instance (s: Set α) (f: α -> β) [s.Nonempty] : (s.image f).Nonempty := by
  have ⟨x, h⟩ := exists_elem s
  exists f x
  exists x

def empty_not_nonempty : ¬Set.Nonempty (⊥: Set α) := nofun

macro_rules
| `(tactic|contradiction) => `(tactic|exfalso; apply empty_not_nonempty; assumption)

end Defs

def union_comm (a b: Set α) : a ∪ b = b ∪ a := by ext; simp [Or.comm]
def inter_comm (a b: Set α) : a ∩ b = b ∩ a := by ext; simp [And.comm]

def union_assoc (a b c: Set α) : a ∪ b ∪ c = a ∪ (b ∪ c) := by ext; simp [or_assoc]
def inter_assoc (a b c: Set α) : a ∩ b ∩ c = a ∩ (b ∩ c) := by ext; simp [and_assoc]

instance : @Std.Commutative (Set α) (· ∩ ·) := ⟨inter_comm⟩
instance : @Std.Associative (Set α) (· ∩ ·) := ⟨inter_assoc⟩
instance : @Std.Commutative (Set α) (· ∪ ·) := ⟨union_comm⟩
instance : @Std.Associative (Set α) (· ∪ ·) := ⟨union_assoc⟩

@[simp] def preimage_id (s: Set α) : s.preimage id = s := rfl
@[simp] def preimage_id' (s: Set α) (f: α -> α) (hf: ∀x, f x = x) : s.preimage f = s := by
  rw [show f = id from ?_, preimage_id]
  ext; apply hf
@[simp] def preimage_preimage (s: Set α) (f: γ -> β) (g: β -> α) : (s.preimage g).preimage f = s.preimage (g ∘ f) := rfl
@[simp] def scompl_scompl (s: Set α) : sᶜᶜ = s := by ext; simp

def scompl_inj {a b: Set α} : aᶜ = bᶜ ↔ a = b := by
  apply Iff.intro
  intro h; rw [←scompl_scompl a, ←scompl_scompl b, h]
  intro h; rw [h]

@[simp] def sInter_empty : ⋂ (⊥: Set (Set _)) = (⊤: Set α) := by ext; simp
@[simp] def sUnion_empty : ⋃ (⊥: Set (Set _)) = (⊥: Set α) := by ext; simp

@[simp] def sInter_univ : ⋂ (⊤: Set (Set _)) = (⊥: Set α) := by
  ext; simp
  exists ⊥
  simp

@[simp] def sUnion_univ : ⋃ (⊤: Set (Set _)) = (⊤: Set α) := by
  ext; simp
  exists ⊤

@[simp] def sInter_insert (a: Set α) (as: Set (Set α)) : ⋂ (insert a as) = a ∩ ⋂as := by
  ext; simp
@[simp] def sUnion_insert (a: Set α) (as: Set (Set α)) : ⋃ (insert a as) = a ∪ ⋃as := by
  ext; simp

@[simp] def inter_top (a: Set α) : a ∩ ⊤ = a := by ext; simp
@[simp] def inter_bot (a: Set α) : a ∩ ⊥ = ⊥ := by ext; simp
@[simp] def top_inter (a: Set α) : ⊤ ∩ a = a := by ext; simp
@[simp] def bot_inter (a: Set α) : ⊥ ∩ a = ⊥ := by ext; simp

@[simp] def union_top (a: Set α) : a ∪ ⊤ = ⊤ := by ext; simp
@[simp] def union_bot (a: Set α) : a ∪ ⊥ = a := by ext; simp
@[simp] def top_union (a: Set α) : ⊤ ∪ a = ⊤ := by ext; simp
@[simp] def bot_union (a: Set α) : ⊥ ∪ a = a := by ext; simp

def singleton_eq_insert (a: α) : ({a}: Set α) = insert a ⊥ := by ext; simp [Set.mem_insert, -Set.mem_insert']

@[simp] def sInter_singleton (a: Set α) : ⋂ ({a}: Set (Set _)) = a := by
  simp [singleton_eq_insert]
@[simp] def sUnion_singleton (a: Set α) : ⋃ ({a}: Set (Set _)) = a := by
  simp [singleton_eq_insert]

@[simp] def sInter_pair_eq_inter (a b: Set α) : ⋂ ({a, b}: Set _) = a ∩ b := by
  simp

@[simp] def sUnion_pair_eq_union (a b: Set α) : ⋃ ({a, b}: Set _) = a ∪ b := by
  simp

def sub_sUnion (U: Set (Set α)) (a: Set α) : a ∈ U -> a ⊆ ⋃ U := by
  intro ha x hx
  exists a

def ofList (list: List α) : Set α where
  Mem := (· ∈ list)

@[simp] def mem_ofList {list: List α} : ∀{x}, x ∈ ofList list ↔ x ∈ list := Iff.rfl

@[simp] def compl_top : ⊤ᶜ = (⊥: Set α) := by ext; simp
@[simp] def compl_bot : ⊥ᶜ = (⊤: Set α) := by ext; simp

@[simp] def compl_sUnion (U: Set (Set α)) : (⋃ U)ᶜ = ⋂ (U.preimage (·ᶜ)) := by
  ext a; simp
  apply Iff.intro
  intro h x hx
  simpa using h xᶜ hx
  intro h x hx
  rw [←scompl_scompl x] at hx
  simpa using h _ hx

@[simp] def compl_sInter (U: Set (Set α)) : (⋂ U)ᶜ = ⋃ (U.preimage (·ᶜ)) := by
  apply scompl_inj.mp
  rw [compl_sUnion]
  simp

def preimage_compl_eq_image_compl (U: Set (Set α)) : U.preimage (·ᶜ) = U.image (·ᶜ) := by
  ext u; simp
  apply Iff.intro
  intro h; refine ⟨_, h, ?_⟩; simp
  rintro ⟨_, _, rfl⟩; simpa

@[simp] def image_insert {α β} (a: α) (U: Set α) (f: α -> β) : (insert a U).image f = insert (f a) (U.image f) := by
  ext b; simp; rw [Eq.comm]

@[simp] def image_empty (f: α -> β) : Set.image f ⊥ = ⊥ := by
  ext; simp

@[simp] def image_singleton (a: α) (f: α -> β) : Set.image f {a} = {f a} := by
  rw [singleton_eq_insert, singleton_eq_insert]
  simp

@[simp] def compl_union (a b: Set α) : (a ∪ b)ᶜ = aᶜ ∩ bᶜ := by
  rw [←sUnion_pair_eq_union, compl_sUnion, preimage_compl_eq_image_compl]
  simp

@[simp] def compl_inter (a b: Set α) : (a ∩ b)ᶜ = aᶜ ∪ bᶜ := by
  rw [←sInter_pair_eq_inter, compl_sInter, preimage_compl_eq_image_compl]
  simp

def nonempty_iff (a: Set α) : a.Nonempty ↔ ¬∀x, x ∉ a := by
  simp; apply Iff.intro <;> (intro ⟨x, hx⟩; exists x)

@[simp] def preimage_inter (f: α -> β) (u v: Set β) : Set.preimage f (u ∩ v) = Set.preimage f u ∩ Set.preimage f v := rfl
@[simp] def preimage_sUnion (f: α -> β) (u: Set (Set β)) : Set.preimage f (⋃ u) = ⋃ u.image (Set.preimage f) := by
  ext a; apply Iff.intro
  intro ⟨u, _, _⟩
  exists u.preimage f
  apply And.intro
  apply Set.mem_image'
  assumption
  assumption
  rintro ⟨_, ⟨u, _, rfl⟩, _⟩
  exists u

def image_eq_range (f: α -> β) (s: Set α): s.image f = Set.range (fun x: s => f x.val) := by
  ext b; simp

def image_univ_eq_range (f: α -> β): image f ⊤  = Set.range f := by
  ext b; simp

def Induced (r: α -> α -> Prop) (U: Set α) : U -> U -> Prop := fun x y => r x y

def image_nonempty_iff {f: α -> β} {s: Set α} : (s.image f).Nonempty ↔ s.Nonempty := by
  apply Iff.intro
  intro ⟨_, a, _, h⟩
  exists a
  intro ⟨a, ha⟩
  exists f a
  apply Set.mem_image'
  assumption

@[implicit_reducible]
def univ_nonempty (α: Type*) [h: Nonempty α] : (⊤: Set α).Nonempty := by
  obtain ⟨x⟩ := h
  exact ⟨x, True.intro⟩

end Set

class IsLawfulSup (α: Type*) [LE α] [SupSet α] where
  protected le_sSup (U: Set α) (u: α) (hu: u ∈ U) : u ≤ ⨆ U

class IsLawfulInf (α: Type*) [LE α]  [InfSet α] where
  protected sInf_le (U: Set α) (u: α) (hu: u ∈ U) : ⨅ U ≤ u

def le_sSup [LE α] [SupSet α] [IsLawfulSup α] (U: Set α) (u: α) (hu: u ∈ U) : u ≤ ⨆ U :=
  IsLawfulSup.le_sSup _ _ hu

def sInf_le [LE α] [InfSet α] [IsLawfulInf α] (U: Set α) (u: α) (hu: u ∈ U) : ⨅ U ≤ u :=
  IsLawfulInf.sInf_le _ _ hu

def Subtype.val_inj {P: α -> Prop} : Function.Injective (Subtype.val (p := P)) := by
  intro a b h
  cases a; cases b; cases h
  rfl

def Bijection.embed_eqv_range [EmbeddingLike F α β] (f: F) : α ↭ Set.range f where
  toFun x := {
    val := f x
    property := ⟨_, rfl⟩
  }
  inj' := by
    intro a b h
    exact inj f (Subtype.mk.inj h)
  surj' := by
    intro ⟨_, _, rfl⟩
    refine ⟨_, rfl⟩

instance {α: Type u} {β: Type v} (f: α -> β) [Small.{w} α] : Small.{w} (Set.range f) :=
  Small.of_embed (α := Set.range f) (β := α) {
    toFun h := Classical.choose h.property
    inj {x y} h := by
      dsimp at h
      replace h := congrArg f h
      rw [Classical.choose_spec x.property, Classical.choose_spec y.property] at h
      ext; assumption
  }

@[implicit_reducible]
def Small.subset {a b: Set α} [Small.{u} b] (h: a ⊆ b) : Small.{u} a := by
  apply Small.of_embed (β := b)
  exact {
    toFun x := {
      val := x.val
      property := h _ x.property
    }
    inj := by
      intro ⟨x, hx⟩ ⟨y, hy⟩ h
      cases h; rfl
  }

instance {α: Type u} {β: Type v} (s: Set α) (f: α -> β) [Small.{w} s] : Small.{w} (Set.image f s) := by
  have : Small (Set.range (fun x: s => f x.val)) := inferInstance
  rw [←Set.image_eq_range] at this
  assumption
