module

public import Math.Data.Set.Defs
public import Math.Data.Set.Nonempty
import Math.Tactic.Basic

namespace Math.Set

public theorem union_comm (a b: Set α) : a ∪ b = b ∪ a := by ext; simp [Or.comm]
public theorem inter_comm (a b: Set α) : a ∩ b = b ∩ a := by ext; simp [And.comm]

public theorem union_assoc (a b c: Set α) : a ∪ b ∪ c = a ∪ (b ∪ c) := by ext; simp [or_assoc]
public theorem inter_assoc (a b c: Set α) : a ∩ b ∩ c = a ∩ (b ∩ c) := by ext; simp [and_assoc]

public instance : @Std.Commutative (Set α) (· ∩ ·) := ⟨inter_comm⟩
public instance : @Std.Associative (Set α) (· ∩ ·) := ⟨inter_assoc⟩
public instance : @Std.Commutative (Set α) (· ∪ ·) := ⟨union_comm⟩
public instance : @Std.Associative (Set α) (· ∪ ·) := ⟨union_assoc⟩

@[simp] public theorem preimage_id (s: Set α) : s.preimage id = s := rfl
@[simp] public theorem preimage_id' (s: Set α) (f: α -> α) (hf: ∀x, f x = x) : s.preimage f = s := by
  rw [show f = id from ?_, preimage_id]
  ext; apply hf
@[simp] public theorem preimage_preimage (s: Set α) (f: γ -> β) (g: β -> α) : (s.preimage g).preimage f = s.preimage (g ∘ f) := rfl
@[simp] public theorem scompl_scompl (s: Set α) : sᶜᶜ = s := by ext; simp

public theorem scompl_inj {a b: Set α} : aᶜ = bᶜ ↔ a = b := by
  apply Iff.intro
  intro h; rw [←scompl_scompl a, ←scompl_scompl b, h]
  intro h; rw [h]

@[simp] public theorem sInter_empty : ⋂ (⊥: Set (Set _)) = (⊤: Set α) := by ext; simp
@[simp] public theorem sUnion_empty : ⋃ (⊥: Set (Set _)) = (⊥: Set α) := by ext; simp

@[simp] public theorem sInter_univ : ⋂ (⊤: Set (Set _)) = (⊥: Set α) := by
  ext; simp
  exists ⊥
  simp

@[simp] public theorem sUnion_univ : ⋃ (⊤: Set (Set _)) = (⊤: Set α) := by
  ext; simp
  exists ⊤

@[simp] public theorem sInter_insert (a: Set α) (as: Set (Set α)) : ⋂ (insert a as) = a ∩ ⋂as := by
  ext; simp
@[simp] public theorem sUnion_insert (a: Set α) (as: Set (Set α)) : ⋃ (insert a as) = a ∪ ⋃as := by
  ext; simp

@[simp] public theorem inter_top (a: Set α) : a ∩ ⊤ = a := by ext; simp
@[simp] public theorem inter_bot (a: Set α) : a ∩ ⊥ = ⊥ := by ext; simp
@[simp] public theorem top_inter (a: Set α) : ⊤ ∩ a = a := by ext; simp
@[simp] public theorem bot_inter (a: Set α) : ⊥ ∩ a = ⊥ := by ext; simp

@[simp] public theorem union_top (a: Set α) : a ∪ ⊤ = ⊤ := by ext; simp
@[simp] public theorem union_bot (a: Set α) : a ∪ ⊥ = a := by ext; simp
@[simp] public theorem top_union (a: Set α) : ⊤ ∪ a = ⊤ := by ext; simp
@[simp] public theorem bot_union (a: Set α) : ⊥ ∪ a = a := by ext; simp

public theorem singleton_eq_insert (a: α) : ({a}: Set α) = insert a ⊥ := by ext; simp [Set.mem_insert, -Set.mem_insert']

@[simp] public theorem sInter_singleton (a: Set α) : ⋂ ({a}: Set (Set _)) = a := by
  simp [singleton_eq_insert]
@[simp] public theorem sUnion_singleton (a: Set α) : ⋃ ({a}: Set (Set _)) = a := by
  simp [singleton_eq_insert]

@[simp] public theorem sInter_pair_eq_inter (a b: Set α) : ⋂ ({a, b}: Set _) = a ∩ b := by
  simp

@[simp] public theorem sUnion_pair_eq_union (a b: Set α) : ⋃ ({a, b}: Set _) = a ∪ b := by
  simp

public theorem sub_sUnion (U: Set (Set α)) (a: Set α) : a ∈ U -> a ⊆ ⋃ U := by
  intro ha x hx
  exists a

@[expose] public def ofList {α} (list: List α) : Set α where
  Mem := (· ∈ list)

@[simp] public theorem mem_ofList {list: List α} : ∀{x}, x ∈ ofList list ↔ x ∈ list := Iff.rfl

@[simp] public theorem compl_top : ⊤ᶜ = (⊥: Set α) := by ext; simp
@[simp] public theorem compl_bot : ⊥ᶜ = (⊤: Set α) := by ext; simp

@[simp] public theorem compl_sUnion (U: Set (Set α)) : (⋃ U)ᶜ = ⋂ (U.preimage (·ᶜ)) := by
  ext a; simp
  apply Iff.intro
  intro h x hx
  simpa using h xᶜ hx
  intro h x hx
  rw [←scompl_scompl x] at hx
  simpa using h _ hx

@[simp] public theorem compl_sInter (U: Set (Set α)) : (⋂ U)ᶜ = ⋃ (U.preimage (·ᶜ)) := by
  apply scompl_inj.mp
  rw [compl_sUnion]
  simp

public theorem preimage_compl_eq_image_compl (U: Set (Set α)) : U.preimage (·ᶜ) = U.image (·ᶜ) := by
  ext u; simp
  apply Iff.intro
  intro h; refine ⟨_, h, ?_⟩; simp
  rintro ⟨_, _, rfl⟩; simpa

@[simp] public theorem image_insert {α β} (a: α) (U: Set α) (f: α -> β) : (insert a U).image f = insert (f a) (U.image f) := by
  ext b; simp; rw [Eq.comm]

@[simp] public theorem image_empty (f: α -> β) : Set.image f ⊥ = ⊥ := by
  ext; simp

@[simp] public theorem image_singleton (a: α) (f: α -> β) : Set.image f {a} = {f a} := by
  rw [singleton_eq_insert, singleton_eq_insert]
  simp

@[simp] public theorem compl_union (a b: Set α) : (a ∪ b)ᶜ = aᶜ ∩ bᶜ := by
  rw [←sUnion_pair_eq_union, compl_sUnion, preimage_compl_eq_image_compl]
  simp

@[simp] public theorem compl_inter (a b: Set α) : (a ∩ b)ᶜ = aᶜ ∪ bᶜ := by
  rw [←sInter_pair_eq_inter, compl_sInter, preimage_compl_eq_image_compl]
  simp

public theorem nonempty_iff (a: Set α) : a.Nonempty ↔ ¬∀x, x ∉ a := by
  simp; apply Iff.intro <;> (intro ⟨x, hx⟩; exists x)

@[simp] public theorem preimage_inter (f: α -> β) (u v: Set β) : Set.preimage f (u ∩ v) = Set.preimage f u ∩ Set.preimage f v := rfl
@[simp] public theorem preimage_sUnion (f: α -> β) (u: Set (Set β)) : Set.preimage f (⋃ u) = ⋃ u.image (Set.preimage f) := by
  ext a; apply Iff.intro
  intro ⟨u, _, _⟩
  exists u.preimage f
  apply And.intro
  apply Set.mem_image'
  assumption
  assumption
  rintro ⟨_, h, _⟩
  simp at h; obtain ⟨u, _, rfl⟩ := h
  exists u

public theorem image_eq_range (f: α -> β) (s: Set α): s.image f = Set.range (fun x: s => f x.val) := by
  ext b; simp

public theorem image_univ_eq_range (f: α -> β): image f ⊤ = Set.range f := by
  ext b; simp

public theorem image_nonempty_iff {f: α -> β} {s: Set α} : (s.image f).Nonempty ↔ s.Nonempty := by
  simp only [nonempty_spec]
  apply Iff.intro
  simp [mem_image]
  intro a h
  exists a
  intro ⟨a, ha⟩
  exists f a
  apply Set.mem_image'
  assumption

public theorem univ_nonempty (α: Type*) [h: Nonempty α] : (⊤: Set α).Nonempty := by
  obtain ⟨x⟩ := h
  exact ⟨x, True.intro⟩

public theorem inter_eq_left (a b: Set α) (h: a ⊆ b) : a ∩ b = a := by
  ext i; apply Iff.intro And.left
  intro ha; apply And.intro ha
  exact h _ ha
public theorem inter_eq_right (a b: Set α) (h: b ⊆ a) : a ∩ b = b := by
  rw [inter_comm, inter_eq_left _ _ h]
public theorem union_inter (a b k: Set α) : (a ∪ b) ∩ k = a ∩ k ∪ b ∩ k := by
  ext i; simp; apply or_and_right
public theorem sdiff_inter (a b: Set α) : a \ b ∩ b = ⊥ := by
  ext i; simp
public theorem sdiff_sub (a b: Set α) : a \ b ⊆ a := fun _ => And.left

public theorem sUnion_preimage (U: Set (Set β)) (f: α -> β) :
  (⋃ U).preimage f = ⋃ (U.image (Set.preimage f)) := by
  ext a; simp

public theorem sInter_preimage (U: Set (Set β)) (f: α -> β) :
  (⋂ U).preimage f = ⋂ (U.image (Set.preimage f)) := by
  ext a; simp

public theorem inter_preimage (a b: Set β) (f: α -> β) :
  (a ∩ b).preimage f = a.preimage f ∩ b.preimage f := by
  ext a; simp

public theorem union_preimage (a b: Set β) (f: α -> β) :
  (a ∪ b).preimage f = a.preimage f ∪ b.preimage f := by
  ext a; simp
