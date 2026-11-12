module

import Math.Tactic.Basic
import Math.Data.List.Defs

namespace Math

@[expose] section

public structure Multiset (α: Type*) where
  ofQuot :: toQuot : Quotient (List.isSetoid α)

namespace Multiset

public def mk (list: List α) : Multiset α where
  toQuot := Quotient.mk _ list

public theorem sound : a ≈ b -> mk a = mk b := by
  unfold mk; intro h; congr 1; apply Quotient.sound
  assumption

public def recOnSubsingleton {motive: Multiset α -> Sort u} [∀ms, Subsingleton (motive ms)] (mk : ∀x, motive (mk x)) (ms: Multiset α) : motive ms := by
  obtain ⟨ms⟩ := ms; apply ms.recOnSubsingleton (motive := fun s => _)
  apply mk
public theorem ind {motive: Multiset α -> Prop} (mk : ∀x, motive (mk x)) (ms: Multiset α) : motive ms := by
  apply recOnSubsingleton; apply mk

public def lift (f: List α -> β) (hf: ∀a b, a ≈ b -> f a = f b) (ms: Multiset α) : β :=
  ms.toQuot.lift f hf

public def lift₂ (f: List α -> List α -> β) (hf: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (as bs: Multiset α) : β :=
  as.toQuot.liftOn₂ bs.toQuot f hf

public def nil : Multiset α := mk []
public def cons (a: α) : Multiset α -> Multiset α :=
  lift (fun as => mk (a::as)) <| by
    intro as bs h; apply sound
    apply List.Perm.cons
    assumption

infixr:67 " ::ₘ " => cons

public instance : Append (Multiset α) where
  append := lift₂ (fun a b => mk (a ++ b)) <| by
    intro a b c d ac bd; apply sound
    apply List.Perm.trans
    apply (List.perm_append_left_iff _).mpr
    assumption
    apply (List.perm_append_right_iff _).mpr
    assumption

public instance : Membership α (Multiset α) where
  mem := flip fun a => lift (a ∈ ·) <| by
    intro as bs h; ext; apply h.mem_iff

@[simp] public theorem mem_cons {a: α} {as: Multiset α} : ∀{x}, x ∈ a::ₘas ↔ x = a ∨ x ∈ as := by
  induction as using ind
  intro x; apply List.mem_cons

public instance [DecidableEq α] (a: α) (s: Multiset α) : Decidable (a ∈ s) :=
  s.recOnSubsingleton (motive := fun s => Decidable (a ∈ s)) fun s => inferInstanceAs (Decidable (a ∈ s))

public theorem nil_append (bs: Multiset α) : nil ++ bs = bs := by
  induction bs using ind; apply sound
  rw [List.nil_append]; apply List.Perm.refl
public theorem cons_append (a: α) (as bs: Multiset α) : a::ₘas ++ bs = a::ₘ(as ++ bs) := by
  induction as using ind
  induction bs using ind; apply sound
  rw [List.cons_append]; apply List.Perm.refl
public theorem append_comm (as bs: Multiset α) : as ++ bs = bs ++ as := by
  induction as using ind
  induction bs using ind; apply sound
  apply List.perm_append_comm
public theorem append_nil (as: Multiset α) : as ++ nil = as := by
  rw [append_comm, nil_append]
public theorem append_cons (b: α) (as bs: Multiset α) : as ++ b::ₘbs = b::ₘ(as ++ bs) := by
  rw [append_comm, cons_append, append_comm]

@[simp] public theorem mem_append {as bs: Multiset α} : ∀{x}, x ∈ as ++ bs ↔ x ∈ as ∨ x ∈ bs := by
  induction as using ind
  induction bs using ind
  intro x; apply List.mem_append

@[induction_eliminator]
public theorem induction
  {motive: Multiset α -> Prop}
  (nil: motive nil)
  (cons: ∀a as, motive as -> motive (a::ₘas))
  (ms: Multiset α) : motive ms := by
  induction ms using ind with | _ ms =>
  induction ms with
  | nil => exact nil
  | cons a as ih => exact cons a (mk as) ih

public def eraseDups [DecidableEq α] : Multiset α -> Multiset α :=
  lift (fun as => mk as.eraseDups) <| by
    intro  as bs h; apply sound
    show as.eraseDups.Perm bs.eraseDups
    apply (List.perm_ext_iff_of_nodup' _ _).mpr
    intro a; simp; apply h.mem_iff
    exact List.nodup_eraseDups as
    exact List.nodup_eraseDups bs

theorem perm_nodup (as bs: List α) (h: as ≈ bs) (ha: as.Nodup) : bs.Nodup := by
  induction h with
  | nil => assumption
  | trans _ _ iha ihb =>
    apply ihb
    apply iha
    assumption
  | cons _ h ih =>
    apply List.nodup_cons.mpr
    apply And.intro
    intro g
    exact (List.nodup_cons.mp ha).left (h.mem_iff.mpr g)
    exact ih (List.nodup_cons.mp ha).right
  | swap a b xs =>
    simp at *
    obtain ⟨⟨b_ne_a, b_not_in_xs⟩, a_not_in_xs, xs_nodup⟩ := ha
    have := Ne.symm b_ne_a
    trivial

public def Nodup : Multiset α -> Prop :=
  lift List.Nodup <| by
    intro a b h
    ext; apply Iff.intro <;> apply perm_nodup
    assumption
    apply List.Perm.symm; assumption

public theorem nodup_nil : Nodup (nil (α := α)) := List.nodup_nil
public theorem nodup_cons (a: α) (as: Multiset α) : (a::ₘas).Nodup ↔ a ∉ as ∧ as.Nodup := by
  induction as using ind
  apply List.nodup_cons
public theorem nodup_append {as bs: Multiset α} : (as ++ bs).Nodup ↔ as.Nodup ∧ bs.Nodup ∧ ∀x ∈ as, x ∉ bs := by
  induction as using ind with | _ as =>
  induction bs using ind with | _ bs =>
  apply Iff.trans List.nodup_append
  apply and_congr; apply Iff.rfl
  apply and_congr; apply Iff.rfl
  apply Iff.intro
  intro h x ha hb
  exact h x ha x hb rfl
  intro h a ha b hb rfl
  exact h a ha hb

public theorem mem_eraseDups [DecidableEq α] (as: Multiset α) : ∀x, x ∈ as.eraseDups ↔ x ∈ as := by
  induction as using ind
  intro; apply List.mem_eraseDups

public theorem nodup_eraseDups [DecidableEq α] (as: Multiset α) : as.eraseDups.Nodup := by
  induction as using ind
  apply List.nodup_eraseDups

public def map (f: α -> β) : Multiset α -> Multiset β :=
  lift (mk ∘ List.map f) <| by
    intro a b h; apply sound
    apply List.perm_map
    assumption

@[simp] public theorem map_nil (f: α -> β) : map f nil = nil := rfl
@[simp] public theorem map_cons (f: α -> β) (a: α) (as: Multiset α) : map f (a::ₘas) = f a::ₘmap f as := by
  induction as using ind
  rfl

public def filter (f: α -> Bool) : Multiset α -> Multiset α :=
  lift (mk ∘ List.filter f) <| by
    intro a b h; apply sound
    apply List.perm_filter
    assumption

@[simp] public theorem mem_filter {f: α -> Bool} {ms: Multiset α} : ∀{x}, x ∈ ms.filter f ↔ x ∈ ms ∧ f x := by
  induction ms using ind
  intro x; apply List.mem_filter

public theorem nodup_filter {f: α -> Bool} {ms: Multiset α} :
  ms.Nodup -> (ms.filter f).Nodup  := by
  induction ms using ind
  apply List.nodup_filter

public def length : Multiset α -> ℕ :=
  lift List.length fun _ _ h => h.length_eq

end Multiset
