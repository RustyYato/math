import LeanMath.Algebra.Monoid.Defs
import LeanMath.Data.Embedding.Defs
import LeanMath.Data.Equiv.Defs

structure FreeMonoid (α: Type*) where
  ofList :: toList : List α

namespace FreeMonoid

instance : One (FreeMonoid α) where
  one := .ofList []
instance : Mul (FreeMonoid α) where
  mul a b := .ofList <| a.toList ++ b.toList
instance : Pow (FreeMonoid α) ℕ := defaultPowN

def ι : α ↪ FreeMonoid α where
  toFun x := .ofList [x]
  inj _ _ h := (List.cons.inj (FreeMonoid.ofList.inj h)).left

instance : IsSemigroup (FreeMonoid α) where
  mul_assoc := by
    intro a b c
    cases a with | ofList a =>
    cases b with | ofList b =>
    cases c with | ofList c =>
    show FreeMonoid.ofList (a ++ b ++ c) = FreeMonoid.ofList (a ++ (b ++ c))
    rw [List.append_assoc]

instance : IsLawfulOneMul (FreeMonoid α) where
  one_mul _ := rfl
  mul_one a := by
    cases a with | ofList a =>
    show FreeMonoid.ofList (a ++ []) = FreeMonoid.ofList a
    rw [List.append_nil]

instance : IsMonoid (FreeMonoid α) where

variable [MonoidOps M] [IsMonoid M]

private def preLift (f: α -> M) : List α -> M
| [] => 1
| a::as => f a * preLift f as

private def preLift_nil (f: α -> M) : preLift f [] = 1 := rfl
private def preLift_mul (f: α -> M) (as bs: List α) : preLift f (as ++ bs) = preLift f as * preLift f bs := by
  induction as with
  | nil => rw [preLift_nil, one_mul]; rfl
  | cons a as ih => rw [List.cons_append, preLift, preLift, ih, mul_assoc]
private def preLift_ι (f: α -> M) (a: α) : preLift f [a] = f a := by rw [preLift, preLift_nil, mul_one]

def lift [MonoidOps M] [IsMonoid M] : (α -> M) ≃ (FreeMonoid α →* M) where
  toFun f := {
    toFun x := preLift f x.toList
    map_one := rfl
    map_mul _ _ := by apply preLift_mul
  }
  invFun f := f ∘ ι
  leftInv f := by
    ext x
    cases x with | ofList x =>
    show preLift (f ∘ ι) x = _
    induction x with
    | nil => show 1 = f 1; rw [map_one]
    | cons x xs ih =>
      rw [preLift]; dsimp
      show _ = f (ι x * .ofList xs)
      rw [map_mul, ih]
  rightInv f := by
    ext x
    apply preLift_ι

@[simp] def lift_ι (f: α -> M) (x: α) : lift f (ι x) = f x := by
  apply preLift_ι

def ι_induction
  (motive: FreeMonoid α -> Prop)
  (one: motive 1)
  (ι_mul: ∀a b, motive b -> motive (ι a * b))
  (a: FreeMonoid α) : motive a := by
  cases a with | ofList a =>
  induction a with
  | nil => apply one
  | cons x xs ih =>
    apply ι_mul
    assumption
@[induction_eliminator]
def induction
  (motive: FreeMonoid α -> Prop)
  (one: motive 1)
  (ι: ∀x, motive (ι x))
  (mul: ∀a b, motive a -> motive b -> motive (a * b))
  (a: FreeMonoid α) : motive a := by
  cases a with | ofList a =>
  induction a with
  | nil => apply one
  | cons x xs ih =>
    apply mul (.ι x)
    apply ι
    assumption

private def preReverse (m: FreeMonoid α) : FreeMonoid α where
  toList := m.toList.reverse

private def preReverse_one : preReverse (α := α) 1 = 1 := rfl
private def preReverse_ι (a: α) : preReverse (ι a) = ι a := rfl
private def preReverse_ι_mul (a: α) (b: FreeMonoid α) : preReverse (ι a * b) = preReverse b * preReverse (ι a) := by
  rw [preReverse]
  show (FreeMonoid.ofList ([a] ++ b.toList).reverse) = _
  rw [List.reverse_append]
  rfl
private def preReverse_mul (a b: FreeMonoid α) : preReverse (a * b) = preReverse b * preReverse a := by
  induction a using ι_induction generalizing b with
  | one => rw [one_mul, preReverse_one, mul_one]
  | ι_mul x as ih₀ => rw [mul_assoc, preReverse_ι_mul, ih₀, preReverse_ι_mul, mul_assoc]

def reverse : FreeMonoid α →* MulOpp (FreeMonoid α) where
  toFun x := MulOpp.mk x.preReverse
  map_one := rfl
  map_mul := preReverse_mul

@[simp] def reverse_ι (a: α) : reverse (ι a) = MulOpp.mk (ι a) := rfl

def ι_eq_mul (a: α) (x y: FreeMonoid α) : ι a = x * y -> x = 1 ∧ y = ι a ∨ x = ι a ∧ y = 1 := by
  intro h
  cases x with | ofList x =>
  cases y with | ofList y =>
  unfold ι at h
  replace h : [a] = x ++ y := ofList.inj h
  replace h := List.singleton_eq_append_iff.mp h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  left; apply And.intro rfl rfl
  right; apply And.intro rfl rfl

def ι_ne_one (a: α) : ι a ≠ 1 := by
  intro h
  have := ofList.inj h
  contradiction

attribute [irreducible] lift ι reverse

def lift_ι' : lift ι = GroupHom.id (FreeMonoid α) := by
  ext x; simp
  induction x with
  | one => rw [map_one]
  | ι x => rw [lift_ι]
  | mul a b iha ihb => rw [map_mul, iha, ihb]

def lift_comp [MonoidOps N] [IsMonoid N] (f: M →* N) (g: α -> M) : lift (f ∘ g) = f ∘ lift g := by
  ext x; simp
  induction x with
  | one => rw [map_one, map_one, map_one]
  | ι x => rw [lift_ι, lift_ι]; rfl
  | mul a b iha ihb => rw [map_mul, map_mul, map_mul, iha, ihb]

instance [Subsingleton α] : IsComm (FreeMonoid α) where
  mul_comm a b := by
    induction a with
    | one => rw [mul_one, one_mul]
    | ι a =>
      induction b with
      | one => rw [mul_one, one_mul]
      | ι b => rw [Subsingleton.allEq a b]
      | mul b₀ b₁ ih₀ ih₁ => rw [←mul_assoc, ih₀, mul_assoc, ih₁, mul_assoc]
    | mul a₀ a₁ ih₀ ih₁ => rw [mul_assoc, ih₁, ←mul_assoc, ih₀, mul_assoc]

end FreeMonoid
