private def Setoid.trivial (α: Sort u) : Setoid α where
  r _ _ := True
  iseqv := {
    refl _ := True.intro
    symm _ := True.intro
    trans _ _ := True.intro
  }

def Trunc (α: Sort u) := Quotient (Setoid.trivial α)

namespace Trunc

def mk {α: Sort u} : α -> Trunc α := Quotient.mk _

def lift (f: α -> β) (h: ∀a b, f a = f b) : Trunc α -> β := Quotient.lift f (fun a b _ => h a b)
def rec
  {motive: Trunc α -> Sort u}
  [∀a, Subsingleton (motive a)]
  (mk: ∀a, motive (mk a)) : ∀x, motive x := by
  apply Quotient.recOnSubsingleton (motive := motive) (f := mk)
@[induction_eliminator]
def ind {motive: Trunc α -> Prop} (mk: ∀a, motive (mk a)) : ∀x, motive x := Quotient.ind mk

instance : Subsingleton (Trunc α) where
  allEq a b := by
    induction a with | mk a =>
    induction b with | mk b =>
    apply Quotient.sound
    exact True.intro

def bind (f: α -> Trunc β) : Trunc α -> Trunc β :=
  lift f <| by
    intro a b
    apply Subsingleton.allEq

def map (f: α -> β) : Trunc α -> Trunc β :=
  bind (mk ∘ f)

end Trunc
