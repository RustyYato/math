module

public import Math.Algebra.Module.Congruence
public import Math.Algebra.Module.Defs.OfEquiv

namespace Math

public structure LinearQuot (R: Type*) {α: Type*} [Add α] [SMul R α] (r: α -> α -> Prop) where
  ofQuot :: toQuot : AlgQuot (LinearCon.generate R r)

namespace LinearQuot

section

variable (R: Type*) [Add α] [SMul R α]

@[local ext]
theorem ext {r: α -> α -> Prop} (a b: LinearQuot R r) (h: a.toQuot = b.toQuot) : a = b := by
  cases a; cases b; congr

variable {r: α -> α -> Prop}

def ofQuot' (r: α -> α -> Prop) : AlgQuot (LinearCon.generate R r) ≃ LinearQuot R r where
  toFun := LinearQuot.ofQuot
  invFun := LinearQuot.toQuot
  leftInv _ := rfl
  rightInv _ := rfl

end

variable {r: α -> α -> Prop}

public instance [Zero α] [Add α] [SMul R α] : Zero (LinearQuot R r) where
  zero := ⟨0⟩
public instance [Add α] [SMul R α] : Add (LinearQuot R r) where
  add a b := ⟨a.toQuot + b.toQuot⟩
public instance [Add α] [SMul R α] : SMul R (LinearQuot R r) where
  smul r a := ⟨r • a.toQuot⟩
public instance [AddMonoidOps α] [IsAddMonoid α] [SMul R α] : SMul ℕ (LinearQuot R r) where
  smul r a := ⟨r • a.toQuot⟩

public instance [AddMonoidOps α] [IsAddMonoid α] [SMul R α] : IsAddMonoid (LinearQuot R r) :=
  OfEquiv.instIsAddMonoid (ofQuot' R r)

public instance [Add α] [IsAddComm α] [SMul R α] : IsAddComm (LinearQuot R r) :=
  OfEquiv.instIsAddComm (ofQuot' R r)

@[expose] public def mk (R: Type*) [Add α] [SMul R α] (r: α -> α -> Prop) : α →ₗ[R] LinearQuot R r where
  toFun := ofQuot ∘ AlgQuot.mk (LinearCon.generate R r)
  map_add _ _ := rfl
  map_smul _ _ := rfl

public theorem sound [Add α] [SMul R α] {a b: α} : r a b -> mk R r a = mk R r b := by
  intro h; unfold mk
  show ⟨AlgQuot.mk _ _⟩ = ofQuot (AlgQuot.mk _ _)
  congr 1; apply AlgQuot.sound
  apply LinearCon.to_generate
  assumption

public theorem exact [Add α] [SMul R α] {a b: α} : mk R r a = mk R r b -> LinearCon.generate R r a b := by
  intro h;
  exact AlgQuot.exact (ofQuot.inj h)

@[induction_eliminator]
public theorem ind [Add α] [SMul R α] {motive: LinearQuot R r -> Prop} (mk: ∀a, motive (mk R r a)) (q: LinearQuot R r) : motive q := by
  obtain ⟨q⟩ := q
  induction q with | _ q =>
  apply mk

variable [Add α] [SMul R α] [Add L] [SMul R L]

def preLift (f: α →ₗ[R] L) (hf: ∀a b, r a b -> f a = f b) : LinearQuot R r →ₗ[R] L where
  toFun q := q.toQuot.lift f <| by
    intro a b h
    apply LinearCon.of_generate (C := LinearCon R _) (LinearCon.eq _) f _ h
    assumption
  map_add a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    apply map_add (α := α) f a b
  map_smul a b := by
    induction b with | _ b =>
    apply map_smul (α := α) f a b

theorem preLift_mk (f: α →ₗ[R] L) (hf: ∀a b, r a b -> f a = f b) : preLift f hf (mk R r x) = f x := rfl

public def lift : { f: α →ₗ[R] L // ∀a b, r a b -> f a = f b } ≃ (LinearQuot R r →ₗ[R] L) where
  toFun f := preLift f.val f.property
  invFun f := {
    val := f.comp (mk R r)
    property := by
      intro a b h; dsimp; congr 1
      apply LinearQuot.sound
      assumption
  }
  leftInv f := by ext a; induction a with | _ a => rfl
  rightInv f := by ext a; rfl

public theorem lift_mk (f: { f: α →ₗ[R] L // ∀a b, r a b -> f a = f b }) : lift f (mk R r x) = f.val x := by
  unfold lift
  rfl
