module

public import Math.Algebra.Semigroup.Defs.Basic
public import Math.Algebra.Congruence.Defs

namespace Math

section

variable [RelLike C α] [IsCon C α]

public instance [Mul α] [IsSemigroup α] [IsMulCon C α] (r: C) : IsSemigroup (AlgQuot r) where
  mul_assoc a b c := by
    induction a
    induction b
    induction c
    show AlgQuot.mk r _ = AlgQuot.mk r _
    rw [mul_assoc]

public instance [Mul α] [IsComm α] [IsMulCon C α] (r: C) : IsComm (AlgQuot r) where
  mul_comm a b := by
    induction a
    induction b
    show AlgQuot.mk r _ = AlgQuot.mk r _
    rw [mul_comm]

public instance [Add α] [IsAddSemigroup α] [IsAddCon C α] (r: C) : IsAddSemigroup (AlgQuot r) where
  add_assoc a b c := by
    induction a
    induction b
    induction c
    show AlgQuot.mk r _ = AlgQuot.mk r _
    rw [add_assoc]

public instance [Add α] [IsAddComm α] [IsAddCon C α] (r: C) : IsAddComm (AlgQuot r) where
  add_comm a b := by
    induction a
    induction b
    show AlgQuot.mk r _ = AlgQuot.mk r _
    rw [add_comm]

end

namespace AddCon

@[expose] public def eq (α: Type*) [Add α] : AddCon α where
  toRel a b := a = b
  toEquiv := by apply eqv
  resp_add := by intro a b c d rfl rfl; rfl

@[expose] public def pullback {α β: Type*}
  [Funlike F α β] [Add α] [Add β]
  [IsAddHom F α β]
  (f: F) (r: AddCon β)
  : AddCon α where
  toRel a b := r (f a) (f b)
  toEquiv := by apply eqv
  resp_add := by
    intro a b c d h g
    rw [map_add f, map_add f]; apply resp_add <;> assumption

inductive Generate (r: α -> α -> Prop) [Add α] : α -> α -> Prop where
| refl (a: α) : Generate r a a
| symm {a b: α} : Generate r a b -> Generate r b a
| trans {a b c: α} : Generate r a b -> Generate r b c -> Generate r a c
| add (a b c d: α) : Generate r a c -> Generate r b d -> Generate r (a + b) (c + d)
| of (a b: α) : r a b -> Generate r a b

public def generate [Add α] (r: α -> α -> Prop) : AddCon α where
  toRel := Generate r
  toEquiv := ⟨Generate.refl, Generate.symm, Generate.trans⟩
  resp_add := Generate.add

variable [Add α] {r: α -> α -> Prop}

public theorem to_generate (h: r a b) : AddCon.generate r a b := by
  exact Generate.of _ _ h

public theorem of_generate
  [Add β] [RelLike C β] [IsAddCon C β]
  [Funlike F α β] [IsAddHom F α β]
  {r: α -> α -> Prop}
  (c: C) (f: F) (hf: respects_rel f r c) :
  respects_rel f (AddCon.generate r) c := by
  intro a b h
  induction h with
  | refl => apply refl
  | symm => apply symm; assumption
  | trans => apply htrans; assumption; assumption
  | add => rw [map_add f, map_add f]; apply resp_add c <;> assumption
  | of => apply hf; assumption

end AddCon

namespace MulCon

@[expose] public def eq (α: Type*) [Mul α] : MulCon α where
  toRel a b := a = b
  toEquiv := by apply eqv
  resp_mul := by intro a b c d rfl rfl; rfl

@[expose] public def pullback {α β: Type*}
  [Funlike F α β] [Mul α] [Mul β]
  [IsMulHom F α β]
  (f: F) (r: MulCon β)
  : MulCon α where
  toRel a b := r (f a) (f b)
  toEquiv := by apply eqv
  resp_mul := by
    intro a b c d h g
    rw [map_mul f, map_mul f]; apply resp_mul <;> assumption

inductive Generate (r: α -> α -> Prop) [Mul α] : α -> α -> Prop where
| refl (a: α) : Generate r a a
| symm {a b: α} : Generate r a b -> Generate r b a
| trans {a b c: α} : Generate r a b -> Generate r b c -> Generate r a c
| mul (a b c d: α) : Generate r a c -> Generate r b d -> Generate r (a * b) (c * d)
| of (a b: α) : r a b -> Generate r a b

public def generate [Mul α] (r: α -> α -> Prop) : MulCon α where
  toRel := Generate r
  toEquiv := ⟨Generate.refl, Generate.symm, Generate.trans⟩
  resp_mul := Generate.mul

variable [Mul α] {r: α -> α -> Prop}

public theorem to_generate (h: r a b) : MulCon.generate r a b := by
  exact Generate.of _ _ h

public theorem of_generate
  [Mul β] [RelLike C β] [IsMulCon C β]
  [Funlike F α β] [IsMulHom F α β]
  {r: α -> α -> Prop}
  (c: C) (f: F) (hf: respects_rel f r c) :
  respects_rel f (MulCon.generate r) c := by
  intro a b h
  induction h with
  | refl => apply refl
  | symm => apply symm; assumption
  | trans => apply htrans; assumption; assumption
  | mul => rw [map_mul f, map_mul f]; apply resp_mul c <;> assumption
  | of => apply hf; assumption

end MulCon

namespace RingCon

@[expose] public def eq (α: Type*) [Add α] [Mul α] : RingCon α where
  toRel a b := a = b
  toEquiv := by apply eqv
  resp_add := by intro a b c d rfl rfl; rfl
  resp_mul := by intro a b c d rfl rfl; rfl

@[expose] public def pullback {α β: Type*}
  [Funlike F α β] [Add α] [Mul α] [Add β] [Mul β]
  [IsAddHom F α β] [IsMulHom F α β]
  (f: F) (r: RingCon β)
  : RingCon α where
  toRel a b := r (f a) (f b)
  toEquiv := by apply eqv
  resp_add := by
    intro a b c d h g
    rw [map_add f, map_add f]; apply resp_add <;> assumption
  resp_mul := by
    intro a b c d h g
    rw [map_mul f, map_mul f]; apply resp_mul <;> assumption

inductive Generate (r: α -> α -> Prop) [Add α] [Mul α] : α -> α -> Prop where
| refl (a: α) : Generate r a a
| symm {a b: α} : Generate r a b -> Generate r b a
| trans {a b c: α} : Generate r a b -> Generate r b c -> Generate r a c
| add (a b c d: α) : Generate r a c -> Generate r b d -> Generate r (a + b) (c + d)
| mul (a b c d: α) : Generate r a c -> Generate r b d -> Generate r (a * b) (c * d)
| of (a b: α) : r a b -> Generate r a b

public def generate [Add α] [Mul α] (r: α -> α -> Prop) : RingCon α where
  toRel := Generate r
  toEquiv := ⟨Generate.refl, Generate.symm, Generate.trans⟩
  resp_add := Generate.add
  resp_mul := Generate.mul

variable [Add α] [Mul α] {r: α -> α -> Prop}

public theorem to_generate (h: r a b) : RingCon.generate r a b := by
  exact Generate.of _ _ h

public theorem of_generate
  [Add β] [Mul β] [RelLike C β] [IsAddCon C β] [IsMulCon C β]
  [Funlike F α β] [IsAddHom F α β] [IsMulHom F α β]
  {r: α -> α -> Prop}
  (c: C) (f: F) (hf: respects_rel f r c) :
  respects_rel f (RingCon.generate r) c := by
  intro a b h
  induction h with
  | refl => apply refl
  | symm => apply symm; assumption
  | trans => apply htrans; assumption; assumption
  | add => rw [map_add f, map_add f]; apply resp_add c <;> assumption
  | mul => rw [map_mul f, map_mul f]; apply resp_mul c <;> assumption
  | of => apply hf; assumption

end RingCon
