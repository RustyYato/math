module

public import Math.Algebra.Module.Defs
public import Math.Algebra.Module.Hom.Defs
public import Math.Algebra.Semiring.Congruence

namespace Math

section

variable (C R α: Type*)
  [SemiringOps R] [IsSemiring R]
  [AddMonoidOps α] [IsAddMonoid α]
  [SMul R α] [IsModule R α]
  [RelLike C α] [IsAddCon C α] [IsSMulCon C R α]
  (c: C)

instance : IsModule R (AlgQuot c) where
  smul_add r a b := by
    induction a using AlgQuot.ind with | _ a =>
    induction b using AlgQuot.ind with | _ b =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [smul_add]
  add_smul r s a := by
    induction a using AlgQuot.ind with | _ a =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [add_smul]
  mul_smul r s a := by
    induction a using AlgQuot.ind with | _ a =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [mul_smul]
  one_smul a := by
    induction a using AlgQuot.ind with | _ a =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [one_smul]
  zero_smul a := by
    induction a using AlgQuot.ind with | _ a =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [zero_smul]
  smul_zero r := by
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [smul_zero]

end

namespace LinearCon

@[expose] public def eq (α: Type*) [Add α] [SMul K α] : LinearCon K α where
  toRel a b := a = b
  toEquiv := by apply eqv
  resp_add := by intro a b c d rfl rfl; rfl
  resp_smul := by intro a b c rfl; rfl

@[expose] public def pullback {α β: Type*}
  [Funlike F α β] [Add α] [SMul K α] [Add β] [SMul K β]
  [IsAddHom F α β] [IsSMulHom F K α β]
  (f: F) (r: LinearCon K β)
  : LinearCon K α where
  toRel a b := r (f a) (f b)
  toEquiv := by apply eqv
  resp_add := by
    intro a b c d h g
    rw [map_add f, map_add f]; apply resp_add <;> assumption
  resp_smul := by
    intro a b c h
    rw [map_smul f, map_smul f]; apply resp_smul <;> assumption

inductive Generate (K: Type*) (r: α -> α -> Prop) [Add α] [SMul K α] : α -> α -> Prop where
| refl (a: α) : Generate K r a a
| symm {a b: α} : Generate K r a b -> Generate K r b a
| trans {a b c: α} : Generate K r a b -> Generate K r b c -> Generate K r a c
| add (a b c d: α) : Generate K r a c -> Generate K r b d -> Generate K r (a + b) (c + d)
| smul (k: K) (a b: α) : Generate K r a b -> Generate K r (k • a) (k • b)
| of (a b: α) : r a b -> Generate K r a b

public def generate (K: Type*) [Add α] [SMul K α] (r: α -> α -> Prop) : LinearCon K α where
  toRel := Generate K r
  toEquiv := ⟨Generate.refl, Generate.symm, Generate.trans⟩
  resp_add := Generate.add
  resp_smul := Generate.smul

variable [Add α] [SMul K α] {r: α -> α -> Prop}

public theorem to_generate (h: r a b) : LinearCon.generate K r a b := by
  exact Generate.of _ _ h

public theorem of_generate
  [Add β] [SMul K β] [RelLike C β] [IsAddCon C β] [IsSMulCon C K β]
  [Funlike F α β] [IsAddHom F α β] [IsSMulHom F K α β]
  {r: α -> α -> Prop}
  (c: C) (f: F) (hf: respects_rel f r c) :
  respects_rel f (LinearCon.generate K r) c := by
  intro a b h
  induction h with
  | refl => apply refl
  | symm => apply symm; assumption
  | trans => apply htrans; assumption; assumption
  | add => rw [map_add f, map_add f]; apply resp_add c <;> assumption
  | smul => rw [map_smul f, map_smul f]; apply resp_smul c <;> assumption
  | of => apply hf; assumption

end LinearCon
