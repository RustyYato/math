namespace Relation

inductive ReflGen (R: α -> α -> Prop) : α -> α -> Prop where
| refl (a: α) : ReflGen R a a
| of (a b: α) : R a b -> ReflGen R a b

inductive ReflTransGen (R: α -> α -> Prop) : α -> α -> Prop where
| refl (a: α) : ReflTransGen R a a
| cons (a b c: α) : R a b -> ReflTransGen R b c -> ReflTransGen R a c

def ReflTransGen.trans : ReflTransGen R a b -> ReflTransGen R b c -> ReflTransGen R a c := by
  intro h g
  induction h generalizing c with
  | refl => assumption
  | cons _ _ _ _ _ ih =>
    apply ReflTransGen.cons
    assumption
    apply ih
    assumption

end Relation
