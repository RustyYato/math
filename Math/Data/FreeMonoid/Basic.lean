module

public import Math.Data.FreeMonoid.Defs

namespace Math

namespace FreeMonoid

attribute [local irreducible] MulOpp

def preReverse : FreeMonoid α -> (FreeMonoid α)ᵐᵒᵖ :=
  fun a => .mk ⟨a.toList.reverse⟩

theorem preReverse_ι_mul (a: α) (as: FreeMonoid α) : preReverse (ι a * as) = MulOpp.mk (ι a) * preReverse as := by
  unfold preReverse
  show MulOpp.mk (ofList (List.reverse ([a] ++ _))) = _
  simp; rfl

def reverseHom : FreeMonoid α →* (FreeMonoid α)ᵐᵒᵖ :=
  GroupHom.copy
    (lift fun i => .mk (ι i))
    preReverse <| by
    intro i
    induction i using list_induction with
    | one => rw [map_one]; rfl
    | ι_mul a b ih => rw [map_mul, lift_ι, preReverse_ι_mul, ih]

theorem reverseHom_ι : reverseHom (ι a) = .mk (ι a) := by
  simp [reverseHom, lift_ι]

theorem reverse_reverse (x: FreeMonoid α) : reverseHom (reverseHom x).get = .mk x := by
  induction x with
  | one => rfl
  | ι => rfl
  | mul a b iha ihb =>
    rw [map_mul]
    show reverseHom (_ * _) = _
    rw [map_mul, iha, ihb]
    rfl

public def reverse : (FreeMonoid α) ≃* (FreeMonoid α)ᵐᵒᵖ where
  toGroupHom := reverseHom
  invFun f := (reverseHom f.get).get
  leftInv x := by
    show reverseHom (reverseHom x.get).get = _
    induction x with | _ x =>
    dsimp; rw [reverse_reverse]
  rightInv x := by
    show (reverseHom (reverseHom x).get).get = _
    rw [reverse_reverse]; rfl

@[simp] public theorem reverse_ι : reverse (ι a) = .mk (ι a) := by
  apply reverseHom_ι

end FreeMonoid

namespace FreeAddMonoid

attribute [local irreducible] AddOpp

def preReverse : FreeAddMonoid α -> (FreeAddMonoid α)ᵃᵒᵖ :=
  fun a => .mk ⟨a.toList.reverse⟩

theorem preReverse_ι_add (a: α) (as: FreeAddMonoid α) : preReverse (ι a + as) = AddOpp.mk (ι a) + preReverse as := by
  unfold preReverse
  show AddOpp.mk (ofList (List.reverse ([a] ++ _))) = _
  simp; rfl

def reverseHom : FreeAddMonoid α →+ (FreeAddMonoid α)ᵃᵒᵖ :=
  AddGroupHom.copy
    (lift fun i => .mk (ι i))
    preReverse <| by
    intro i
    induction i using list_induction with
    | zero => rw [map_zero]; rfl
    | ι_add a b ih => rw [map_add, lift_ι, preReverse_ι_add, ih]

theorem reverseHom_ι : reverseHom (ι a) = .mk (ι a) := by
  simp [reverseHom, lift_ι]

theorem reverse_reverse (x: FreeAddMonoid α) : reverseHom (reverseHom x).get = .mk x := by
  induction x with
  | zero => rfl
  | ι => rfl
  | add a b iha ihb =>
    rw [map_add]
    show reverseHom (_ + _) = _
    rw [map_add, iha, ihb]
    rfl

public def reverse : (FreeAddMonoid α) ≃+ (FreeAddMonoid α)ᵃᵒᵖ where
  toAddGroupHom := reverseHom
  invFun f := (reverseHom f.get).get
  leftInv x := by
    show reverseHom (reverseHom x.get).get = _
    induction x with | _ x =>
    dsimp; rw [reverse_reverse]
  rightInv x := by
    show (reverseHom (reverseHom x).get).get = _
    rw [reverse_reverse]; rfl

@[simp] public theorem reverse_ι : reverse (ι a) = .mk (ι a) := by
  apply reverseHom_ι

end FreeAddMonoid
