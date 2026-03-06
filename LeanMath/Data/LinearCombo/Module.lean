import LeanMath.Data.LinearCombo.Defs
import LeanMath.Algebra.Module.Defs
import LeanMath.Logic.Nontrivial

namespace LinearCombo

instance
  {R S α: Type*}
  [AddMonoidOps R] [IsAddMonoid R] [IsAddComm R]
  [SemiringOps S] [IsSemiring S]
  [SMul S R] [IsModule S R]
  : IsModule S (LinearCombo R α) where
  zero_smul a := by
    induction a with
    | zero => rw [smul_zero]
    | ι => rw [smul_ι, zero_smul, map_zero]
    | add _ _ iha ihb => rw [smul_add, iha, ihb, add_zero]
  add_smul s₀ s₁ a := by
    induction a with
    | zero => simp [smul_zero, add_zero]
    | ι a r => simp [add_smul, map_add]
    | add a b iha ihb =>
      simp [smul_add, iha, ihb]
      ac_rfl

variable
  {R M: Type*}
  [AddMonoidOps M] [IsAddMonoid M] [IsAddComm M]
  [SemiringOps R] [IsSemiring R]
  [SMul R M] [IsModule R M]

private def Pre.lift (f: α -> M) : Pre R α -> M
| .zero => 0
| .of r a => r • f a
| .add a b => Pre.lift f a + Pre.lift f b

private def preLift (f: α -> M) : LinearCombo R α →ₗ[R] M where
  toFun := liftPre (Pre.lift f) <| by
    intro a b h
    induction h with
    | refl => rfl
    | symm => symm; assumption
    | trans _ _ iha ihb => rw [iha, ihb]
    | zero => apply zero_smul
    | zero_add => apply zero_add
    | add_of => apply add_smul
    | add_comm => apply add_comm
    | add_assoc => apply add_assoc
    | add_congr =>
      show _ + _ = _ + _
      congr
  map_add := by
    intro a b
    induction a using ind with | _ =>
    induction b using ind with | _ =>
    rfl
  map_smul r a := by
    induction a using ind with | _ a =>
    show Pre.lift f (a.smul r) = r • Pre.lift f a
    induction a with
    | zero => symm; apply smul_zero
    | of => apply mul_smul
    | add =>
      show _ + _ = r • (_ + _)
      rw [smul_add]
      congr

unseal ι in
private def preLift_ι (f: α -> M) (a: α) (r: R) : preLift f (ι a r) = r • f a := rfl

def lift : (α -> M) ≃ (LinearCombo R α →ₗ[R] M) where
  toFun := preLift
  invFun f := f ∘ (ι · 1)
  leftInv f := by
    apply DFunLike.ext; intro l
    induction l with
    | zero => rw [map_zero, map_zero]
    | ι =>
      rw [preLift_ι]
      simp [←map_smul, smul_ι]
      congr; apply mul_one
    | add a b iha ihb  => rw [map_add, map_add]; congr
  rightInv f := by
    apply DFunLike.ext; intro a
    dsimp
    show preLift f (ι a 1) = f a
    rw [preLift_ι, one_smul]

def lift_ι (f: α -> M) (a: α) (r: R) : lift f (ι a r) = r • f a := preLift_ι _ _ _

@[simp]
def lift_ι₁ (f: α -> M) (a: α) : lift f (ι a (1: R)) = f a := by rw [lift_ι, one_smul]

attribute [irreducible] lift

-- for any non-trivial ground semiring, the ι function is injective
def ι_inj [Nontrivial R] : Function.Injective (ι · (1: R) (α := α)) := by
  intro a b h
  simp at h
  classical
  let f := lift (M := R) (R := R) (α := α) (fun x => if x = b then 0 else 1)
  replace h₀ : f (ι b 1) = 0 := by simp [f]
  replace h₀ : f (ι a 1) = 0 := by rw [h, h₀]
  simp [f] at h₀
  apply Classical.byContradiction
  intro g
  have := h₀ g
  contradiction

end LinearCombo
