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
    | ι a r => simp [smul_ι, add_smul, map_add]
    | add a b iha ihb =>
      simp [smul_add, iha, ihb]
      ac_rfl

variable
  {R M: Type*}
  [AddMonoidOps M] [IsAddMonoid M] [IsAddComm M]
  [SemiringOps R] [IsSemiring R]
  [SMul R M] [IsModule R M]

def liftLin : (α -> M) ≃ (LinearCombo R α →ₗ[R] M) where
  toFun f := {
    toFun := lift (fun a => {
      toFun r := r • f a
      map_zero := by rw [zero_smul]
      map_add x y := by rw [add_smul]
    })
    map_add := map_add _
    map_smul r a := by
      show lift _ _ = r • lift _ _
      induction a with
      | zero => rw [map_zero, smul_zero, smul_zero, map_zero]
      | add a b iha ihb => rw [map_add, smul_add, smul_add, map_add, iha, ihb]
      | ι a r' =>
        rw [smul_ι, lift_ι, lift_ι]
        show (r • r') • f a = r • r' • f a
        rw [←mul_smul]; rfl
  }
  invFun f := f ∘ (ι · 1)
  leftInv f := by
    dsimp; apply DFunLike.ext; intro l
    show lift _ l = f l
    induction l with
    | zero => rw [map_zero, map_zero]
    | add a b iha ihb => rw [map_add, map_add, iha, ihb]
    | ι a r =>
      rw [lift_ι]
      show r • f (ι a 1) = _
      rw [←map_smul, smul_ι]
      congr; apply mul_one
  rightInv f := by
    dsimp; ext a; simp
    show lift _ _ = _
    rw [lift_ι]
    apply one_smul

def liftLin_ι (f: α -> M) (a: α) (r: R) : liftLin f (ι a r) = r • f a := lift_ι _ _ _

@[simp]
def lift_ι₁ (f: α -> M) (a: α) : liftLin f (ι a (1: R)) = f a := by rw [liftLin_ι, one_smul]

attribute [irreducible] liftLin

-- for any non-trivial ground semiring, the ι function is injective
def ι_inj [Nontrivial R] : Function.Injective (ι · (1: R) (α := α)) := by
  intro a b h
  simp at h
  classical
  let f := liftLin (M := R) (R := R) (α := α) (fun x => if x = b then 0 else 1)
  replace h₀ : f (ι b 1) = 0 := by simp [f]
  replace h₀ : f (ι a 1) = 0 := by rw [h, h₀]
  simp [f] at h₀
  apply Classical.byContradiction
  intro g
  have := h₀ g
  contradiction

end LinearCombo
