import LeanMath.Tactic.TypeStar

namespace Nat

variable
  {motive: ℕ -> Sort u}
  (ind: ∀x, (∀y, y < x -> motive y) -> motive x)
  (funext': ∀(x: ℕ) (f g: ∀y, y < x -> motive y),
    (∀y hy, f y hy = g y hy) -> ind x f = ind x g)

def strongRec.go (x fuel: ℕ) (h: x < fuel) : motive x :=
  match fuel with
  | fuel + 1 =>
  ind _ (fun y hy => go y fuel (by
    apply Nat.lt_of_lt_of_le hy
    apply Nat.le_of_lt_succ
    assumption))

def strongRec.go_fuel_irr
  {fuel₀ fuel₁ h₀ h₁} :
  go ind x fuel₀ h₀ = go ind x fuel₁ h₁ := by
  induction x using Nat.strongRecOn generalizing fuel₀ fuel₁ with
  | _ n ih =>
  match fuel₀, fuel₁ with
  | fuel₀ + 1, fuel₁ + 1 =>
  unfold go
  apply funext'
  intro y hy
  apply ih
  assumption

def strongRec (x: ℕ) : motive x :=
  strongRec.go ind x (x + 1) (Nat.lt_succ_self _)

def step_strongRec (x: ℕ) : strongRec ind x = ind x (fun y _ => strongRec ind y) := by
  rw [strongRec]; unfold strongRec.go
  apply funext'
  intro y hy
  apply strongRec.go_fuel_irr
  assumption

end Nat
