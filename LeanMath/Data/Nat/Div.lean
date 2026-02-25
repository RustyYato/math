import LeanMath.Tactic.AxiomBlame

private theorem div.go.fuel_congr (x y fuel1 fuel2 : Nat) (hy : 0 < y) (h1 : x < fuel1) (h2 : x < fuel2) :
    Nat.div.go y hy fuel1 x h1 = Nat.div.go y hy fuel2 x h2 := by
  match fuel1, fuel2 with
  | 0, _ => contradiction
  | _, 0 => contradiction
  | .succ fuel1, .succ fuel2  =>
    simp only [Nat.div.go]
    split
    next => rw [div.go.fuel_congr]
    next => rfl
termination_by structural fuel1

theorem nat_div_eq (x y : Nat) : x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 := by
  change Nat.div _ _ = ite _ (Nat.div _ _ + 1) _
  unfold Nat.div
  split
  next =>
    rw [Nat.div.go]
    split
    next =>
      rw [if_pos (And.intro (by assumption) (by assumption))]
      congr 1
      apply div.go.fuel_congr
    next =>
      rw [if_neg]
      intro ⟨_, _⟩
      contradiction
  next =>
    rw [if_neg]
    intro ⟨_, _⟩
    contradiction

private theorem modCore.go.fuel_congr (x y fuel1 fuel2 : Nat) (hy : 0 < y) (h1 : x < fuel1) (h2 : x < fuel2) :
    Nat.modCore.go y hy fuel1 x h1 = Nat.modCore.go y hy fuel2 x h2 := by
  match fuel1, fuel2 with
  | 0, _ => contradiction
  | _, 0 => contradiction
  | .succ fuel1, .succ fuel2  =>
    simp only [Nat.modCore.go]
    split
    next => rw [modCore.go.fuel_congr]
    next => rfl
termination_by structural fuel1

private theorem modCore_eq (x y : Nat) : Nat.modCore x y =
  if 0 < y ∧ y ≤ x then
    Nat.modCore (x - y) y
  else
    x := by
  unfold Nat.modCore
  split
  next =>
    rw [Nat.modCore.go]
    split
    next =>
      rw [if_pos (And.intro (by assumption) (by assumption))]
      apply modCore.go.fuel_congr
    next =>
      rw [if_neg]
      intro ⟨_, _⟩
      contradiction
  next =>
    rw [if_neg]
    intro ⟨_, _⟩
    contradiction

private theorem modCore_eq_mod (n m : Nat) : Nat.modCore n m = n % m := by
  change Nat.modCore n m = Nat.mod n m
  match n, m with
  | 0, _ =>
    rw [modCore_eq]
    exact if_neg fun ⟨hlt, hle⟩ => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hle)
  | (_ + 1), _ =>
    rw [Nat.mod]; dsimp
    refine iteInduction (fun _ => rfl) (fun h => ?false) -- cannot use `split` this early yet
    rw [modCore_eq]
    exact if_neg fun ⟨_hlt, hle⟩ => h hle

theorem nat_mod_eq (x y : Nat) : x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x := by
  rw [←modCore_eq_mod, ←modCore_eq_mod, modCore_eq]

def nat_div_add_mod (a b: Nat) : b * (a / b) + a % b = a := by
  induction a, b using Nat.div.inductionOn with
  | base a b h =>
    rw [nat_div_eq, if_neg h, nat_mod_eq, if_neg h, Nat.mul_zero, Nat.zero_add]
  | ind a b h ih =>
    rw [nat_div_eq, if_pos h, nat_mod_eq, if_pos h]
    rw [Nat.mul_succ, Nat.add_comm _ b, Nat.add_assoc, ih, Nat.add_comm]
    clear ih
    obtain ⟨g, h⟩ := h
    clear g
    induction a generalizing b with
    | zero =>
      cases Nat.le_zero.mp h
      rfl
    | succ a ih =>
      cases b with
      | zero => rfl
      | succ b =>
        rw [Nat.succ_sub_succ, Nat.add_succ]
        rw [ih]
        apply Nat.le_of_succ_le_succ
        assumption

def nat_div2_rec_lemma (n: Nat) (h: n ≠ 0) : n / 2 < n := by
  rw (occs := [2]) [←nat_div_add_mod n 2]
  rw [←nat_div_add_mod n 2] at h
  rw [Nat.two_mul, Nat.add_assoc]
  apply Nat.lt_add_of_pos_right
  if h₀:n % 2 = 0 then
    rw [h₀]; rw [h₀] at h
    if h₁:n / 2 = 0 then
      rw [h₁]; rw [h₁] at h
      contradiction
    else
      rw [Nat.add_zero]
      apply Nat.zero_lt_of_ne_zero
      assumption
  else
    apply Nat.add_pos_right
    apply Nat.zero_lt_of_ne_zero
    assumption

def nat_div2_rec.go
  {motive: Nat -> Sort u}
  (base: motive 0)
  (ind: ∀(n: Nat), n ≠ 0 -> motive (n / 2) -> motive n)
  : ∀(n fuel: Nat), n < fuel -> motive n :=
  fun n fuel hfuel =>
  if h:n = 0 then
    flip cast base <| by rw [h]
  else
    match fuel with
    | fuel + 1 =>
    ind n h <| nat_div2_rec.go base ind (n / 2) fuel <| by
      apply Nat.lt_of_lt_of_le
      apply nat_div2_rec_lemma
      assumption
      apply Nat.le_of_lt_succ
      assumption

private def nat_div2_rec.go_congr
  {motive: Nat -> Sort u}
  (base: motive 0)
  (ind: ∀(n: Nat), n ≠ 0 -> motive (n / 2) -> motive n)
  (n fuel₀ fuel₁: Nat) (h₀: n < fuel₀) (h₁: n < fuel₁) :
  go base ind n fuel₀ h₀ = go base ind n fuel₁ h₁ := by
  induction n using Nat.strongRecOn generalizing fuel₀ fuel₁ with
  | ind n ih =>
  cases fuel₀ with
  | zero => contradiction
  | succ fuel₀ =>
  cases fuel₁ with
  | zero => contradiction
  | succ fuel₁ =>
  unfold go
  split
  rfl
  dsimp
  congr 1
  apply ih
  apply nat_div2_rec_lemma
  assumption

def nat_div2_rec
  {motive: Nat -> Sort u}
  (base: motive 0)
  (ind: ∀(n: Nat), n ≠ 0 -> motive (n / 2) -> motive n) :
  ∀n, motive n :=
  fun n => nat_div2_rec.go base ind n (n + 1) (Nat.lt_succ_self _)

def nat_div2_rec_base
  {motive: Nat -> Sort u}
  (base: motive 0)
  (ind: ∀(n: Nat), n ≠ 0 -> motive (n / 2) -> motive n)
  : nat_div2_rec base ind 0 = base := rfl

def nat_div2_rec_ind
  {motive: Nat -> Sort u}
  (base: motive 0)
  (ind: ∀(n: Nat), n ≠ 0 -> motive (n / 2) -> motive n)
  (n: Nat) (h: n ≠ 0)
  : nat_div2_rec base ind n = ind n h (nat_div2_rec base ind (n / 2)) := by
  rw [nat_div2_rec]
  unfold nat_div2_rec.go
  rw [dif_neg h]
  show ind _ _ _ = _
  congr 1
  apply nat_div2_rec.go_congr

def mod_lt (a b: Nat) (h: 0 < b) : a % b < b := by
  induction a, b using Nat.div.inductionOn with
  | base a b g =>
    rw [nat_mod_eq, if_neg g]
    exact Nat.lt_of_not_le (fun ha => g ⟨h, ha⟩)
  | ind a b g ih =>
    rw [nat_mod_eq, if_pos g]
    apply ih
    assumption

def nat_mod2_eq_zero_or_one (n: Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  match h:n % 2 with
  | 0 => left; rfl
  | 1 => right; rfl
  | k + 2 =>
    have := mod_lt n 2 (by decide)
    rw [h] at this
    replace : k + 2 < 0 + 2 := this
    replace := Nat.lt_of_add_lt_add_right this
    contradiction
