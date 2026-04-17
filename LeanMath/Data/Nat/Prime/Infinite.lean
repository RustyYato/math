import LeanMath.Data.Nat.Prime.Defs
import LeanMath.Data.Fintype.Order
import LeanMath.Order.Monotone

namespace Nat

def fact : ℕ -> ℕ
| 0 => 1
| n + 1 => (n + 1) * fact n

def fact_ne_zero (n: ℕ) : fact n ≠ 0 := by
  induction n with
  | zero => nofun
  | succ n ih =>
    intro h
    rcases Nat.mul_eq_zero.mp h with h | h
    contradiction
    contradiction

def dvd_fact_of_le {n m: ℕ} : 0 < m -> m ≤ n -> m ∣ fact n := by
  intro h
  match m with
  | m + 1 =>
  clear h
  induction n with
  | zero => nofun
  | succ n ih =>
    intro g
    rw [Nat.le_iff_lt_or_eq, Or.comm] at g
    rcases g with g | g
    rw [g]; apply Nat.dvd_mul_right
    apply Nat.dvd_trans
    apply ih
    apply Nat.le_of_lt_succ
    assumption
    apply Nat.dvd_mul_left

def prime_larger_than (n: ℕ) : ℕ := (fact n + 1).minFact

instance prime_larger_spec (n: ℕ) : IsPrime (prime_larger_than n) := by
  apply Nat.minFact_prime
  intro h
  replace h := Nat.succ.inj h
  exact fact_ne_zero n h

def lt_prime_larger_than (n: ℕ) : n < prime_larger_than n := by
  apply Decidable.byContradiction
  intro h; rw [Nat.not_lt] at h
  have h₀: n.prime_larger_than ∣ fact n := by
    apply dvd_fact_of_le
    apply Nat.pos_of_ne_zero
    apply IsPrime.ne_zero
    assumption
  have h₁: n.prime_larger_than ∣ fact n + 1 := Nat.minFact_dvd (n.fact + 1)
  have := Nat.dvd_sub h₁ h₀
  rw [Nat.add_sub_cancel_left] at this
  exact (prime_larger_spec n).not_unit ((Nat.dvd_one.mp this) ▸ inferInstance)

end Nat

private unsafe def is_coprime_with (primes: @& Array ℕ) (n: ℕ) : Bool := Id.run do
  for p in primes do
    if p ∣ n then
      return false
  return true

private unsafe def prime_counting_imp (n: ℕ) : ℕ := Id.run do
  if n = 0 then
    return 2
  else if n = 1 then
    return 3
  else

  let mut i := 6
  let mut primes_so_far : Array ℕ := #[2, 3]
  let mut n := n - 1

  while true do
    if is_coprime_with primes_so_far (i - 1) then
      n <- n - 1
      primes_so_far <- primes_so_far.push (i - 1)
      if n = 0 then
        return i - 1
    if is_coprime_with primes_so_far (i + 1) then
      n <- n - 1
      primes_so_far <- primes_so_far.push (i + 1)
      if n = 0 then
        return i + 1
    i <- i + 6

  unreachable!

private def prime_counting' (n: ℕ) : ℕ :=
  have has_next : ∃p, IsPrime p ∧ ∀(m: Fin n), prime_counting' m ≠ p := by
    let p := max_of_range (fun i: Fin n => prime_counting' i.val)
    exists Nat.prime_larger_than p
    apply And.intro
    apply Nat.prime_larger_spec
    intro ⟨m, hm⟩
    apply ne_of_lt
    apply Nat.lt_of_le_of_lt _ (Nat.lt_prime_larger_than _)
    show prime_counting' (Fin.mk m hm).val ≤ p
    apply le_max_of_range (f := fun i: Fin n => prime_counting' i.val)
  Nat.find has_next
decreasing_by
  any_goals assumption
  any_goals apply Fin.isLt

private def prime_counting'_next (n: ℕ) : ∃p, IsPrime p ∧ ∀(m: Fin n), prime_counting' m ≠ p := by
    let p := max_of_range (fun i: Fin n => prime_counting' i.val)
    exists Nat.prime_larger_than p
    apply And.intro
    apply Nat.prime_larger_spec
    intro ⟨m, hm⟩
    apply ne_of_lt
    apply Nat.lt_of_le_of_lt _ (Nat.lt_prime_larger_than _)
    show prime_counting' (Fin.mk m hm).val ≤ p
    apply le_max_of_range (f := fun i: Fin n => prime_counting' i.val)

structure prime_counting_spec (f: ℕ -> ℕ) : Prop where
  all_primes: ∀i, IsPrime (f i)
  strict_monotone: ∀(i: ℕ) {p: ℕ} (_: IsPrime p), p < f i ↔ ∃j < i, p = f j

private unsafe def native_prime_counting : {
  f: ℕ -> ℕ // prime_counting_spec f
} := {
  val := prime_counting_imp
  property := lcProof
}

private def prime_of_lt_prime_counting (i p: ℕ) (hp: IsPrime p) : p < prime_counting' i -> ∃j < i, p = prime_counting' j := by
  intro h
  unfold prime_counting' at h
  have ⟨j, hj⟩ := Decidable.not_forall.mp fun g => Nat.find_minimal _ _ h ⟨hp, g⟩
  exists j.val
  apply And.intro
  exact j.isLt
  symm; apply Decidable.byContradiction
  assumption

private def prime_of_le_prime_counting (i p: ℕ) (hp: IsPrime p) : p ≤ prime_counting' i -> ∃j ≤ i, p = prime_counting' j := by
  intro h; rw [Nat.le_iff_lt_or_eq] at h
  rcases h with h | h
  have ⟨j, j_lt_i, eq⟩  := prime_of_lt_prime_counting i p hp h
  exists j
  apply And.intro
  apply Nat.le_of_lt
  assumption
  assumption
  exists i

private instance prime_counting_is_prime (i: ℕ): IsPrime (prime_counting' i) := by
  unfold prime_counting'
  have := Nat.find_spec (prime_counting'_next i)
  exact this.left

@[implemented_by native_prime_counting]
private opaque prime_counting : {
  f: ℕ -> ℕ // prime_counting_spec f
} := {
  val := prime_counting'
  property := {
    all_primes := prime_counting_is_prime
    strict_monotone := by
      intro i p hp
      apply Iff.intro
      · intro h
        unfold prime_counting' at h; dsimp
        have := fun g => Nat.find_minimal _ _ h ⟨hp, g⟩
        replace ⟨j, hj⟩ := Decidable.not_forall.mp this
        rw [Decidable.not_not] at hj
        subst p
        exists j.val
        apply And.intro
        exact j.isLt
        rfl
      · rintro ⟨j, hj, rfl⟩
        clear hp
        induction i using Nat.strongRecOn generalizing j with
        | _ i ih =>
        apply Nat.not_le.mp
        intro h
        have ⟨k, hk, eq⟩ := prime_of_le_prime_counting j _ (prime_counting_is_prime i) h
        rw [prime_counting'] at eq
        refine (Nat.find_spec (prime_counting'_next i)).right ⟨k, ?_⟩ eq.symm
        apply Nat.lt_of_le_of_lt
        assumption
        assumption
  }
}


def Nat.le_of_strict_monotone (f: ℕ -> ℕ) (hf: StrictMonotone f) : i ≤ f i := by
  induction i with
  | zero => apply Nat.zero_le
  | succ i ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (hf (Nat.lt_succ_self i)))

protected def Nat.prime_counting : ℕ -> ℕ := prime_counting.val
instance Nat.prime_counting_is_prime (n: ℕ) : IsPrime (Nat.prime_counting n) := prime_counting.property.all_primes _
def Nat.prime_counting_strict_mono : StrictMonotone Nat.prime_counting := by
  intro i j h
  apply ((prime_counting.property).strict_monotone j (prime_counting.property.all_primes i)).mpr
  exists i
def Nat.prime_counting_inj : Function.Injective Nat.prime_counting := Nat.prime_counting_strict_mono.inj

def Nat.le_prime_counting  (i: ℕ): i ≤ Nat.prime_counting i := by
  apply Nat.le_of_strict_monotone
  apply Nat.prime_counting_strict_mono

def Nat.prime_counting_surj : Function.Surjective (β := { p: ℕ // IsPrime p }) (fun i => {
  val := Nat.prime_counting i
  property := Nat.prime_counting_is_prime i
}) := by
  intro ⟨p, hp⟩; dsimp
  rcases Nat.lt_or_eq_of_le (Nat.le_prime_counting p) with h | h
  have ⟨j, _, hj⟩ := (prime_counting.property.strict_monotone p (p := p) hp).mp h
  exists j
  symm; congr
  exists p
  symm; congr
