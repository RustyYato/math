module

public import Math.Algebra.Monoid.Defs
import Math.Order.Relation.Defs

namespace Math

public class HasChar (α: Type*) [AddMonoidOps α] [IsAddMonoid α] (n: outParam ℕ) where
  nsmul_eq_zero_iff_dvd (i: ℕ): (∀(a: α), i • a = 0) ↔ n ∣ i

variable [AddMonoidOps α] [IsAddMonoid α]

public theorem HasChar.char_dvd [HasChar α c] (n: ℕ) : (∀a: α, n • a = 0) -> c ∣ n :=
  (HasChar.nsmul_eq_zero_iff_dvd n).mp

public theorem nsmul_eq_zero [HasChar α c] (n: ℕ) (h: c ∣ n) : ∀a: α, n • a = 0 :=
  (HasChar.nsmul_eq_zero_iff_dvd _).mpr h

public theorem spec [HasChar α c] : ∀a: α, c • a = 0 :=
  nsmul_eq_zero _ (Nat.dvd_refl _)

public theorem HasChar.unique (h: HasChar α n) (g: HasChar α m) : n = m := by
  apply Nat.dvd_antisymm
  apply (h.nsmul_eq_zero_iff_dvd _).mp
  apply (g.nsmul_eq_zero_iff_dvd _).mpr
  apply Nat.dvd_refl
  apply (g.nsmul_eq_zero_iff_dvd _).mp
  apply (h.nsmul_eq_zero_iff_dvd _).mpr
  apply Nat.dvd_refl

public theorem HasChar.char_exists [LEM] (α: Type*) [AddMonoidOps α] [IsAddMonoid α] : ∃n, HasChar α n := by
  rcases Or.symm (em (∃n > 0, ∀a: α, n • a = 0)) with h | h
  · exists 0
    refine ⟨?_⟩
    intro i; apply Iff.intro
    intro hi
    rcases i with _ | i; apply Nat.dvd_refl
    nomatch h ⟨i + 1, Nat.zero_lt_succ _, hi⟩
    intro h; cases Nat.zero_dvd.mp h
    intro a; rw [zero_nsmul]
  · have := Math.instIsWelFoundedNatLt
    have ⟨n, ⟨npos, hn⟩, min⟩ := exists_min (· < ·) h
    exists n; refine ⟨?_⟩
    intro i; symm
    apply Iff.intro
    · rintro ⟨i, rfl⟩ a
      rw [mul_nsmul, hn]
    · induction i using Nat.strongRecOn with
      | _ i ih =>
      intro hi
      rcases Or.symm (Nat.lt_or_eq_of_le (Nat.zero_le i)) with rfl | ipos
      apply Nat.dvd_zero
      have n_le_i := Nat.not_lt.mp (min i ⟨ipos, hi⟩)
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le n_le_i
      clear n_le_i ipos
      apply Nat.dvd_add
      apply Nat.dvd_refl
      apply ih i ?_ ?_
      · rw (occs := [1]) [←zero_add i]
        apply Nat.add_lt_add_right
        assumption
      intro a
      have := hi a
      rwa [add_nsmul, hn, zero_add] at this

public theorem HasChar.of_eqv [AddMonoidOps β] [IsAddMonoid β] [HasChar α n] (eqv: α ≃+ β) : HasChar β n where
  nsmul_eq_zero_iff_dvd x := by
    apply Iff.intro
    intro h
    apply char_dvd (α := α)
    intro a
    apply eqv.inj
    rw [map_nsmul, map_zero]
    apply h
    intro h a
    apply eqv.symm.inj
    rw [map_nsmul, nsmul_eq_zero, map_zero]
    assumption

public instance : HasChar ℕ 0 where
  nsmul_eq_zero_iff_dvd n := by
    apply Iff.intro
    intro h
    cases n
    apply Nat.dvd_refl
    have := h 1
    nomatch this
    rintro ⟨_, rfl⟩
    intro
    simp [zero_nsmul]

public instance : HasChar ℤ 0 where
  nsmul_eq_zero_iff_dvd n := by
    apply Iff.intro
    intro h
    cases n
    apply Nat.dvd_refl
    have := h 1
    nomatch this
    rintro ⟨_, rfl⟩
    intro
    simp [zero_nsmul]

public class NontrivialChar (α: Type*) [AddMonoidOps α] [IsAddMonoid α] (n: outParam ℕ) extends HasChar α n where
  n_not_dvd_two : ¬n ∣ 2

public theorem char_ne_one (α: Type*) [AddMonoidOps α] [IsAddMonoid α] {n: ℕ} [h: NontrivialChar α n] : n ≠ 1 := by
  intro rfl
  exact h.n_not_dvd_two (by decide)
public theorem char_ne_two (α: Type*) [AddMonoidOps α] [IsAddMonoid α] {n: ℕ} [h: NontrivialChar α n] : n ≠ 2 := by
  intro rfl
  exact h.n_not_dvd_two (by decide)
public theorem char_eq_zero_or_gt_two (α: Type*) [AddMonoidOps α] [IsAddMonoid α] {n: ℕ} [h: NontrivialChar α n] : n = 0 ∨ 2 < n := by
  match n, h with
  | 0, _ => left; rfl
  | 1, h => nomatch char_ne_one α
  | 2, h => nomatch char_ne_two α
  | n + 3, h => right; apply Nat.add_lt_add_right _ 2; apply Nat.zero_lt_succ

public instance instNontrivialChar0 [HasChar α 0] : NontrivialChar α 0 where
  n_not_dvd_two := by decide
public instance instNontrivialCharN [HasChar α (n + 3)] : NontrivialChar α (n + 3) where
  n_not_dvd_two := by
    intro h; apply Nat.not_lt_of_le (Nat.le_of_dvd (by decide) h)
    apply Nat.add_lt_add_right _ 2
    apply Nat.zero_lt_succ
