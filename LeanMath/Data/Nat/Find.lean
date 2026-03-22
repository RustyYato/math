import LeanMath.Tactic.TypeStar
import LeanMath.Tactic.AxiomBlame
import LeanMath.Data.Nat.Basic

variable {P: ℕ -> Prop} [DecidablePred P] (h: ∃n, P n)

private structure find_measure (h: ∃n, P n) where
  val: ℕ
  spec: ∀x < val, ¬P x

private def find_measure.le_limit {limit: ℕ} (plimit: P limit) (m: find_measure h) : m.val ≤ limit :=
  Nat.le_of_not_lt fun h => m.spec _ h plimit

private def find_measure.of_val (n: ℕ) (hn: ∀m < n, ¬P m) : find_measure h where
  val := n
  spec := hn

instance instWf : WellFoundedRelation (find_measure h) where
  rel x y := y.val < x.val
  wf := by
    -- use id to hide the relation between h and limit
    -- so that h doesn't get eliminated
    have ⟨limit, plimit⟩ := id h
    apply WellFounded.intro
    intro a
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (a.le_limit h plimit)
    induction k using Nat.strongRecOn generalizing a with | _ k ih =>
    apply Acc.intro
    intro b hb
    obtain ⟨k', h⟩ := Nat.exists_eq_add_of_le (b.le_limit h plimit)
    have : k' < k := by
      apply Nat.add_lt_add_iff_left.mp
      rw [h]
      apply Nat.add_lt_add_iff_right.mpr
      assumption
    apply ih
    assumption
    rwa [←h]

private def findAux
  (start step: ℕ) (hstep: 0 < step) (h: ∃k, P (k * step + start))
  (n: ℕ) (hn: ∃i, n = i * step + start)
  (gn: ∀k, k * step + start < n -> ¬P (k * step + start))
  : Σ'n, P n ∧ ∀k, k * step + start < n -> ¬P (k * step + start) :=
  if pn:P n then
    ⟨_, pn, gn⟩
  else
    findAux start step hstep h (n + step) (by
      obtain ⟨i, rfl⟩ := hn
      exists i + 1
      rw [Nat.succ_mul, Nat.add_right_comm]) <| by
      intro k hk gk
      obtain ⟨i, rfl⟩ := hn
      rw [Nat.add_right_comm, ←Nat.succ_mul,
        Nat.add_lt_add_iff_right] at hk
      replace hk := (Nat.mul_lt_mul_right' hstep).mp hk
      rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq, Or.comm] at hk
      rcases hk with rfl | hk
      contradiction
      have := gn k ?_
      contradiction
      apply Nat.add_lt_add_right
      apply Nat.mul_lt_mul_of_pos_right
      assumption
      assumption
termination_by find_measure.of_val h ((n - start) / step) (by
  intro m hm
  obtain ⟨i, rfl⟩ := hn
  simp [hstep] at hm
  apply gn m
  apply Nat.add_lt_add_right
  apply Nat.mul_lt_mul_of_pos_right
  assumption
  assumption)
decreasing_by
  show (n - start) / step < (n + step - start) / step
  rw [Nat.add_comm _ step, Nat.add_sub_assoc, Nat.add_div_left]
  apply Nat.lt_succ_self
  assumption
  obtain ⟨i, rfl⟩ := hn
  apply Nat.le_add_left

protected def Nat.findAux := findAux (P := P) 0 1 (Nat.zero_lt_succ _) (
    have ⟨n, hn⟩ := h
    ⟨n, Nat.mul_one _ ▸ hn⟩) 0 ⟨0, rfl⟩ nofun

def Nat.find : ℕ := (Nat.findAux h).1
def Nat.find_spec : P (find h) := (Nat.findAux h).2.1
def Nat.find_minimal : ∀n < find h, ¬P n := by
  intro n hn
  have := (Nat.findAux h).2.2 n
  rw [Nat.mul_one] at this
  exact this hn
