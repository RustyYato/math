import LeanMath.Tactic.TypeStar
import LeanMath.Tactic.AxiomBlame

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

private def findAux (h: ∃n, P n) (n: ℕ) (hn: ∀m < n, ¬P m) : Σ'n, P n ∧ ∀m < n, ¬P m :=
  if pn:P n then
    ⟨_, pn, hn⟩
  else
    findAux h (n + 1) <| by
      intro m hm
      rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at hm
      rcases hm with hm | rfl
      apply hn; assumption
      assumption
termination_by find_measure.of_val h n hn
decreasing_by exact Nat.lt_succ_self _

def Nat.find : ℕ := (findAux h 0 nofun).1
def Nat.find_spec : P (find h) := (findAux h 0 nofun).2.1
def Nat.find_minimal : ∀n < find h, ¬P n := (findAux h 0 nofun).2.2
