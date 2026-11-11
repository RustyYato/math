module

namespace List

public theorem nodup_eraseDups [BEq α] [LawfulBEq α] (as: List α) : as.eraseDups.Nodup := by
  induction len_eq:as.length using Nat.strongRecOn generalizing as with
  | _ len ih =>
  cases as with
  | nil => rw [List.eraseDups_nil]; apply List.nodup_nil
  | cons a as =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    apply And.intro
    · intro h; simp at h
    · subst len
      replace ih (bs: List α) (h) := ih bs.length h bs rfl
      apply ih
      apply flip Nat.lt_of_le_of_lt
      apply Nat.lt_succ_self
      apply List.length_filter_le
