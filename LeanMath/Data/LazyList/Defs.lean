import LeanMath.Tactic.TypeStar
import LeanMath.Tactic.AxiomBlame
import LeanMath.Logic.LEM

structure LazyList (α: Type*) where
  size: ℕ
  getElem: Fin size -> α

def Array.dedup [DecidableEq α] (as: Array α) : Array α :=
  as.foldl (fun out a => if out.any (· == a) then out else out.push a) #[]

def Array.dedup_nodup [DecidableEq α] (as: Array α) : as.dedup.toList.Nodup := by
  cases as with | mk as =>
  unfold dedup; simp
  generalize hout:#[] = out
  have : out.toList.Nodup := by rw [←hout]; apply List.nodup_nil
  clear hout
  induction as generalizing out with
  | nil => assumption
  | cons a as ih =>
    simp
    apply ih
    split
    · assumption
    · simp
      apply List.nodup_append.mpr
      simp [this]
      intro x hx
      have := Array.mem_iff_getElem.mp hx
      intro rfl
      contradiction

def Array.dedup_mem [DecidableEq α] (as: Array α) : ∀{x}, x ∈ as.dedup ↔ x ∈ as := by
  cases as with | mk as =>
  unfold dedup; simp
  intro x
  rw [List.foldl_eq_foldr_reverse]
  rw [←List.mem_reverse]
  generalize as.reverse = bs
  clear as
  induction bs generalizing x with
  | nil => simp
  | cons a as ih =>
    simp
    split <;> (rename_i h)
    · rw [←Array.mem_iff_getElem] at h
      apply Iff.intro
      · intro g
        exact .inr (ih.mp g)
      · intro g
        rcases g with rfl | g
        assumption
        apply ih.mpr
        assumption
    · rw [←Array.mem_iff_getElem] at h
      simp
      apply Iff.intro
      · intro g
        rcases g with g | rfl
        right; apply ih.mp
        assumption
        left; rfl
      · intro g
        rcases g with rfl | g
        right; rfl
        left; apply ih.mpr
        assumption

def List.nodup_getElem (as: List a) : as.Nodup -> Function.Injective (fun i: Fin as.length => as[i]) := by
  intro h
  induction h with
  | nil => nofun
  | @cons a as nomem h ih =>
    intro i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simp
      | succ j =>
        simp [j.succ_ne_zero.symm]
        intro hs
        have := nomem a (List.mem_of_getElem hs.symm)
        contradiction
    | succ i =>
      cases j using Fin.cases with
      | succ j => simp; apply ih
      | zero =>
        simp [i.succ_ne_zero]
        intro hs
        have := nomem a (List.mem_of_getElem hs)
        contradiction

namespace LazyList

def empty : LazyList α where
  size := 0
  getElem := Fin.elim0

@[simp]
def empty_size : (LazyList.empty (α := α)).size = 0 := rfl

def size_eq_zero {as: LazyList α} : as.size = 0 ↔ as = .empty := by
  obtain ⟨size, as⟩ := as
  simp [empty]
  intro rfl
  simp; ext x
  exact x.elim0

def replicate (n: Nat) (a: α) : LazyList α where
  size := n
  getElem _ := a

def singleton : α -> LazyList α := replicate 1

@[simp] def size_replicate (n: ℕ) (a: α) : (replicate n a).size = n := rfl

@[simp] def size_singleton (a: α) : (singleton a).size = 1 := rfl

@[coe]
def ofArray (array: Array α) : LazyList α where
  size := array.size
  getElem i := array[i]

@[coe]
def ofList (list: List α) : LazyList α :=
  .ofArray (.mk list)

instance : GetElem (LazyList α) ℕ α fun l x => x < l.size where
  getElem xs i h := xs.getElem ⟨i, h⟩

@[simp] def mk_getElem (size: ℕ) (getElem: Fin size -> α) {i} :
  (LazyList.mk size getElem)[i] = getElem i := rfl
@[simp] def mk_getElem' (size: ℕ) (getElem: Fin size -> α) {i} {h} :
  (LazyList.mk size getElem)[i] = getElem ⟨i, h⟩ := rfl

@[ext (iff := false)]
def ext (as bs: LazyList α) :
  ∀(h: as.size = bs.size),
  (∀i: Fin as.size, as[i] = bs[i.cast h]) -> as = bs := by
  intro h g
  obtain ⟨as_size, as⟩ := as
  obtain ⟨bs_size, bs⟩ := bs
  cases h
  simp; ext i
  apply g

def cons (a: α) (as: LazyList α) : LazyList α where
  size := as.size + 1
  getElem
  | ⟨0, _⟩ => a
  | ⟨n + 1, h⟩ => as[n]'(Nat.lt_of_succ_lt_succ h)

@[simp]
def size_cons : (cons a as).size = as.size + 1 := rfl

@[simp]
def getElem_cons_zero : (cons a as)[0] = a := rfl

@[simp]
def getElem_cons_succ (n: ℕ) (h: n < as.size): (cons a as)[n + 1]'(by simp [h]) = as[n] := rfl

def append (as bs: LazyList α) : LazyList α where
  size := as.size + bs.size
  getElem x := if h:x < as.size then as[x]'(h) else bs[x - as.size]'(by
    apply Nat.sub_lt_left_of_lt_add
    apply Nat.le_of_not_lt
    assumption
    exact x.isLt)

instance : Append (LazyList α) where
  append := append

@[simp]
def size_append (as bs: LazyList α) : (as ++ bs).size = as.size + bs.size := rfl

def getElem_append_of_lt {as bs: LazyList α} (n: ℕ) (h: n < as.size): (as ++ bs)[n]'(by simp; omega) = as[n] := by
  show (append _ _)[_]'_ = _
  unfold append
  simp; rwa [dif_pos]

def getElem_append_of_ge {as bs: LazyList α} (n: ℕ) (h₀: n >= as.size) (h₁: n < as.size + bs.size): (as ++ bs)[n] = bs[n - as.size] := by
  show (append _ _)[_]'_ = _
  unfold append
  simp; rw [dif_neg]
  omega

@[simp]
def getElem_append_of_add {as bs: LazyList α} (n: ℕ) (h₁: n < bs.size): (as ++ bs)[as.size + n]'(by simp; omega) = bs[n] := by
  rw [getElem_append_of_ge]
  simp
  omega

@[simp]
def empty_append (as: LazyList α) : .empty ++ as = as := by
  ext i
  simp
  simp
  rfl

@[simp]
def append_empty (as: LazyList α) : as ++ .empty = as := by
  ext i
  simp
  simp
  show (append _ _)[_]'_ = _
  unfold append
  simp
  rfl

instance : Membership α (LazyList α) where
  mem as a := ∃i: Fin as.size, as[i] = a

@[simp] def not_mem_empty : ¬x ∈ empty := nofun

@[simp] def mem_cons : x ∈ cons a as ↔ x = a ∨ x ∈ as := by
  apply Iff.intro
  · intro ⟨i, hi⟩
    cases i using Fin.cases
    left; symm; simpa using hi
    right
    rename_i i
    exists i
  · intro h
    rcases h with rfl | h
    exists ⟨0, by simp⟩
    obtain ⟨i, h⟩ := h
    exists i.succ

@[simp] def mem_append {as bs: LazyList α} : x ∈ as ++ bs ↔ x ∈ as ∨ x ∈ bs := by
  apply Iff.intro
  · intro ⟨i, hi⟩
    replace hi : (append as bs)[i]'_ = x := hi
    simp [append] at hi
    split at hi
    left; exists ⟨i.val, ?_⟩
    assumption
    right
    exists ⟨i.val - as.size, ?_⟩
    omega
    assumption
  · intro h
    rcases h with ⟨i, h⟩ | ⟨i, h⟩
    exists ⟨i, ?_⟩
    simp; omega
    simp; rwa [getElem_append_of_lt]
    exists ⟨i + as.size, ?_⟩
    simp; omega
    simp; rw [getElem_append_of_ge]
    simpa
    omega

@[simp] def cons_append (a: α) (as bs: LazyList α) : (cons a as) ++ bs = cons a (as ++ bs) := by
  symm
  ext i; simp; omega
  simp
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp
    by_cases h:i.val < as.size
    rw [getElem_append_of_lt ,getElem_append_of_lt]
    rfl
    simp; omega
    rw [getElem_append_of_ge ,getElem_append_of_ge]
    simp
    simp; omega
    omega

def cons_eq_singleton_append (a: α) (as: LazyList α) : cons a as = singleton a ++ as := by
  ext i; simp; rw [Nat.add_comm]
  dsimp
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    by_cases h:i.val < as.size
    rw [getElem_append_of_ge]
    rfl
    apply Nat.le_add_left
    rfl

def Nodup (as: LazyList α) := Function.Injective as.getElem

def Nodup.head {a: α} {as: LazyList α} : (cons a as).Nodup -> a ∉ as := by
  rintro h ⟨j, rfl⟩
  have := (@h (0: Fin (as.size + 1)) j.succ rfl)
  nomatch this

def Nodup.tail {a: α} {as: LazyList α} : (cons a as).Nodup -> as.Nodup := by
  intro h i j eq
  exact Fin.succ_inj.mp (@h i.succ j.succ eq)

def Nodup.left {as bs: LazyList α} : (as ++ bs).Nodup -> as.Nodup := by
  intro h i j eq
  have := (@h (i.castLE (by simp)) (j.castLE (by simp)) ?_)
  apply Fin.val_inj.mp
  simpa [←Fin.val_inj] using this
  show (as ++ bs)[Fin.val _]'_ = (as ++ bs)[Fin.val _]'_
  rwa [getElem_append_of_lt, getElem_append_of_lt]

def Nodup.right {as bs: LazyList α} : (as ++ bs).Nodup -> bs.Nodup := by
  intro h i j eq
  have := (@h (i.natAdd as.size) (j.natAdd as.size) ?_)
  apply Fin.val_inj.mp
  simpa [←Fin.val_inj] using this
  show (as ++ bs)[as.size + i.val]'_ = (as ++ bs)[as.size + j.val]'_
  rw [getElem_append_of_ge, getElem_append_of_ge]
  simpa
  omega
  omega

def Nodup.append_comm {as bs: LazyList α} : (as ++ bs).Nodup -> (bs ++ as).Nodup := by
  intro h i j eq
  replace eq : (bs ++ as)[i.val]'_ = (bs ++ as)[j.val]'_ := eq
  replace h : ∀i j: Fin _, (as ++ bs)[i.val]'_ = (as ++ bs)[j.val]'_ -> i = j := h
  by_cases hi:i.val < bs.size <;> by_cases hj:j.val < bs.size
  · have := @h ⟨as.size + i.val, by simp; omega⟩ ⟨as.size + j.val, by simp; omega⟩ (by
      simp
      show (as ++ bs)[as.size + i.val]'_ = (as ++ bs)[as.size + j.val]'_
      rw [getElem_append_of_add, getElem_append_of_add]
      rw (occs := [1, 2]) [getElem_append_of_lt] at eq
      rw [eq, getElem_append_of_lt]
      any_goals omega)
    simpa [Fin.val_inj] using this
  · rw [getElem_append_of_lt _ hi, getElem_append_of_ge _ (by omega)] at eq
    have : j.val - bs.size < as.size := by
      have : j.val < bs.size + as.size := j.isLt
      omega
    have := @h ⟨as.size + i.val, by simp; omega⟩ ⟨j.val - bs.size, by simp; omega⟩
    simp at this
    rw [getElem_append_of_add i.val, getElem_append_of_lt] at this
    have := this eq
    repeat omega
  · rw [getElem_append_of_lt _ hj, getElem_append_of_ge _ (by omega)] at eq
    have : i.val - bs.size < as.size := by
      have : i.val < bs.size + as.size := i.isLt
      omega
    have := @h ⟨i.val - bs.size,  by simp; omega⟩ ⟨as.size + j.val, by simp; omega⟩
    simp at this
    rw [getElem_append_of_add j.val, getElem_append_of_lt] at this
    have := this eq
    repeat omega
  · have : i.val - bs.size < as.size := by
      have : i.val < bs.size + as.size := i.isLt
      omega
    have : j.val - bs.size < as.size := by
      have : j.val < bs.size + as.size := j.isLt
      omega
    have := @h ⟨i.val - bs.size, by simp; omega⟩ ⟨j.val - bs.size, by simp; omega⟩ (by
      simp
      rw [getElem_append_of_lt, getElem_append_of_lt]
      rw (occs := [1, 2]) [getElem_append_of_ge] at eq
      rw [eq, getElem_append_of_ge]
      any_goals omega)
    simp at this
    omega

def of_nodup_cons {a: α} {as: LazyList α} : (cons a as).Nodup -> as.Nodup := by
  intro h i j eq
  exact Fin.succ_inj.mp (@h i.succ j.succ eq)

def toArray (x: LazyList α) : Array α :=
  Array.ofFn x.getElem

def toList (x: LazyList α) : List α :=
  List.ofFn x.getElem

def basic_dedup [DecidableEq α] (x: LazyList α) : LazyList α :=
  LazyList.ofArray (x.toArray.dedup)

def basic_dedup_nodup [DecidableEq α] (as: LazyList α) : as.basic_dedup.Nodup := by
  intro i j h
  refine List.nodup_getElem _ ?_ h
  apply Array.dedup_nodup

@[simp] def mem_ofArray (as: Array α) : x ∈ LazyList.ofArray as ↔ x ∈ as := by
  rw [Array.mem_iff_getElem]
  simp [ofArray]
  show (∃i: Fin as.size, as[i] = x) ↔ _
  apply Iff.intro
  intro ⟨⟨i, h⟩, _⟩
  exists i; exists h
  intro ⟨i, h, _⟩
  exists ⟨i, h⟩

@[simp] def mem_toArray (as: LazyList α) : x ∈ as.toArray ↔ x ∈ as := by
  unfold toArray
  rw [Array.mem_ofFn] -- FIXME[classical] Array uses classical recklessly, so it's not practical to avoid it
  rfl

def basic_dedup_mem [DecidableEq α] (as: LazyList α) : ∀{x}, x ∈ as.basic_dedup ↔ x ∈ as := by
  intro x; simp [basic_dedup, Array.dedup_mem]

def fold (f: α -> β -> β) (acc: β) : LazyList α -> β
| .mk size getElem => Fin.foldr size (f ∘ getElem) acc

@[simp] def fold_empty (f: α -> β -> β) (acc: β) : fold f acc .empty = acc := rfl
@[simp] def fold_cons (f: α -> β -> β) (acc: β) (a: α) (as: LazyList α) : fold f acc (.cons a as) = f a (as.fold f acc) := by
  unfold fold
  dsimp; rw [Fin.foldr_succ]
  rfl

@[induction_eliminator]
def induction
  {motive: LazyList α -> Prop}
  (nil: motive .empty)
  (cons: ∀a as, motive as -> motive (.cons a as))
  (as: LazyList α) : motive as := by
  obtain ⟨size, getElem⟩ := as
  induction size with
  | zero =>
    rw [show (LazyList.mk 0 getElem) = .empty from size_eq_zero.mp rfl]
    apply nil
  | succ size ih =>
    rw [show (LazyList.mk (size + 1) getElem) = (LazyList.cons (getElem 0) (LazyList.mk size (getElem ∘ Fin.succ))) from ?_]
    apply cons
    apply ih
    ext i; rfl
    cases i using Fin.cases with
    | zero => rfl
    | succ i => rfl

@[cases_eliminator]
def cases
  {motive: LazyList α -> Prop}
  (nil: motive .empty)
  (cons: ∀a as, motive (.cons a as))
  (as: LazyList α) : motive as := by
  induction as with
  | nil => apply nil
  | cons a as ih => apply cons

def mem_iff_append (x: α) (as: LazyList α) : x ∈ as ↔ ∃as₀ as₁: LazyList α, as = as₀ ++ (cons x as₁) := by
  apply flip Iff.intro
  rintro ⟨as, bs, rfl⟩
  simp [mem_append, mem_cons]
  induction as with
  | nil => simp
  | cons a as ih =>
    simp; intro h
    rcases h with rfl | h
    refine ⟨.empty, as, ?_⟩
    simp
    have ⟨as₀, as₁, h⟩ := ih h
    subst as
    refine ⟨cons a as₀, as₁, ?_⟩
    simp

def append_assoc (as bs cs: LazyList α) : as ++ (bs ++ cs) = as ++ bs ++ cs := by
  induction as generalizing bs cs with
  | nil => simp
  | cons a as ih => simp [ih]

@[simp] def fold_singleton (f: α -> β -> β) (acc: β) (a: α) : fold f acc (singleton a) = f a acc := rfl

def fold_append (f: α -> β -> β) (acc: β) (as bs: LazyList α) :
  fold f acc (as ++ bs) =
  (fold f (fold f acc bs) as) := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih]

def fold_comm (f: α -> β -> β) (acc: β)
  (hcomm: ∀a₀ a₁ b, f a₀ (f a₁ b) = f a₁ (f a₀ b))
  (as: LazyList α) (a: α) : fold f (f a acc) as = fold f acc (cons a as) := by
  induction as generalizing a with
  | nil => simp
  | cons a as ih =>
    simp
    simp [ih]
    rw [hcomm]

def fold_comm_append (f: α -> β -> β) (acc: β)
  (hcomm: ∀a₀ a₁ b, f a₀ (f a₁ b) = f a₁ (f a₀ b))
  (as bs: LazyList α) : fold f acc (as ++ bs) = fold f acc (bs ++ as) := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih =>
    simp
    rw [cons_eq_singleton_append, append_assoc, ←ih,
      append_assoc, fold_append (as := _ ++ _)]
    simp
    rw [fold_comm, fold_cons]
    assumption

end LazyList
