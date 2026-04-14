import LeanMath.Data.ZFSet.Defs
import LeanMath.Order.Defs

namespace ZFSet

structure IsOrdinal (o: ZFSet) where
  transitive (a: ZFSet) (ha: a ∈ o) : a ⊆ o
  locally_connected (a b: ZFSet) (ha: a ∈ o) (hb: b ∈ o) :
    a ∈ b ∨ a = b ∨ b ∈ a

def IsOrdinal.mem_trans {a b c: ZFSet} (h: IsOrdinal c) (ha: a ∈ b) (hb: b ∈ c) : a ∈ c := by
  apply h.transitive
  assumption
  assumption

def IsOrdinal.mem {a b: ZFSet} (h: IsOrdinal b) (ha: a ∈ b) : IsOrdinal a where
  transitive := by
    intro z hz
    have z_sub_b := h.transitive _ (h.transitive _ ha _ hz)
    intro x hx
    rcases h.locally_connected a x ha (z_sub_b x hx) with h | h | h
    have : Relation.TransGen (· ∈ ·) x x :=  by
      apply Relation.trans
      apply Relation.TransGen.single
      assumption
      apply Relation.trans
      apply Relation.TransGen.single
      assumption
      apply Relation.TransGen.single
      assumption
    nomatch Relation.irrefl this
    subst a
    have : Relation.TransGen (· ∈ ·) z z :=  by
      apply Relation.trans
      apply Relation.TransGen.single
      assumption
      apply Relation.TransGen.single
      assumption
    nomatch Relation.irrefl this
    assumption
  locally_connected := by
    intro x y hx hy
    apply h.locally_connected
    exact h.transitive _ ha _ hx
    exact h.transitive _ ha _ hy

def IsOrdinal.omega : IsOrdinal omega where
  transitive := by
    intro a ha
    rw [mem_omega] at ha
    obtain ⟨m, hm, rfl⟩ := ha
    intro z hz
    rw [mem_natCast] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    apply natCast_mem_omega
  locally_connected := by
    intro a b ha hb
    rw [mem_omega] at ha hb
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    rw [natCast_mem_natCast, natCast_mem_natCast, natCast_inj.eq_iff]
    apply Nat.lt_trichotomy

def IsOrdinal.natCast (n: ℕ) : IsOrdinal n := by
  apply IsOrdinal.mem
  apply IsOrdinal.omega
  apply natCast_mem_omega

def IsOrdinal.succ (o: ZFSet) (ho: IsOrdinal o) : IsOrdinal o.succ where
  transitive := by
    intro a ha b hb
    simp at *
    right; rcases ha with rfl | ha
    assumption
    apply ho.mem_trans
    assumption
    assumption
  locally_connected := by
    intro a b ha hb
    simp at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    right; left; rfl
    right; right; assumption
    left; assumption
    apply ho.locally_connected
    assumption
    assumption

def IsOrdinal.inter (a b: ZFSet) (ha: IsOrdinal a) (hb: IsOrdinal b) : IsOrdinal (a ∩ b) where
  transitive := by
    intro x hx y hy
    simp at *
    cases hx
    apply And.intro
    apply ha.mem_trans <;> assumption
    apply hb.mem_trans <;> assumption
  locally_connected := by
    intro x y hx hy
    simp at hx hy
    cases hx; cases hy
    apply ha.locally_connected <;> assumption

def IsOrdinal.sInter (U: ZFSet) (hU: ∀x ∈ U, IsOrdinal x) : IsOrdinal U.sInter where
  transitive := by
    intro x hx y hy
    rw [mem_sInter'] at *
    apply And.intro hx.left
    intro z hz
    apply (hU _ hz).transitive
    apply hx.right
    assumption
    assumption
  locally_connected := by
    intro x y hx hy
    simp [mem_sInter'] at hx hy
    obtain ⟨u, hu⟩ := hx.left
    apply (hU _ hu).locally_connected
    apply hx.right; assumption
    apply hy.right; assumption

def sInter_sub (U: ZFSet) : ∀u ∈ U, sInter U ⊆ u := by
  intro u hu x hx
  rw [mem_sInter ⟨_, hu⟩] at hx
  apply hx; assumption

@[pp_with_univ]
structure Ordinal.{u} where
  ofZFSet ::
  toZFSet : ZFSet.{u}
  spec: IsOrdinal toZFSet

instance : LE Ordinal where
  le a b := a.toZFSet ⊆ b.toZFSet
instance : LT Ordinal where
  lt a b := a.toZFSet ∈ b.toZFSet

instance : Min Ordinal where
  min a b := {
    toZFSet := a.toZFSet ∩ b.toZFSet
    spec := IsOrdinal.inter _ _ a.spec b.spec
  }

instance : IsLawfulMin Ordinal where
  min_le_left _ h := (mem_inter.mp h).left
  min_le_right _ h := (mem_inter.mp h).right

instance : NatCast Ordinal where
  natCast n := {
    toZFSet := n
    spec := IsOrdinal.natCast _
  }
instance : OfNat Ordinal n := ⟨n⟩

def Ordinal.omega : Ordinal where
  toZFSet := ZFSet.omega
  spec := IsOrdinal.omega

@[ext]
def Ordinal.ext (a b: Ordinal) (h: ∀x, x < a ↔ x < b) : a = b := by
  suffices a.toZFSet = b.toZFSet by cases a; congr
  ext x;
  apply Iff.intro
  intro ha
  apply (h ⟨x, _⟩).mp
  assumption
  apply IsOrdinal.mem a.spec
  assumption
  intro hb
  apply (h ⟨x, _⟩).mpr
  assumption
  apply IsOrdinal.mem b.spec
  assumption

variable [LEM]

-- instance : IsPartialOrder Ordinal where
--   lt_iff_le_and_not_ge := by
--     intro a b
--     apply Iff.intro
--     intro h
--     apply And.intro
--     apply b.spec.transitive
--     assumption
--     intro g
--     exact mem_irrefl _ (g a.toZFSet h)
--     intro ⟨ha, hb⟩
--     let U := b.toZFSet \ a.toZFSet
--     have ⟨x, hx⟩ := (LEM.not_forall.mp hb)
--     replace ⟨hx, gx⟩ := LEM.not_forall.mp hx
--     have Unonempty : U.Nonempty := ⟨x, mem_sdiff.mpr ⟨hx, gx⟩⟩
--     suffices a.toZFSet = sInter U by
--       show a.toZFSet ∈ b.toZFSet
--       rw [this]
--       suffices U.sInter ∈ b.toZFSet \ a.toZFSet by rw [mem_sdiff] at this; exact this.left
--       sorry
--     clear x hx gx
--     ext x; apply Iff.intro
--     intro x_in_a
--     have := ha
--     rw [mem_sInter Unonempty]
--     intro y hy
--     unfold U at hy; rw [mem_sdiff] at hy
--     apply (b.spec.mem hy.left).transitive




--     -- have : sInter U ∈ U := by

--     --   sorry
--     have := sInter_sub U
--     clear hb
--     -- have :=
--     sorry
--   refl _ _ := id
--   trans h g x hx := g _ (h _ hx)
--   antisymm ha hb := by
--     ext x; apply Iff.intro
--     apply ha; apply hb

-- def IsOrdinal.sub_total (a b: ZFSet) (ha: IsOrdinal a) (hb: IsOrdinal b) : a ⊆ b ∨ b ⊆ a := by
--   apply LEM.byContradiction
--   rw [not_or]
--   intro ⟨hab, hba⟩
--   have : a ∩ b ∈ a := by
--     sorry
--   have min_ord := IsOrdinal.inter a b ha hb

--   intro h x hx
--   replace h : ¬∀_, _ := h
--   simp only [LEM.not_forall] at h
--   obtain ⟨y, h_in_a, y_notin_b⟩ := h
--   sorry

-- def IsOrdinal.union (a b: ZFSet) (ha: IsOrdinal a) (hb: IsOrdinal b) : IsOrdinal (a ∪ b) where
--   transitive := by
--     intro x hx y hy
--     simp at *
--     rcases hx with hx | hx
--     left; apply ha.mem_trans <;> assumption
--     right; apply hb.mem_trans <;> assumption
--   locally_connected := by
--     intro x y hx hy
--     simp at hx hy
--     rcases hx with hx | hx <;> rcases hy with hy | hy
--     · apply ha.locally_connected <;> assumption
--     · sorry
--     · sorry
--     · apply hb.locally_connected <;> assumption

-- def IsOrdinal.connected (a b: ZFSet) (ha: IsOrdinal)

end ZFSet
