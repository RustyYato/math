import LeanMath.Algebra.Group.Free
import LeanMath.Algebra.Group.Set
import LeanMath.Data.ZMod.Ring
import LeanMath.Data.Set.Relation

inductive Rel (n: ℕ) : FreeGroup Unit -> FreeGroup Unit -> Prop where
| intro (g: FreeGroup Unit) : Rel n (g ^ n) 1

-- the cyclic group of order n
structure CyclicGroup (n: ℕ) where
  ofQuot :: toQuot : GroupQuot (Rel n)

namespace CyclicGroup

private abbrev equiv_quot₀ : CyclicGroup n ≃ GroupQuot (Rel n) where
  toFun := CyclicGroup.toQuot
  invFun := CyclicGroup.ofQuot
  leftInv _ := rfl
  rightInv _ := rfl

instance : One (CyclicGroup n) := ⟨equiv_quot₀.symm 1⟩
instance : Mul (CyclicGroup n) where
  mul a b := equiv_quot₀.symm (equiv_quot₀ a * equiv_quot₀ b)
instance : Div (CyclicGroup n) where
  div a b := equiv_quot₀.symm (equiv_quot₀ a / equiv_quot₀ b)
instance : Inv (CyclicGroup n) where
  inv a := equiv_quot₀.symm (equiv_quot₀ a)⁻¹
instance : Pow (CyclicGroup n) ℕ where
  pow a n := equiv_quot₀.symm <| (equiv_quot₀ a) ^ n
instance : Pow (CyclicGroup n) ℤ where
  pow a n := equiv_quot₀.symm <| (equiv_quot₀ a) ^ n

def equiv_quot : CyclicGroup n ≃* GroupQuot (Rel n) where
  toFun := CyclicGroup.toQuot
  invFun := CyclicGroup.ofQuot
  leftInv _ := rfl
  rightInv _ := rfl
  map_one := rfl
  map_mul _ _ := rfl

instance : IsLawfulDiv (CyclicGroup n) :=
  IsLawfulDiv.lift equiv_quot (fun _ => rfl) (fun _ _ => rfl)
instance : IsLawfulPowN (CyclicGroup n) :=
  IsLawfulPowN.lift equiv_quot (fun _ _ => rfl)
instance : IsLawfulPowZ (CyclicGroup n) :=
  IsLawfulPowZ.lift equiv_quot (fun _ => rfl) (fun _ _ => rfl)
instance : IsGroup (CyclicGroup n) :=
  IsGroup.lift equiv_quot (fun _ => rfl)
instance : IsComm (CyclicGroup n) :=
  IsComm.lift equiv_quot

def ofFree : FreeGroup Unit →* CyclicGroup n :=
  equiv_quot.symm.toGroupHom.comp (GroupQuot.mk _)

def ι : CyclicGroup n := equiv_quot.symm (GroupQuot.mk _ (FreeGroup.ι ()))

def preind
  {motive: CyclicGroup n -> Prop}
  (ofFree: ∀x: FreeGroup Unit, motive (ofFree x))
  (x: CyclicGroup n) : motive x := by
  obtain ⟨x⟩ := x
  induction x using GroupQuot.ind with | mk x =>
  apply ofFree

def generated_by_ι
  (x: CyclicGroup n) : ∃n: ℤ, x = ι ^ n := by
  cases x using preind with | _ x =>
  induction x with
  | one =>
    exists 0
    rw [map_one, zpow_zero]
  | mul a b ha hb =>
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    exists a + b
    rw [map_mul, ha, hb, zpow_add]
  | inv a ha =>
    obtain ⟨a, ha⟩ := ha
    exists -a
    rw [map_inv, ha, zpow_neg]
  | ι =>
    exists 1; rw [zpow_one]; rfl

def pown_eq_one (x: CyclicGroup n) : x ^ n = 1 := by
  cases x using preind with | _ x =>
  induction x with
  | one => simp [map_one]; apply one_npow
  | inv x ih =>
    simp [map_inv]
    rw [←one_inv, ←ih]
    apply eq_inv_of_mul
    erw [←mul_npow, inv_mul_cancel, one_npow]
  | mul a b iha ihb =>
    erw [map_mul, mul_npow, iha, ihb, mul_one]
  | ι x =>
    show equiv_quot.symm (_) ^ n = _
    rw [←map_npow, ←map_one equiv_quot.symm]
    congr; apply GroupQuot.sound
    apply Rel.intro

def generated_by_ι' [NeZero n] (x: CyclicGroup n) : ∃k < n, x = ι ^ k := by
  obtain ⟨k, ih⟩ := generated_by_ι x
  exists (k % n).toNat
  apply And.intro
  apply (Int.toNat_lt _).mpr
  apply Int.emod_lt
  apply NeZero.ne
  apply Int.emod_nonneg
  apply NeZero.ne
  rw [ih, ←zpow_ofNat, Int.ofNat_toNat, Int.max_eq_left]
  rw (occs := [1]) [←Int.mul_ediv_add_emod k n]
  rw [zpow_add, zpow_mul, zpow_ofNat, pown_eq_one, one_zpow, one_mul]
  apply Int.emod_nonneg
  apply NeZero.ne

def lift [GroupOps α] [IsGroup α] (h: ∀x: α, x ^ n = 1) (x: α) : CyclicGroup n →* α :=
  (GroupQuot.lift (Rel n) {
    val := FreeGroup.lift (fun _ => x)
    property := by
      intro x y h
      cases h
      rw [map_npow, map_one]; apply h
  }).comp equiv_quot.toGroupHom

def lift_ι [GroupOps α] [IsGroup α] (h: ∀x: α, x ^ n = 1) : lift h x ι = x := by
  unfold lift ι
  simp [FreeGroup.lift_ι]

def zpow_eq_zpow_emod (x: CyclicGroup n) (m: ℤ) : x ^ m = x ^ (m % n) := by
  rw (occs := [1]) [←Int.ediv_mul_add_emod m n, zpow_add, zpow_mul, zpow_ofNat, pown_eq_one, one_mul]

private def pow' : CyclicGroup n →* MulOfAdd (ZMod n) := lift (by
  intro x
  cases x using MulOfAdd.induction with | mk x =>
  show MulOfAdd.mkHom x ^ n = 1
  show MulOfAdd.mkHom (n • x) = 1
  rw [ZMod.nsmul_eq_natCast_mul, ZMod.natCast_degree, zero_mul]
  rfl) (MulOfAdd.mkHom 1)

def pow'_ι : pow' (n := n) ι = MulOfAdd.mkHom 1 := by
  apply lift_ι

def pow : CyclicGroup n ≃* MulOfAdd (ZMod n) where
  toFun := pow'
  invFun x := ι ^ x.get.val
  leftInv x := by
    cases x using MulOfAdd.induction with | mk x =>
    dsimp; rw [map_zpow, pow'_ι]
    show MulOfAdd.mkHom (x.val • 1) = MulOfAdd.mkHom x
    congr; apply mul_one
  rightInv x := by
    obtain ⟨x, rfl⟩ := generated_by_ι x
    dsimp; rw [map_zpow, pow'_ι]
    show ι ^ (x • (1: ZMod n)).val = ι ^ x
    rw [ZMod.zsmul_val, ZMod.one_val]
    rw [Int.mul_emod, Int.emod_emod, ←Int.mul_emod]
    rw [mul_one]; rw [←zpow_eq_zpow_emod]
  map_one := map_one _
  map_mul := map_mul _

def pow_ι : pow (n := n) ι = MulOfAdd.mkHom 1 := by
  apply pow'_ι

def pow_symm (x: CyclicGroup n) : ι ^ (pow x).get.val = x := by
  show (pow.symm (pow x)) = x
  rw [GroupEquiv.coe_symm]

def cast_pown (m: ℕ) : CyclicGroup n →* CyclicGroup (n * m) :=
  (GroupQuot.lift (Rel n) {
    val := CyclicGroup.ofFree.comp (zpowHom m)
    property x y h := by
      cases h
      dsimp
      rw [one_zpow, map_one, zpow_ofNat, ←npow_mul, map_npow, pown_eq_one]
  }).comp equiv_quot.toGroupHom

def cast_pown_ι : cast_pown (m := m) (n := n) ι = ι ^ m := by
  apply GroupQuot.lift_mk

def cast (h: n = m) : CyclicGroup n ≃* CyclicGroup m where
  toFun := lift (α := CyclicGroup m) (n := n) (fun x => h ▸ pown_eq_one x) ι
  invFun := lift (α := CyclicGroup n) (n := m) (fun x => h ▸ pown_eq_one x) ι
  leftInv := by
    intro x
    obtain ⟨k, rfl⟩ := generated_by_ι x
    rw [map_zpow, map_zpow, lift_ι, lift_ι]
  rightInv := by
    intro x
    obtain ⟨k, rfl⟩ := generated_by_ι x
    rw [map_zpow, map_zpow, lift_ι, lift_ι]
  map_one := map_one _
  map_mul := map_mul _

def cast_ι (h: n = m) : cast h ι = ι := lift_ι (fun x => h ▸ pown_eq_one x)

def of_powz_eq_one (m: ℤ) : ι (n := n) ^ m = 1 -> (n: ℤ) ∣ m := by
  intro h; rw [zpow_eq_zpow_emod] at h
  cases n with
  | zero =>
    simp at h
    have := congrArg pow h
    rw [map_zpow, map_one] at this
    replace : (m • (pow ι).get).val = ZMod.val 0 := (congrArg (ZMod.val ∘ MulOfAdd.get) this)
    simp at this
    rcases of_mul_eq_zero this with h | h
    subst m; apply Int.dvd_zero
    rw [pow_ι] at h
    contradiction
  | succ n =>
    have := congrArg pow h
    rw [map_zpow, map_one] at this
    replace : ((m % _) • (pow ι).get).val = ZMod.val 0 := (congrArg (ZMod.val ∘ MulOfAdd.get) this)
    rw [pow_ι] at this
    simp only [ZMod.zsmul_val, ZMod.zero_val] at this
    replace : ((m % _) • (1: ZMod _)).val = 0 := this
    rw [ZMod.zsmul_val, ZMod.one_val, ←Int.mul_emod, mul_one] at this
    apply Int.dvd_of_emod_eq_zero
    assumption

def ofCyclicEmbed (f: CyclicGroup m ↪* CyclicGroup n) : m ∣ n := by
  have h : f (ι ^ n) = f 1 := by rw [map_npow, pown_eq_one, map_one]
  replace h := f.inj h
  rw [←zpow_ofNat] at h
  apply Int.natCast_dvd_natCast'.mp (of_powz_eq_one _ h)

def ofSubgroup [LEM] (s: Subgroup (CyclicGroup n)) : ∃m, Nonempty (s ≃* CyclicGroup m) := by
  rcases em (Set.coe s = {1}) with h | h
  · exists 1
    exact ⟨{
      toFun _ := 1
      invFun _ := 1
      leftInv x := by dsimp; rw [←npow_one x, pown_eq_one]
      rightInv x := by
        dsimp
        have := x.property
        conv at this => { lhs; rw [h] }
        ext; exact this
      map_one := rfl
      map_mul _ _ := (mul_one _).symm
    }⟩
  · let U := ((s.toSet \ {1}).image (Int.natAbs ∘ ZMod.val ∘ MulOfAdd.get ∘ pow))
    have Unonempty : U.Nonempty := by
      have : Nontrivial s := by
        apply LEM.byContradiction
        intro g
        apply h
        ext x; apply Iff.intro
        intro hx
        apply LEM.byContradiction
        intro hne
        refine g ⟨⟨x, hx⟩, ⟨_, mem_one s⟩, ?_⟩
        intro h; cases h; contradiction
        intro rfl
        apply mem_one s
      let one : Set.coe s := 1
      have ⟨b, ne_one⟩ := Nontrivial.exists_ne (1: Set.coe s)
      apply Set.image_nonempty_iff.mpr
      exists b
      apply And.intro
      exact b.property
      dsimp; intro g; apply ne_one
      ext; exact g
    have ⟨minpow, ⟨mem_minpow, hmin_pow⟩, u⟩ := Set.exists_unique_min (· < ·) Unonempty
    clear u
    have mem : ι ^ minpow ∈ s := by
      obtain ⟨i, hi, rfl⟩ := Set.mem_image.mp mem_minpow
      dsimp
      rw [←zpow_ofNat, ←Int.mul_sign_self]
      rw [zpow_mul, pow_symm]
      rcases (pow i).get.val.sign_trichotomy with h | h | h
      rw [h, zpow_one]; exact hi.left
      rw [h, zpow_zero]; exact mem_one _
      rw [h, zpow_neg_one]; apply mem_inv; exact hi.left
    have minpow_dvd : minpow ∣ n := by
      sorry
    have : ∀x ∈ s, ∃m: ℤ, x = (ι ^ minpow) ^ m := by
      sorry
    replace : ∀x: Set.coe s, existsUnique fun m: CyclicGroup (n / minpow) => x.val = (cast (by
      rw [Nat.div_mul_cancel minpow_dvd]) (cast_pown (n := n / minpow) minpow ι)) := by
      sorry
    have ⟨f, hf⟩ := Classical.axiomOfUniqueChoice this
    clear this
    exists n / minpow
    exact ⟨GroupEquiv.symm {
      toFun := lift (by
        intro x; ext
        have := (hf x).left
        show x.val ^ _ = _
        rw [this]
        rw [cast_pown_ι, map_npow, cast_ι, ←npow_mul,
          Nat.mul_div_cancel' minpow_dvd, pown_eq_one]
        rfl) ⟨_,  mem⟩
      invFun := f
      leftInv := by
        sorry
      rightInv := by
        sorry
      map_one := map_one _
      map_mul := map_mul _
    }⟩

def ofEmbed [LEM] [GroupOps α] [IsGroup α] (f: α ↪* CyclicGroup n) : ∃m, Nonempty (α ≃* CyclicGroup m) := by
  have ⟨m, ⟨hm⟩⟩ := ofSubgroup (Subgroup.range f.toGroupHom)
  exists m
  exact ⟨(Subgroup.equivRange f).trans hm⟩

end CyclicGroup
