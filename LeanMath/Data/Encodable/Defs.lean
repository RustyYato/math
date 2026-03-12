import LeanMath.Data.Equiv.Basic
import LeanMath.Data.POption.Defs
import LeanMath.Data.Nat.Find

class Encodable (α: Sort*) where
  decode: ℕ -> POption α
  encode: α -> ℕ
  spec : ∀a, decode (encode a) = .some a

structure Encoding (α: Sort*) [Encodable α] : Type where
  ofEncoding ::
  encoding: ℕ
  spec: ∃a: α, Encodable.encode a = encoding

variable {α β: Sort*} [Encodable α]

def Encoding.val (a: Encoding α) : α :=
  (Encodable.decode a.encoding).get <| by
    intro h
    have ⟨x, hx⟩ := a.spec
    rw [←hx, Encodable.spec] at h
    contradiction

def Encoding.mk (a: α) : Encoding α where
  encoding := _
  spec := ⟨a, rfl⟩

def Encoding.canonicalize (n: ℕ) (hn: (Encodable.decode (α := α) n).isSome) : Encoding α where
  encoding := Encodable.encode <| (Encodable.decode (α := α) n).get <| by
      intro h; rw [h] at hn; contradiction
  spec := ⟨_, rfl⟩

def Encoding.mk_val (a: α) : (mk a).val = a := by
  unfold mk val
  dsimp; simp [Encodable.spec]

def Encoding.val_mk (a: Encoding α) : mk a.val = a := by
  unfold val
  have ⟨x, hx⟩ := a.spec
  simp [←hx, Encodable.spec]
  unfold mk
  congr

@[simp] def Encoding.decode_encoding (a: Encoding α) : Encodable.decode a.encoding = .some a.val := by
  unfold val
  have ⟨x, hx⟩ := a.spec
  simp [←hx, Encodable.spec]

def Equiv.encoding (α: Sort*) [Encodable α] : α ≃ Encoding α where
  toFun := Encoding.mk
  invFun := Encoding.val
  leftInv := Encoding.val_mk
  rightInv := Encoding.mk_val

-- make this opaque so that users can't rely on an exact algorithm
-- even by unfolding, or using kernel hacks
opaque Encodable.choose (h: Nonempty α) : α :=
  have spec : ∃n, (Encodable.decode n).isSome := by
    have ⟨a⟩ := h
    refine ⟨Encodable.encode a, ?_⟩
    rw [Encodable.spec]; rfl
  (Equiv.encoding α).symm {
    encoding := (Encoding.canonicalize (Nat.find spec) (Nat.find_spec spec)).encoding
    spec := Encoding.spec _
  }

variable {P: α -> Prop} [DecidablePred P]

instance : Encodable { a: α // P a } where
  decode n :=
    match Encodable.decode n with
    | .none => .none
    | .some a => if pa:P a then .some ⟨_, pa⟩ else .none
  encode a := Encodable.encode a.val
  spec := by
    intro ⟨a, pa⟩
    simp [Encodable.spec]
    rw [dif_pos pa]

private def Encodable.choiceX (h: ∃a, P a) : { a // P a } := Encodable.choose <| by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha⟩

def Encodable.choice (h: ∃a, P a) : α := choiceX h
def Encodable.choice_spec (h: ∃a, P a) : P (choice h) := (choiceX h).property

instance : Encodable ℕ where
  decode := .some
  encode := id
  spec _ := rfl

def Encodable.ofEquiv (f: α ≃ β) : Encodable β where
  decode n := match Encodable.decode n with
    | .some a => .some (f a)
    | .none => .none
  encode b := Encodable.encode (f.symm b)
  spec b := by simp [Encodable.spec]

instance : Encodable (Fin n) := .ofEquiv (Equiv.fin_eqv_suptype n).symm
