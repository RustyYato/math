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

class EncodableZero (α: Type*) [Zero α] extends Encodable α where
  protected encode_zero : encode 0  = 0

def encode_zero (α: Type*) [Zero α] [EncodableZero α] : Encodable.encode (0: α) = 0 := EncodableZero.encode_zero

def decode_zero (α: Type*) [Zero α] [EncodableZero α] : Encodable.decode 0 = .some (0: α) := by
  rw [←encode_zero α, Encodable.spec]

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

instance : EncodableZero ℕ where
  decode := .some
  encode := id
  spec _ := rfl
  encode_zero := rfl

@[implicit_reducible]
def Encodable.ofEquiv (f: α ≃ β) : Encodable β where
  decode n := match Encodable.decode n with
    | .some a => .some (f a)
    | .none => .none
  encode b := Encodable.encode (f.symm b)
  spec b := by simp [Encodable.spec]

instance : Encodable (Fin n) := .ofEquiv (Equiv.fin_eqv_suptype n).symm

instance : Encodable Bool where
  decode
  | 0 => .some false
  | 1 => .some true
  | _ => .none
  encode
  | false => 0
  | true => 1
  spec x := by cases x <;> rfl

def Encodable.axiomOfChoice {α: Type*} {β: α -> Type*} [∀a, Encodable (β a)] {P: ∀a, β a -> Prop} [∀a, DecidablePred (P a)] (h: ∀a, ∃b: β a, P a b) : ∃f: (∀a, β a), ∀a, P a (f a) := by
  refine ⟨fun a => Encodable.choice (h a) ,?_⟩
  intro a
  apply Encodable.choice_spec
