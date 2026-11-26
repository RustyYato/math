module

public import Math.Data.Embedding.Defs
public import Math.Data.Nat.Find

import Math.Tactic.Basic

namespace Math

public class Encodable (α: Type*) where
  encode: α -> ℕ
  decode: ℕ -> Option α
  encode_decode (a: α) : decode (encode a) = a

public def encode [Encodable α] : α ↪ ℕ where
  toFun := Encodable.encode
  injective {a b} h := by
    apply Option.some.inj
    rw [←Encodable.encode_decode a, ←Encodable.encode_decode b, h]

public def decode (α: Type*) [Encodable α] : ℕ -> Option α :=
  Encodable.decode

@[simp]
public theorem encode_decode [Encodable α] (a: α) : decode α (encode a) = .some a :=
  Encodable.encode_decode a

public structure Encoding (α: Type*) [Encodable α] : Type where
  encoding: ℕ
  encoding_spec: ∃a: α, encoding = encode a

namespace Encoding

end Encoding

public def choice [Encodable α] (h: Nonempty α) : α :=
  let i := Nat.find (f := Option.isSome ∘ decode α) <| by
    obtain ⟨a⟩ := h
    exists encode a
    dsimp; rw [encode_decode]; rfl
  (decode α i).get <| by
    apply Nat.find_spec (f := Option.isSome ∘ decode α)

public instance : Encodable ℕ where
  encode := id
  decode := .some
  encode_decode _ := rfl

public instance {P: α -> Prop} [DecidablePred P] [Encodable α] : Encodable { a: α // P a } where
  encode a := encode a.val
  decode i :=
    match decode α i with
    | .some a => if h:P a then .some ⟨a, h⟩ else .none
    | .none => .none
  encode_decode := by
    intro ⟨a, ha⟩
    dsimp; rw [encode_decode]; dsimp
    rw [dite_eq_left]

variable {P: α -> Prop} [Encodable α] [DecidablePred P]

def chooseAux (h: ∃a, P a) : { x // P x } := choice <| by
  obtain ⟨x, px⟩ := h
  exists x

public def choose (h: ∃a, P a) : α := chooseAux h
public theorem choose_spec (h: ∃a, P a) : P (choose h) := (chooseAux h).property

public def countableChoice
  {α: ι -> Type*} [∀i, Encodable (α i)]
  {P: ∀i, α i -> Prop} [∀i, DecidablePred (P i)]
  (h: ∀i, ∃v: α i, P i v) :
  { f: ∀i, α i // ∀i, P i (f i) } where
  val i := choose (h i)
  property i := choose_spec (h i)

public abbrev Countable (α: Type*) : Prop := Nonempty (α ↪ ℕ)

public instance [Encodable α] : Countable α := ⟨encode⟩

public instance : Encodable (Fin n) where
  encode := Fin.val
  decode i := if h:i < n then .some ⟨i, h⟩ else .none
  encode_decode a := by rw [dite_eq_left]

public instance [Encodable α] [Encodable β] : Encodable (α ⊕ β) where
  encode
  | .inl a => 2 * encode a
  | .inr a => 2 * encode a + 1
  decode i :=
    bif i % 2 == 0 then
      (decode _ (i / 2)).map .inl
    else
      (decode _ (i / 2)).map .inr
  encode_decode a := by
    cases a with
    | inl =>
      dsimp
      rw [Nat.mul_mod_right]; dsimp; rw [Bool.cond_true]
      rw [Nat.mul_div_cancel_left, encode_decode]; rfl
      decide
    | inr =>
      dsimp
      rw [Nat.mul_add_mod]; dsimp; rw [Bool.cond_false]
      rw [Nat.mul_add_div]; dsimp; rw [encode_decode]; rfl
      decide
