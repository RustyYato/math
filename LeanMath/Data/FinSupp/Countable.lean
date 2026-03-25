import LeanMath.Data.FinSupp.Defs
import LeanMath.Data.Countable.Defs
import LeanMath.Data.Nat.Prod
import LeanMath.Data.Nat.Find
import LeanMath.Data.Nat.Prime.Infinite
import LeanMath.Data.Nat.Prime.Factors

variable [LEM]

local instance [Zero α] : Zero (POption α) where
  zero := .some 0

instance [DecidableEq ι] [Zero α] [Encodable ι] [EncodableZero α] : Encodable (Finsupp ι α) where
  encode f := f.fold_with (fun i a acc =>
    have i := Encodable.encode i
    have a := Encodable.encode a
    acc * Nat.prime_counting i ^ a) 0 (by
      intro i a _
      dsimp
      rw [encode_zero, npow_zero, mul_one]) (by
        dsimp; intro i j a₀ a₁ b
        rw [mul_comm_right])
  decode n :=
    have factors := Nat.factors n
    let factors : Finsupp ι ℕ := DirectSum.lift (fun p => {
      toFun v :=
        match Encodable.decode (α := ι) p.val with
        | .some i => Finsupp.single i v
        | .none => 0
      map_zero := by
        cases Encodable.decode (α := ι) p.val
        rfl
        apply Finsupp.single_zero
      map_add a b := by
        cases Encodable.decode (α := ι) p.val
        symm; apply add_zero
        symm; apply Finsupp.single_add
    }) factors.toDirectSum
    let func : ℕ →₀ POption α := {
      toFun := Encodable.decode
      map_zero := by rw [decode_zero]; rfl
    }
    let output: Finsupp ι (POption α) := Finsupp.map func factors
    sorry
    -- output.fold_with (fun i a acc =>
    --   acc.and_then fun acc =>
    --   a.and_then fun a => .some (acc.set i a)) .none (by
    --     intro i a h
    --     dsimp
    --     cases a
    --     rfl
    --     show POption.some _ = _

    --     sorry) sorry
  spec := sorry
