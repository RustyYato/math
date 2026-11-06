module

import Math.Tactic.Basic

namespace Math

@[expose] public def OrderOpp (α: Type*) := α

postfix:max "ᵒᵖ" => OrderOpp

namespace OrderOpp

@[expose] public def mk : α -> OrderOpp α := id
@[expose] public def get : OrderOpp α -> α := id
@[induction_eliminator] public def rec {motive: OrderOpp α -> Sort*} (mk: ∀a, motive (mk a)) (o: αᵒᵖ) : motive o := mk o

attribute [local irreducible] OrderOpp

public instance [LE α] : LE (OrderOpp α) where
  le a b := b.get ≤ a.get

public instance [LT α] : LT (OrderOpp α) where
  lt a b := b.get < a.get

public instance [Min α] : Max (OrderOpp α) where
  max a b := .mk <| min a.get b.get

public instance [Max α] : Min (OrderOpp α) where
  min a b := .mk <| max a.get b.get
