module

import Math.Tactic.Basic
public import Math.Order.TopBot.Defs

namespace Math

@[expose] public def OrderOpp (α: Type*) := α

postfix:max "ᵒᵖ" => OrderOpp

namespace OrderOpp

@[expose] public def mk : α -> αᵒᵖ := id
@[expose] public def get : αᵒᵖ -> α := id
@[induction_eliminator] public def rec {motive: αᵒᵖ -> Sort*} (mk: ∀a, motive (mk a)) (o: αᵒᵖ) : motive o := mk o

section

attribute [local irreducible] OrderOpp

public instance [LE α] : LE αᵒᵖ where
  le a b := b.get ≤ a.get

public instance [LT α] : LT αᵒᵖ where
  lt a b := b.get < a.get

public instance [Min α] : Max αᵒᵖ where
  max a b := .mk <| min a.get b.get

public instance [Max α] : Min αᵒᵖ where
  min a b := .mk <| max a.get b.get

public instance [Top α] : Bot αᵒᵖ where
  bot := .mk ⊤
public instance [Bot α] : Top αᵒᵖ where
  top := .mk ⊥

end

public instance [Top α] [LE α] [IsLawfulTop α] : IsLawfulBot αᵒᵖ where
  bot_le := le_top (α := α)
public instance [Bot α] [LE α] [IsLawfulBot α] : IsLawfulTop αᵒᵖ where
  le_top := bot_le (α := α)
