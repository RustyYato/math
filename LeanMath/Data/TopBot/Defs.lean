class Top (α: Sort u) where
  top: α

class Bot (α: Sort u) where
  bot: α

notation "⊤" => Top.top
notation "⊥" => Bot.bot

class IsLawfulTop (α: Type u) [LE α] [Top α] where
  protected le_top (a: α) : a ≤ ⊤

class IsLawfulBot (α: Type u) [LE α] [Bot α] where
  protected bot_le (a: α) : ⊥ ≤ a

def le_top [LE α] [Top α] [IsLawfulTop α] (a: α) : a ≤ ⊤ := IsLawfulTop.le_top _
def bot_le [LE α] [Bot α] [IsLawfulBot α] (a: α) : ⊥ ≤ a := IsLawfulBot.bot_le _

instance : Bot Nat where
  bot := 0

instance : IsLawfulBot Nat where
  bot_le := Nat.zero_le
