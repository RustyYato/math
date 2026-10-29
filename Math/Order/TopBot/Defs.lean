module

import Math.Tactic.Basic

public class Top (α: Type*) where
  top: α

public class Bot (α: Type*) where
  bot: α

notation "⊤" => Top.top
notation "⊥" => Bot.bot

public class IsLawfulTop (α: Type*) [Top α] [LE α]: Prop where
  le_top (a: α) : a ≤ ⊤

public class IsLawfulBot (α: Type*) [Bot α] [LE α]: Prop where
  bot_le (a: α) : ⊥ ≤ a

export IsLawfulTop (le_top)
export IsLawfulBot (bot_le)
