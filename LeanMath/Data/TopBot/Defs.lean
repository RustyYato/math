class Top (α: Sort u) where
  top: α

class Bot (α: Sort u) where
  bot: α

notation "⊤" => Top.top
notation "⊥" => Bot.bot
