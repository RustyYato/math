module

public import Math.Logic.Funlike
import Math.Tactic.Basic

public structure Hom (α β: Sort*) where
  toFun: α -> β

namespace Hom

public instance : Funlike (Hom α β) α β where
