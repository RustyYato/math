module

import Math.Algebra.Module.Set.Defs
import Math.Algebra.Ring.Set.Defs

namespace Math

instance [SetLike S α] [AddGroupOps α] [IsAddGroup α] [IsMemZero S α] [IsMemNeg S α] [IsMemAdd S α] : IsMemSMul S ℤ α where
  mem_smul _ r a := by apply mem_zsmul
