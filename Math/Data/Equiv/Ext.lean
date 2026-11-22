module

public import Math.Data.Equiv.Defs
public import Math.Data.Embedding.Defs
public import Math.Data.Surjection.Defs

namespace Math

public instance [EquivLike F α β] : EmbeddingLike F α β where
  coeInjective f := (Equiv.coe f).inj
public instance [EquivLike F α β] : SurjectionLike F α β where
  coeSurjection f := (Equiv.coe f).surj
