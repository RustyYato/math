import LeanMath.Data.Fintype.Pi
import LeanMath.Data.Fintype.Sigma
import LeanMath.Data.Fintype.Pairing

noncomputable scoped instance (priority := 10) Classical.instFintypeOfFinite [f: Finite α] : Fintype α :=
  Classical.choice f
