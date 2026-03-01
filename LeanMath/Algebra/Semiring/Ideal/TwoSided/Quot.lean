import LeanMath.Algebra.Semiring.Ideal.TwoSided.Defs

variable [SemiringOps α] [IsSemiring α]

section

variable [RelLike C α] [IsMulCon C] [IsAddCon C]

def Ideal.ofCon (c: C) : Ideal α where
  toSet := { Mem := (c 0 ·) }
  mem_zero := (IsCon.eqv c).refl 0
  mem_add := by
    intro a b ha hb
    show c 0 (a + b)
    rw [←add_zero 0]
    apply resp_add
    assumption
    assumption
  mem_left_mul := by
    intro a k ha
    show c 0 (k * a)
    rw [←mul_zero k]
    apply resp_mul
    apply (IsCon.eqv c).refl
    assumption
  mem_right_mul := by
    intro a k ha
    show c 0 (a * k)
    rw [←zero_mul k]
    apply resp_mul
    assumption
    apply (IsCon.eqv c).refl

end

private def rel (i: Ideal α) (a b: α) := ∃x ∈ i, ∃ y ∈ i, a + x = b + y

private def eqv (i: Ideal α) : Equivalence (rel i) where
  refl a := by
    refine ⟨0, ?_, 0, ?_, ?_⟩
    apply mem_zero
    apply mem_zero
    rw [add_zero]
  symm {a b} h := by
    obtain ⟨x, hx, y, hy, h⟩ := h
    exact ⟨y, hy, x, hx, h.symm⟩
  trans {x y z} h g := by
    obtain ⟨x₀, hx₀, y₀, hy₀, h⟩ := h
    obtain ⟨x₁, gx₁, y₁, gy₁, g⟩ := g
    refine ⟨x₀ + x₁, ?_, y₀ + y₁, ?_, ?_⟩
    apply mem_add <;> assumption
    apply mem_add <;> assumption
    rw [←add_assoc, h, add_assoc, add_comm y₀, ←add_assoc,
      g, add_assoc, add_comm y₁]

def Ideal.toCon' (i: Ideal α) : RingCon α where
  toFun := rel i
  eqv := eqv i
  resp_add {a b c d} h g := by
    obtain ⟨x₀, hx₀, y₀, hy₀, h⟩ := h
    obtain ⟨x₁, gx₁, y₁, gy₁, g⟩ := g
    refine ⟨x₀ + x₁, ?_, y₀ + y₁, ?_, ?_⟩
    apply mem_add <;> assumption
    apply mem_add <;> assumption
    rw [show a + b + (x₀ + x₁) = (a + x₀) + (b + x₁) by ac_rfl]
    rw [h ,g]
    ac_rfl
  resp_mul {a b c d} h g := by
    obtain ⟨x₀, hx₀, y₀, hy₀, h⟩ := h
    obtain ⟨x₁, gx₁, y₁, gy₁, g⟩ := g
    apply (eqv i).trans
    show rel i (a * b) (a * d)
    · refine ⟨a * x₁, ?_, a * y₁, ?_, ?_⟩
      apply mem_left_mul
      assumption
      apply mem_left_mul
      assumption
      rw [←mul_add, ←mul_add, g]
    · refine ⟨x₀ * d, ?_, y₀ * d, ?_, ?_⟩
      apply mem_right_mul
      assumption
      apply mem_right_mul
      assumption
      rw [←add_mul, ←add_mul, h]

-- ofCon i.toCon' it may be a slightly larger ideal
-- if α happens ot be a Ring, then `ofCon i.toCon' = i`
def Ideal.subOfConToCon' (i: Ideal α) : i ⊆ ofCon i.toCon' := by
  intro x hx
  refine ⟨x, ?_, 0, ?_, ?_⟩
  assumption
  apply mem_zero
  rw [add_zero, zero_add]
