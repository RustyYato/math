module

public import Math.Data.Set.Nonempty
public import Math.Algebra.Monoid.Set.Defs
public import Math.Algebra.Module.Defs.Basic
public import Math.Algebra.Module.Defs.Hom

namespace Math

public abbrev MemSMul (R: Type*) [SMul R α] [SetLike S α] (s: S) : Prop :=
  ∀{r: R} {a: α}, a ∈ s -> r • a ∈ s

public class IsMemSMul (S R α: Type*) [SetLike S α] [SMul R α] where
  mem_smul (s: S) : MemSMul R s := by intro s; exact s.mem_smul

export IsMemSMul (mem_smul)

public structure Submodule (R α: Type*) [Zero α] [Add α] [SMul R α] extends AddSubmonoid α where
  protected mem_smul : MemSMul R toSet

public instance [Zero α] [Add α] [SMul R α] : SetLike (Submodule R α) α where
public instance [Zero α] [Add α] [SMul R α] : IsMemZero (Submodule R α) α where
public instance [Zero α] [Add α] [SMul R α] : IsMemAdd (Submodule R α) α where
public instance [Zero α] [Add α] [SMul R α] : IsMemSMul (Submodule R α) R α where

namespace MemSMul

public theorem copy [SMul R α] [SetLike S α] [IsMemSMul S R α]
  (u: Set α) (h: ∃s: S, u = s) : MemSMul R u := by
  obtain ⟨s, rfl⟩ := h
  exact mem_smul s

public theorem copy' [SMul R α] [SetLike S α] [IsMemSMul S R α]
  {s: S} {u: Set α} (h: ∀x, x ∈ s ↔ x ∈ u) : MemSMul R u := by
  intro r a ha
  apply (h _).mp
  apply mem_smul
  apply (h _).mpr; assumption

variable [SMul R α] [SMul R β] [Funlike F α β] [IsSMulHom F R α β]

public theorem preimage [SetLike S β] [IsMemSMul S R β] (f: F) (s: S) : MemSMul R (Set.preimage f s) := by
  intro r a ha
  show f _ ∈ s; rw [map_smul]
  apply mem_smul <;> assumption

public theorem image [SetLike S α] [IsMemSMul S R α] (f: F) (s: S) : MemSMul R (Set.image f s) := by
  intro r a ha; simp at *
  obtain ⟨a, ha, rfl⟩ := ha
  exists r • a
  apply And.intro
  exact mem_smul s ha
  rw [map_smul]

end MemSMul

namespace Submodule

variable [Zero α] [Add α] [SMul R α]

inductive Span (U: Set α) : α -> Prop where
| of {a: α} : a ∈ U -> Span U a
| zero : Span U 0
| smul {r: R} {a: α} : Span U a -> Span U (r • a)
| add {a b: α} : Span U a -> Span U b -> Span U (a + b)

public def span (R: Type*) [SMul R α] (U: Set α) : Submodule R α where
  toSet := { Mem := Span U }
  mem_zero := Span.zero
  mem_smul := Span.smul
  mem_add := Span.add

public theorem sub_span {U: Set α} : U ⊆ span R U := fun _ => Span.of
public theorem of_mem_span [SetLike S α] [IsMemZero S α] [IsMemAdd S α] [IsMemSMul S R α]
  (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ span R U, x ∈ s := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | zero => apply mem_zero
  | smul => apply mem_smul <;> assumption
  | add => apply mem_add <;> assumption

public abbrev closure (U: Set α) : Submodule R α := span R U

public theorem sub_closure {U: Set α} : U ⊆ span R U := sub_span
public theorem of_mem_closure [SetLike S α] [IsMemZero S α] [IsMemAdd S α] [IsMemSMul S R α]
  (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ span R U, x ∈ s := of_mem_span _ _ h

public instance : Top (Submodule R α) where
   top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_smul _ := True.intro
    mem_add _ _ := True.intro
   }

public instance [IsLawfulZero α] [IsLawfulSMulZero R α] : Bot (Submodule R α) where
   bot := {
    toSet := {0}
    mem_zero := rfl
    mem_smul {r a} := by
      intro rfl; rw [smul_zero]; rfl
    mem_add {a b} := by
      intro rfl rfl; rw [add_zero]; rfl
   }

public theorem bot_sub [IsLawfulZero α] [IsLawfulSMulZero R α] (a: Submodule R α) : ⊥ ⊆ a := by intro x rfl; exact mem_zero a
public theorem sub_top (a: Submodule R α) : a ⊆ ⊤ := fun _ _ => True.intro

section

variable [SetLike S α] [IsMemZero S α] [IsMemAdd S α] [IsMemSMul S R α]

@[expose] public def of (R: Type*) [SMul R α] [IsMemSMul S R α] (s: S) : Submodule R α where
  toSet := s
  mem_zero := mem_zero s
  mem_smul := mem_smul s
  mem_add := mem_add s
@[expose] public def copy (R: Type*) [SMul R α] [IsMemSMul S R α] (s: S) (u: Set α) (hu: ∀x, x ∈ s ↔ x ∈ u) : Submodule R α where
  toSet := u
  mem_zero := MemZero.copy' hu
  mem_smul := MemSMul.copy' hu
  mem_add := MemAdd.copy' hu

@[simp] public theorem mem_of {s: S} : ∀{x}, x ∈ of R s ↔ x ∈ s := Iff.rfl
@[simp] public theorem mem_copy {s: S} {u: Set α} {hu} : ∀{x}, x ∈ copy R s u hu ↔ x ∈ s := (hu _).symm

end

end Submodule

instance [SetLike S α] [AddMonoidOps α] [IsAddMonoid α] [IsMemZero S α] [IsMemAdd S α] : IsMemSMul S ℕ α where
  mem_smul _ r a := by apply mem_nsmul
