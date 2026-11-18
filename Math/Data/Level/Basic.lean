module

public import Math.Data.Level.Defs

@[expose] section

namespace Math

namespace Kind

public inductive IsLeSProp : Kind -> Prop where
| sprop : IsLeSProp .sprop
| trunc : IsLeSProp a -> IsLeSProp (.trunc a)
| max : IsLeSProp a -> IsLeSProp b -> IsLeSProp (.max a b)

public inductive IsPropLe : Kind -> Prop where
| prop : IsPropLe .prop
| type : IsPropLe .type
| trunc : IsPropLe a -> IsPropLe (.trunc a)
| max_left : IsPropLe a -> IsPropLe (.max a b)
| max_right : IsPropLe b -> IsPropLe (.max a b)

public inductive IsTypeLe : Kind -> Prop where
| type : IsTypeLe .type
| max_left : IsTypeLe a -> IsTypeLe (.max a b)
| max_right : IsTypeLe b -> IsTypeLe (.max a b)

public def le_sprop : Kind -> Bool
| .sprop => true
| .trunc a => a.le_sprop
| .max a b => a.le_sprop && b.le_sprop
| .prop | .type | .param _ => false

public theorem le_sprop_spec : le_sprop a ↔ IsLeSProp a := by
  induction a with
  | sprop =>
    apply Iff.intro
    intro; apply IsLeSProp.sprop
    intro; rfl
  | prop | type | param =>
    apply Iff.intro
    nofun; nofun
  | trunc a ih =>
    apply Iff.intro
    intro h; apply IsLeSProp.trunc; apply ih.mp; assumption
    intro h; apply ih.mpr; cases h; assumption
  | max a b iha ihb =>
    apply Iff.intro
    intro h
    have ⟨h₀, h₁⟩ := Bool.and_eq_true_iff.mp h
    apply IsLeSProp.max
    apply iha.mp; assumption
    apply ihb.mp; assumption
    intro h; apply Bool.and_eq_true_iff.mpr
    cases h
    apply And.intro
    apply iha.mpr; assumption
    apply ihb.mpr; assumption

public instance : Decidable (IsLeSProp k) :=
  decidable_of_bool _ le_sprop_spec

public def prop_le : Kind -> Bool
| .type | .prop => true
| .max a b => a.prop_le || b.prop_le
| .trunc a => a.prop_le
| .param _ | .sprop => false

public theorem prop_le_spec : prop_le a ↔ IsPropLe a := by
  induction a with
  | prop | type =>
    apply Iff.intro
    intro; first|apply IsPropLe.prop|apply IsPropLe.type
    intro; rfl
  | sprop  | param =>
    apply Iff.intro
    nofun; nofun
  | trunc a ih =>
    apply Iff.intro
    intro h; apply IsPropLe.trunc; apply ih.mp; assumption
    intro h; apply ih.mpr; cases h; assumption
  | max a b iha ihb =>
    apply Iff.intro
    intro h
    cases Bool.or_eq_true_iff.mp h
    apply IsPropLe.max_left
    apply iha.mp; assumption
    apply IsPropLe.max_right
    apply ihb.mp; assumption
    intro h; apply Bool.or_eq_true_iff.mpr
    cases h
    left; apply iha.mpr; assumption
    right; apply ihb.mpr; assumption

public instance : Decidable (IsPropLe k) :=
  decidable_of_bool _ prop_le_spec

public def type_le : Kind -> Bool
| .type => true
| .max a b => a.type_le || b.type_le
| .param _ | .trunc _ | .sprop | .prop => false

public theorem type_le_spec : type_le a ↔ IsTypeLe a := by
  induction a with
  | type =>
    apply Iff.intro
    intro; first|apply IsTypeLe.type
    intro; rfl
  | trunc | prop | sprop  | param =>
    apply Iff.intro
    nofun; nofun
  | max a b iha ihb =>
    apply Iff.intro
    intro h
    cases Bool.or_eq_true_iff.mp h
    apply IsTypeLe.max_left
    apply iha.mp; assumption
    apply IsTypeLe.max_right
    apply ihb.mp; assumption
    intro h; apply Bool.or_eq_true_iff.mpr
    cases h
    left; apply iha.mpr; assumption
    right; apply ihb.mpr; assumption

public instance : Decidable (IsTypeLe k) :=
  decidable_of_bool _ type_le_spec

public inductive IsTruncLe : Kind -> Kind -> Prop where
| sprop : IsTruncLe .sprop a
| prop : IsPropLe a -> IsTruncLe .prop a
| type : IsPropLe a -> IsTruncLe .type a

| max : IsTruncLe a k -> IsTruncLe b k -> IsTruncLe (.max a b) k
| max_left : IsTruncLe k a -> IsTruncLe k (.max a b)
| max_right : IsTruncLe k b -> IsTruncLe k (.max a b)

| trunc : IsTruncLe a b -> IsTruncLe (.trunc a) b
| param_prop : IsTruncLe (.param i) .prop
| param_type : IsTruncLe (.param i) .type
| param_trunc : IsTruncLe (.param i) b -> IsTruncLe (.param i) (.trunc b)
| param : IsTruncLe (.param i) (.param i)

public def trunc_ble (a b: Kind) : Bool := match a with
| .sprop => true
| .prop | .type => b.prop_le
| .max a₀ a₁ => a₀.trunc_ble b && a₁.trunc_ble b
| .trunc a => a.trunc_ble b
| .param i =>
  match b with
  | .sprop => false
  | .trunc b => a.trunc_ble b
  | .type | .prop => true
  | .param j => i == j
  | .max b₀ b₁ => a.trunc_ble b₀ || a.trunc_ble b₁

theorem IsTruncLe.helper₀ : IsTruncLe (.trunc a) b -> IsTruncLe a b := by
  generalize hA:a.trunc = A
  intro h; induction h generalizing a
  any_goals contradiction
  rename_i ih;
  apply IsTruncLe.max_left
  apply ih; assumption
  rename_i ih;
  apply IsTruncLe.max_right
  apply ih; assumption
  cases hA; assumption

theorem IsTruncLe.helper₁ : IsTruncLe .prop b -> IsPropLe b := by
  generalize hA:Kind.prop = A
  intro h; induction h
  any_goals contradiction
  cases hA; assumption
  rename_i ih
  apply IsPropLe.max_left
  apply ih; assumption
  rename_i ih;
  apply IsPropLe.max_right
  apply ih; assumption

theorem IsTruncLe.helper₂ : IsTruncLe .type b -> IsPropLe b := by
  generalize hA:Kind.type = A
  intro h; induction h
  any_goals contradiction
  cases hA; assumption
  rename_i ih
  apply IsPropLe.max_left
  apply ih; assumption
  rename_i ih;
  apply IsPropLe.max_right
  apply ih; assumption

theorem IsTruncLe.helper₃ : IsTruncLe (.max a b) k -> IsTruncLe a k ∧ IsTruncLe b k := by
  generalize hA:a.max b = A
  intro h; induction h
  any_goals contradiction
  · rename_i k₀ k₁ ih₀ ih₁
    cases hA; apply And.intro <;> assumption
  · rename_i ih
    apply And.intro
    apply IsTruncLe.max_left
    exact (ih hA).left
    apply IsTruncLe.max_left
    exact (ih hA).right
  · rename_i ih
    apply And.intro
    apply IsTruncLe.max_right
    exact (ih hA).left
    apply IsTruncLe.max_right
    exact (ih hA).right

public theorem trunc_ble_spec : trunc_ble a b ↔ IsTruncLe a b := by
  apply Iff.intro
  · induction a with
    | sprop => intro; apply IsTruncLe.sprop
    | prop | type =>
      intro h; first|apply IsTruncLe.prop|apply IsTruncLe.type
      unfold trunc_ble at h; apply prop_le_spec.mp; assumption
    | trunc a ih =>
      unfold trunc_ble
      intro h; apply IsTruncLe.trunc
      apply ih; assumption
    | max x y iha ihb =>
      unfold trunc_ble
      intro h
      have ⟨h₀, h₁⟩ := Bool.and_eq_true_iff.mp h
      apply IsTruncLe.max
      apply iha; assumption
      apply ihb; assumption
    | param i =>
      induction b with
      | sprop =>
        unfold trunc_ble
        nofun
      | prop | type =>
        unfold trunc_ble
        intro; first|apply IsTruncLe.param_prop|apply IsTruncLe.param_type
      | param j =>
        unfold trunc_ble; dsimp
        intro h; rw [beq_iff_eq.mp h]; apply IsTruncLe.param
      | trunc a ih =>
        unfold trunc_ble
        intro h; apply IsTruncLe.param_trunc
        apply ih; assumption
      | max a b iha ihb =>
        unfold trunc_ble
        intro h
        cases  Bool.or_eq_true_iff.mp h
        apply IsTruncLe.max_left
        apply iha; assumption
        apply IsTruncLe.max_right
        apply ihb; assumption
  · intro h
    induction h with
    | sprop => unfold trunc_ble; rfl
    | prop
    | type => unfold trunc_ble; apply prop_le_spec.mpr; assumption
    | max => unfold trunc_ble; apply Bool.and_eq_true_iff.mpr; apply And.intro <;> assumption
    | trunc => unfold trunc_ble; assumption
    | param_prop
    | param_type => unfold trunc_ble; rfl
    | param_trunc => unfold trunc_ble; assumption
    | param => unfold trunc_ble; dsimp; apply beq_iff_eq.mpr; rfl
    | @max_left k a b ha ih
    | @max_right k a b ha ih =>
      induction k with
      | sprop => unfold trunc_ble; rfl
      | prop =>
        unfold trunc_ble
        apply prop_le_spec.mpr
        apply IsTruncLe.helper₁
        first|(apply IsTruncLe.max_left; assumption)|(apply IsTruncLe.max_right; assumption)
      | type =>
        unfold trunc_ble
        apply prop_le_spec.mpr
        apply IsTruncLe.helper₂
        first|(apply IsTruncLe.max_left; assumption)|(apply IsTruncLe.max_right; assumption)
      | param => unfold trunc_ble; apply Bool.or_eq_true_iff.mpr; first|(left; assumption)|(right; assumption)
      | trunc k ih₀ =>
        unfold trunc_ble
        apply ih₀
        apply IsTruncLe.helper₀
        assumption
        unfold trunc_ble at ih
        assumption
      | max k₀ k₁ ih₀ ih₁ =>
        unfold trunc_ble
        apply Bool.and_eq_true_iff.mpr
        apply And.intro
        · apply ih₀
          · exact (IsTruncLe.helper₃ ha).left
          · unfold trunc_ble at ih
            exact (Bool.and_eq_true_iff.mp ih).left
        · apply ih₁
          · exact (IsTruncLe.helper₃ ha).right
          · unfold trunc_ble at ih
            exact (Bool.and_eq_true_iff.mp ih).right

public instance : Decidable (IsTruncLe a b) :=
    decidable_of_bool _ trunc_ble_spec

public protected inductive LE : Kind -> Kind -> Prop where
| sprop : Kind.LE .sprop a
| prop : IsPropLe a -> Kind.LE .prop a
| type : IsTypeLe a -> Kind.LE .type a

| max : Kind.LE a k -> Kind.LE b k -> Kind.LE (.max a b) k
| max_left : Kind.LE k a -> Kind.LE k (.max a b)
| max_right : Kind.LE k b -> Kind.LE k (.max a b)

| trunc : IsTruncLe a b -> Kind.LE (.trunc a) b

| param_type : Kind.LE (.param i) .type
| param : Kind.LE (.param i) (.param i)

public instance : LE Kind where
  le := Kind.LE

public def ble (a b: Kind) : Bool := match a with
| .sprop => true
| .prop => b.prop_le
| .type => b.type_le
| .max a₀ a₁ => a₀.ble b && a₁.ble b
| .trunc a => a.trunc_ble b
| .param i =>
  match b with
  | .sprop | .prop | .trunc _ => false
  | .type => true
  | .param j => i == j
  | .max b₀ b₁ => a.ble b₀ || a.ble b₁

theorem Kind.LE.helper₁ : Kind.LE .prop b -> IsPropLe b := by
  generalize hA:Kind.prop = A
  intro h; induction h
  any_goals contradiction
  cases hA; assumption
  rename_i ih
  apply IsPropLe.max_left
  apply ih; assumption
  rename_i ih;
  apply IsPropLe.max_right
  apply ih; assumption

theorem Kind.LE.helper₂ : Kind.LE .type b -> IsTypeLe b := by
  generalize hA:Kind.type = A
  intro h; induction h
  any_goals contradiction
  cases hA; assumption
  rename_i ih
  apply IsTypeLe.max_left
  apply ih; assumption
  rename_i ih;
  apply IsTypeLe.max_right
  apply ih; assumption

theorem Kind.LE.helper₃ : Kind.LE (.max a b) k -> Kind.LE a k ∧ Kind.LE b k := by
  generalize hA:a.max b = A
  intro h; induction h
  any_goals contradiction
  · rename_i k₀ k₁ ih₀ ih₁
    cases hA; apply And.intro <;> assumption
  · rename_i ih
    apply And.intro
    apply Kind.LE.max_left
    exact (ih hA).left
    apply Kind.LE.max_left
    exact (ih hA).right
  · rename_i ih
    apply And.intro
    apply Kind.LE.max_right
    exact (ih hA).left
    apply Kind.LE.max_right
    exact (ih hA).right

theorem Kind.LE.helper₅ : Kind.LE (.trunc a) b -> IsTruncLe a b := by
  generalize hA:a.trunc = A
  intro h; induction h
  any_goals cases hA
  · rename_i k₀ k₁ ih₀ ih₁
    apply IsTruncLe.max_left
    apply ih₁; rfl
  · rename_i k₀ k₁ ih₀ ih₁
    apply IsTruncLe.max_right
    apply ih₁; rfl
  · assumption

public theorem ble_spec : ble a b ↔ a ≤ b := by
  apply Iff.intro
  · induction a with
    | sprop => intro; apply Kind.LE.sprop
    | prop =>
      intro h; apply Kind.LE.prop
      unfold ble at h; apply prop_le_spec.mp; assumption
    | type =>
      intro h; apply Kind.LE.type
      unfold ble at h; apply type_le_spec.mp; assumption
    | max x y iha ihb =>
      unfold ble
      intro h
      have ⟨h₀, h₁⟩ := Bool.and_eq_true_iff.mp h
      apply Kind.LE.max
      apply iha; assumption
      apply ihb; assumption
    | trunc a ih =>
      clear ih
      intro h; apply LE.trunc
      apply trunc_ble_spec.mp
      unfold ble at h
      assumption
    | param i =>
      induction b with
      | sprop | prop | trunc _ =>
        unfold ble
        nofun
      | type =>
        unfold ble
        intro; first|apply Kind.LE.param_prop|apply Kind.LE.param_type
      | param j =>
        unfold ble; dsimp
        intro h; rw [beq_iff_eq.mp h]; apply Kind.LE.param
      | max a b iha ihb =>
        unfold ble
        intro h
        cases  Bool.or_eq_true_iff.mp h
        apply Kind.LE.max_left
        apply iha; assumption
        apply Kind.LE.max_right
        apply ihb; assumption
  · intro h
    induction h with
    | sprop => unfold ble; rfl
    | prop => unfold ble; apply prop_le_spec.mpr; assumption
    | type => unfold ble; apply type_le_spec.mpr; assumption
    | max => unfold ble; apply Bool.and_eq_true_iff.mpr; apply And.intro <;> assumption
    | trunc => unfold ble; apply trunc_ble_spec.mpr; assumption
    | param_type => unfold ble; rfl
    | param => unfold ble; dsimp; apply beq_iff_eq.mpr; rfl
    | @max_left k a b ha ih
    | @max_right k a b ha ih =>
      induction k with
      | sprop => unfold ble; rfl
      | prop =>
        unfold ble
        apply prop_le_spec.mpr
        apply Kind.LE.helper₁
        first|(apply Kind.LE.max_left; assumption)|(apply Kind.LE.max_right; assumption)
      | type =>
        unfold ble
        apply type_le_spec.mpr
        apply Kind.LE.helper₂
        first|(apply Kind.LE.max_left; assumption)|(apply Kind.LE.max_right; assumption)
      | param => unfold ble; apply Bool.or_eq_true_iff.mpr; first|(left; assumption)|(right; assumption)
      | trunc k ih₀ =>
        unfold ble
        unfold ble at ih
        apply trunc_ble_spec.mpr
        first|(
        apply IsTruncLe.max_left
        apply trunc_ble_spec.mp
        assumption)|(
        apply IsTruncLe.max_right
        apply trunc_ble_spec.mp
        assumption)
      | max k₀ k₁ ih₀ ih₁ =>
        unfold ble
        apply Bool.and_eq_true_iff.mpr
        apply And.intro
        · apply ih₀
          · exact (Kind.LE.helper₃ ha).left
          · unfold ble at ih
            exact (Bool.and_eq_true_iff.mp ih).left
        · apply ih₁
          · exact (Kind.LE.helper₃ ha).right
          · unfold ble at ih
            exact (Bool.and_eq_true_iff.mp ih).right

public instance : Decidable (Kind.LE a b) :=
    decidable_of_bool _ ble_spec

theorem IsTruncLe.helper₄ : IsTruncLe k a.trunc -> IsTruncLe k (.trunc (.max a b)) := by
  generalize hA:a.trunc=A
  intro h; induction h
  all_goals cases hA
  · apply IsTruncLe.sprop
  · apply IsTruncLe.prop
    rename_i h; cases h; apply IsPropLe.trunc; apply IsPropLe.max_left; assumption
  · apply IsTruncLe.type
    rename_i h; cases h; apply IsPropLe.trunc; apply IsPropLe.max_left; assumption
  · rename_i iha ihb; apply IsTruncLe.max
    apply iha; rfl
    apply ihb; rfl
  · rename_i ih; apply IsTruncLe.trunc
    apply ih; rfl
  · apply IsTruncLe.param_trunc
    apply IsTruncLe.max_left
    assumption
theorem IsTruncLe.helper₅ : IsTruncLe k b.trunc -> IsTruncLe k (.trunc (.max a b)) := by
  generalize hA:b.trunc=A
  intro h; induction h
  all_goals cases hA
  · apply IsTruncLe.sprop
  · apply IsTruncLe.prop
    rename_i h; cases h; apply IsPropLe.trunc; apply IsPropLe.max_right; assumption
  · apply IsTruncLe.type
    rename_i h; cases h; apply IsPropLe.trunc; apply IsPropLe.max_right; assumption
  · rename_i iha ihb; apply IsTruncLe.max
    apply iha; rfl
    apply ihb; rfl
  · rename_i ih; apply IsTruncLe.trunc
    apply ih; rfl
  · apply IsTruncLe.param_trunc
    apply IsTruncLe.max_right
    assumption

theorem IsTruncLe.helper₆ : IsTruncLe a b -> IsTruncLe a b.trunc := by
  intro h; induction h with
  | sprop => apply IsTruncLe.sprop
  | prop => apply IsTruncLe.prop; apply IsPropLe.trunc; assumption
  | type => apply IsTruncLe.type; apply IsPropLe.trunc; assumption
  | trunc =>
    apply IsTruncLe.trunc
    assumption
  | max =>
    apply IsTruncLe.max
    assumption
    assumption
  | max_left =>
    apply helper₄
    assumption
  | max_right =>
    apply helper₅
    assumption
  | param_prop =>
    apply IsTruncLe.param_trunc
    apply IsTruncLe.param_prop
  | param_type =>
    apply IsTruncLe.param_trunc
    apply IsTruncLe.param_type
  | param_trunc =>
    apply IsTruncLe.param_trunc
    assumption
  | param =>
    apply IsTruncLe.param_trunc
    apply IsTruncLe.param

theorem trunc_le_trunc_self (a: Kind) : a.IsTruncLe a.trunc := by
    induction a with
    | sprop => apply IsTruncLe.sprop
    | prop => apply IsTruncLe.prop; apply IsPropLe.trunc; apply IsPropLe.prop
    | type => apply IsTruncLe.type; apply IsPropLe.trunc; apply IsPropLe.type
    | param => apply IsTruncLe.param_trunc; apply IsTruncLe.param
    | trunc =>
      apply IsTruncLe.trunc
      apply IsTruncLe.helper₆
      assumption
    | max =>
      apply IsTruncLe.max
      apply IsTruncLe.helper₄
      assumption
      apply IsTruncLe.helper₅
      assumption

theorem le_refl' (a: Kind) : a ≤ a := by
  induction a with
  | sprop => apply LE.sprop
  | prop => apply LE.prop; apply IsPropLe.prop
  | type => apply LE.type; apply IsTypeLe.type
  | param => apply LE.param
  | trunc =>
    apply LE.trunc
    apply trunc_le_trunc_self
  | max =>
    apply LE.max
    apply LE.max_left
    assumption
    apply LE.max_right
    assumption

theorem trunc_le_of_le_sprop (a b: Kind) : a.IsLeSProp -> IsTruncLe a b := by
  intro h
  induction h with
  | sprop => apply IsTruncLe.sprop
  | max =>
    apply IsTruncLe.max
    assumption
    assumption
  | @trunc a h ih =>
    apply IsTruncLe.trunc
    assumption

public theorem le_of_le_sprop (a b: Kind) : a.IsLeSProp -> a ≤ b := by
  intro h
  induction h with
  | sprop => apply LE.sprop
  | max =>
    apply LE.max
    assumption
    assumption
  | @trunc a h ih =>
    apply LE.trunc
    apply trunc_le_of_le_sprop
    assumption

public theorem trunc_le_of_type_le (a b: Kind) : b.IsTypeLe -> IsTruncLe a b := by
  intro h
  induction h with
  | type =>
    induction a with
    | sprop => apply IsTruncLe.sprop
    | prop => apply IsTruncLe.prop; apply IsPropLe.type
    | type => apply IsTruncLe.type; apply IsPropLe.type
    | param => apply IsTruncLe.param_type
    | trunc => apply IsTruncLe.trunc; assumption
    | max => apply IsTruncLe.max; assumption; assumption
  | max_left =>
    apply IsTruncLe.max_left
    assumption
  | max_right =>
    apply IsTruncLe.max_right
    assumption
public theorem le_of_type_le (a b: Kind) : b.IsTypeLe -> a ≤ b := by
  intro h
  induction h with
  | type =>
    induction a with
    | sprop => apply LE.sprop
    | prop => apply LE.prop; apply IsPropLe.type
    | type => apply LE.type; apply IsTypeLe.type
    | param => apply LE.param_type
    | trunc => apply LE.trunc; apply trunc_le_of_type_le; apply IsTypeLe.type
    | max => apply LE.max; assumption; assumption
  | max_left =>
    apply LE.max_left
    assumption
  | max_right =>
    apply LE.max_right
    assumption

theorem IsPropLe.ofIsTypeLe : IsTypeLe a -> IsPropLe a := by
  intro h
  induction h with
  | type => apply IsPropLe.type
  | max_left _ ih =>
    refine IsPropLe.max_left ?_; apply ih;
  | max_right _ ih =>
    refine IsPropLe.max_right ?_; apply ih

theorem IsPropLe.of_le : IsPropLe a -> a ≤ b -> IsPropLe b := by
  intro h g
  induction h with
  | prop => exact Kind.LE.helper₁ g
  | type =>
    apply IsPropLe.ofIsTypeLe
    exact Kind.LE.helper₂ g
  | @trunc a h ih =>
    clear ih
    replace g := Kind.LE.helper₅ g
    induction h with
    | prop => exact IsTruncLe.helper₁ g
    | type => exact IsTruncLe.helper₂ g
    | trunc _ ih =>
      apply ih
      exact IsTruncLe.helper₀ g
    | max_left _ ih =>
      apply ih
      exact (IsTruncLe.helper₃ g).left
    | max_right _ ih =>
      apply ih
      exact (IsTruncLe.helper₃ g).right
  | max_left _ ih =>
    apply ih
    exact (Kind.LE.helper₃ g).left
  | max_right _ ih =>
    apply ih
    exact (Kind.LE.helper₃ g).right

theorem IsPropLe.of_trunc_le : IsPropLe a -> IsTruncLe a b -> IsPropLe b := by
  intro h g
  induction h with
  | prop => exact IsTruncLe.helper₁ g
  | type => exact IsTruncLe.helper₂ g
  | @trunc a h ih => apply ih; exact IsTruncLe.helper₀ g
  | max_left _ ih =>
    apply ih
    exact (IsTruncLe.helper₃ g).left
  | max_right _ ih =>
    apply ih
    exact (IsTruncLe.helper₃ g).right

theorem IsTruncLe.of_prop_le : IsPropLe b -> IsTruncLe a b := by
  intro h
  induction a with
  | sprop => apply IsTruncLe.sprop
  | prop => apply IsTruncLe.prop; assumption
  | type => apply IsTruncLe.type; assumption
  | trunc a ih =>
    apply IsTruncLe.trunc
    assumption
  | max a b iha ihb =>
    apply IsTruncLe.max
    assumption
    assumption
  | param i =>
    induction h with
    | prop => apply IsTruncLe.param_prop
    | type => apply IsTruncLe.param_type
    | trunc => apply IsTruncLe.param_trunc; assumption
    | max_left => apply IsTruncLe.max_left; assumption
    | max_right => apply IsTruncLe.max_right; assumption

instance : IsTrans IsTruncLe where
  htrans {a b c} h g := by
    induction h with
    | sprop => apply IsTruncLe.sprop
    | prop
    | type =>
      first|apply IsTruncLe.prop| apply IsTruncLe.type
      apply IsPropLe.of_trunc_le
      assumption
      assumption
    | max _ _ iha ihb =>
      apply IsTruncLe.max
      apply iha; assumption
      apply ihb; assumption
    | max_left _ ih =>
      apply ih
      exact (IsTruncLe.helper₃ g).left
    | max_right _ ih =>
      apply ih
      exact (IsTruncLe.helper₃ g).right
    | param_prop =>
      apply IsTruncLe.of_prop_le
      exact IsTruncLe.helper₁ g
    | param_type =>
      apply IsTruncLe.of_prop_le
      exact IsTruncLe.helper₂ g
    | param_trunc _ ih =>
      apply ih
      exact IsTruncLe.helper₀ g
    | param => assumption
    | trunc _  ih =>
      apply IsTruncLe.trunc
      apply ih
      assumption

public instance : LT Kind where
  lt a b := a ≤ b ∧ ¬b ≤ a
public instance : IsPreorder Kind where
  lt_iff_le_and_not_ge := Iff.rfl
  refl := le_refl'
  htrans {a b c} h g := by
    induction h with
    | sprop => apply LE.sprop
    | @prop a h =>
      apply LE.prop
      apply IsPropLe.of_le
      assumption
      assumption
    | @type a h =>
      apply LE.type
      induction h with
      | type => exact Kind.LE.helper₂ g
      | max_left _ ih =>
        apply ih
        exact (Kind.LE.helper₃ g).left
      | max_right _ ih =>
        apply ih
        exact (Kind.LE.helper₃ g).right
    | max a b iha ihb =>
      apply LE.max
      apply iha
      assumption
      apply ihb
      assumption
    | max_left _ ih =>
      apply ih
      exact (Kind.LE.helper₃ g).left
    | max_right _ ih =>
      apply ih
      exact (Kind.LE.helper₃ g).right
    | param_type =>
      apply le_of_type_le
      exact Kind.LE.helper₂ g
    | param => assumption
    | @trunc a b h =>
      apply LE.trunc
      apply htrans; assumption
      clear h
      induction g with
      | sprop => apply IsTruncLe.sprop
      | prop => apply IsTruncLe.prop; assumption
      | type =>
        apply IsTruncLe.type
        apply IsPropLe.ofIsTypeLe
        assumption
      | max => apply IsTruncLe.max <;> assumption
      | max_left => apply IsTruncLe.max_left; assumption
      | max_right => apply IsTruncLe.max_right; assumption
      | trunc => apply IsTruncLe.trunc; assumption
      | param_type => apply IsTruncLe.param_type
      | param => apply IsTruncLe.param

public theorem prop_le_sound {a: Kind} : IsPropLe a -> eval_le .prop a := by
  intro h; induction h with
  | prop => intro; apply le_refl
  | type => intro; apply le_top
  | @trunc a _ ih =>
    intro f; replace ih := ih f
    revert ih; simp [eval]
    generalize eval f a=A
    decide +revert
  | max_left _ ih =>
    intro f; simp [eval]; apply le_trans (ih f)
    apply left_le_max
  | max_right _ ih =>
    intro f; simp [eval]; apply le_trans (ih f)
    apply right_le_max
public theorem type_le_sound {a: Kind} : IsTypeLe a -> eval_le .type a := by
  intro h; induction h with
  | type => intro; apply le_top
  | max_left _ ih =>
    intro f; simp [eval]; apply le_trans (ih f)
    apply left_le_max
  | max_right _ ih =>
    intro f; simp [eval]; apply le_trans (ih f)
    apply right_le_max
public theorem trunc_le_sound {a b: Kind} : IsTruncLe a b -> eval_le (.trunc a) b := by
  intro h; induction h with
  | sprop => intro f; simp [eval]; apply bot_le
  | prop | type =>
    apply prop_le_sound
    assumption
  | @max a b k _ _ iha ihb =>
    intro f
    replace iha := iha f
    replace ihb := ihb f
    revert iha ihb
    simp [eval]
    generalize eval f a = A
    generalize eval f b = B
    generalize eval f k = K
    decide +revert
  | max_left _ ih =>
    intro f; simp [eval]; apply le_trans (ih f)
    apply left_le_max
  | max_right _ ih =>
    intro f; simp [eval]; apply le_trans (ih f)
    apply right_le_max
  | trunc a iha =>
    intro f; simp [eval]
    rw [show ∀a: ConcreteKind, a.trunc.trunc = a.trunc by decide]
    apply iha
  | @param_prop i
  | @param_type i =>
    intro f; simp [eval]
    generalize f i = A; decide +revert
  | @param_trunc i a _ ih =>
    intro f; replace ih := ih f
    revert ih; simp [eval]
    generalize f i = A
    generalize eval f a = B
    decide +revert
  | @param i =>
    intro f; simp [eval]; generalize f i = A
    decide +revert

public theorem le_sound {a b: Kind} : a ≤ b -> a.eval_le b := by
  intro h; induction h with
  | sprop => intro; apply bot_le
  | prop => apply prop_le_sound; assumption
  | type => apply type_le_sound; assumption
  | @max a b k ha hb iha ihb =>
    intro i; simp [eval]
    apply max_le; apply iha; apply ihb
  | max_left _  ih =>
    intro i; simp [eval]
    apply le_trans _ (left_le_max _ _)
    apply ih
  | max_right _ ih =>
    intro i; simp [eval]
    apply le_trans _ (right_le_max _ _)
    apply ih
  | trunc =>
    apply trunc_le_sound
    assumption
  | param_type => intro i; apply le_top
  | param => intro; apply le_refl

end Kind
