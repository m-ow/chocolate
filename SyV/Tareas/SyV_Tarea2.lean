import SyV.SyVPrelude

set_option autoImplicit false
set_option tactic.hygienic false

namespace SyV

#print State

inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → ℕ) → Stmt
  | comp       : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo    : (State → Prop) → Stmt → Stmt
  -- Nueva instrucción `for`
  | forDo    : String → (State → ℕ) → (State → ℕ) → Stmt → Stmt

infixr:90 "; " => Stmt.comp

/- ## Semántica de Paso Grande -/

inductive BigStep : Stmt × State → State → Prop where
  | skip (s) : BigStep (Stmt.skip, s) s
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | comp (S T s t u) (hS : BigStep (S, s) t)
      (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | if_true (B S T s t) (hcond : B s)
      (hbody : BigStep (S, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | if_false (B S T s t) (hcond : ¬ B s)
      (hbody : BigStep (T, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | while_true (B S s t u) (hcond : B s)
      (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.whileDo B S, t) u) :
    BigStep (Stmt.whileDo B S, s) u
  | while_false (B S s) (hcond : ¬ B s) :
    BigStep (Stmt.whileDo B S, s) s
  -- Nueva regla para el caso `false` del `for`
  | for_false (x M N S s₀ s₁)
     (hassgn : BigStep (Stmt.assign x M, s₀) s₁)
     (hcond : ¬ ((fun s => s x ≤ N s) s₁)) :
    BigStep (Stmt.forDo x M N S, s₀) s₁
  -- Nueva regla para el caso `true` del `for`
  | for_true (x M N S s₀ s₁ s₂ s₃)
      (hassign : BigStep (Stmt.assign x M, s₀) s₁)
      (hcond : (fun s => s x ≤ N s) s₁)
      (hbody : BigStep (S, s₁) s₂)
      (hrest : BigStep (Stmt.forDo x (fun s ↦ (s x) + 1) N S, s₂) s₃) :
    BigStep (Stmt.forDo x M N S, s₀) s₃

infix:110 " ⟹ " => BigStep

/- ## Propiedades de la Semántica de Paso Grande -/

/- ### Ejercicio 1 (2 pts.) -/

theorem BigStep_deterministic {Ss l r} (hl : Ss ⟹ l)
    (hr : Ss ⟹ r) :
  l = r :=
  by
    induction hl generalizing r with
    | skip s =>
      cases hr with
      | skip => rfl
    | assign x a s =>
      cases hr with
      | assign => rfl
    | comp S T s l₀ l hS hT ihS ihT =>
      cases hr with
      | comp _ _ _ r₀ _ hS' hT' =>
        cases ihS hS' with
        | refl =>
          cases ihT hT' with
          | refl => rfl
    | if_true B S T s l hB hS ih =>
      cases hr with
      | if_true _ _ _ _ _ hB' hS'  => apply ih hS'
      | if_false _ _ _ _ _ hB' hS' => aesop
    | if_false B S T s l hB hT ih =>
      cases hr with
      | if_true _ _ _ _ _ hB' hS'  => aesop
      | if_false _ _ _ _ _ hB' hS' => apply ih hS'
    | while_true B S s l₀ l hB hS hw ihS ihw =>
      cases hr with
      | while_true _ _ _ r₀ hB' hB' hS' hw' =>
        cases ihS hS' with
        | refl =>
          cases ihw hw' with
          | refl => rfl
      | while_false _ _ _ hB' => aesop
    | while_false B S s hB =>
      cases hr with
      | while_true _ _ _ s' _ hB' hS hw => aesop
      | while_false _ _ _ hB'           => rfl
    | for_false _ _ _ _ _ _ hassign hcond hassign_ih =>
      -- Demuestra el caso `for_false` borrando el `sorry`
      sorry
    | for_true _ _ _ _ _ _ _ _ hassign hcond hbody hrest hassign_ih hbody_ih hrest_ih =>
      -- Demuestra el caso `for_true` borrando el `sorry`
      sorry


@[simp] theorem BigStep_skip_Iff {s t} :
  (Stmt.skip, s) ⟹ t ↔ t = s :=
  by
    apply Iff.intro
    . intro h
      cases h with
      | skip => rfl
    . intro h
      rw [h]
      apply BigStep.skip

@[simp] theorem BigStep_assign_Iff {x a s t} :
  (Stmt.assign x a, s) ⟹ t ↔ t = s[x ↦ a s] :=
  by
    apply Iff.intro
    . intro h
      cases h with
      | assign => rfl
    . intro h
      rw [h]
      apply BigStep.assign

@[simp] theorem BigStep_comp_Iff {S T s u} :
  (S; T, s) ⟹ u ↔ (∃t, (S, s) ⟹ t ∧ (T, t) ⟹ u) :=
  by
    apply Iff.intro
    . intro h
      cases h with
      | comp =>
        apply Exists.intro t
        apply And.intro <;> assumption
    . intro h
      cases h with
      | intro s' h' =>
        cases h' with
        | intro hS hT =>
          apply BigStep.comp <;>
            assumption

@[simp] theorem BigStep_if_Iff {B S T s t} :
  (Stmt.ifThenElse B S T, s) ⟹ t ↔
  (B s ∧ (S, s) ⟹ t) ∨ (¬ B s ∧ (T, s) ⟹ t) :=
  by
    apply Iff.intro
    . intro h
      cases h with
      | if_true _ _ _ _ _ hB hS =>
        apply Or.intro_left
        aesop
      | if_false _ _ _ _ _ hB hT =>
        apply Or.intro_right
        aesop
    . intro h
      cases h with
      | inl h =>
        cases h with
        | intro hB hS =>
          apply BigStep.if_true <;> assumption
      | inr h =>
        cases h with
        | intro hB hT =>
          apply BigStep.if_false <;> assumption

theorem BigStep_while_Iff {B S s u} :
  (Stmt.whileDo B S, s) ⟹ u ↔
  (∃t, B s ∧ (S, s) ⟹ t ∧ (Stmt.whileDo B S, t) ⟹ u)
  ∨ (¬ B s ∧ u = s) :=
  by
    apply Iff.intro
    . intro h
      cases h with
      | while_true _ _ _ t _ hB hS hw =>
        apply Or.intro_left
        apply Exists.intro t
        aesop
      | while_false _ _ _ hB =>
        apply Or.intro_right
        aesop
    . intro h
      cases h with
      | inl hex =>
        cases hex with
        | intro t h =>
          cases h with
          | intro hB h =>
            cases h with
            | intro hS hwhile =>
              apply BigStep.while_true <;>
                assumption
      | inr h =>
        cases h with
        | intro hB hus =>
          rw [hus]
          apply BigStep.while_false
          assumption

@[simp] theorem BigStep_while_true_Iff {B S s u}
    (hcond : B s) :
  (Stmt.whileDo B S, s) ⟹ u ↔
  (∃t, (S, s) ⟹ t ∧ (Stmt.whileDo B S, t) ⟹ u) :=
  by
    rw [BigStep_while_Iff]
    simp [hcond]

@[simp] theorem BigStep_while_false_Iff {B S s t}
    (hcond : ¬ B s) :
  (Stmt.whileDo B S, s) ⟹ t ↔ t = s :=
  by
    rw [BigStep_while_Iff]
    simp [hcond]


/- ### Ejercicio 2 (2 pts.) -/

theorem BigStep_for_Iff {x M N S s u} :
  (Stmt.forDo x M N S, s) ⟹ u ↔
  (∃t₁ t₂, (Stmt.assign x M, s) ⟹ t₁
    ∧ ((fun s => s x ≤ N s) t₁)
    ∧ (S, t₁) ⟹ t₂
    ∧ (Stmt.forDo x (fun s => (s x) + 1) N S, t₂) ⟹ u)
  ∨ ((Stmt.assign x M, s) ⟹ u ∧ ¬ ((fun s => s x ≤ N s) u)) :=
  by
    sorry


/- ## Semántica de Paso Pequeño -/

inductive SmallStep : Stmt × State → Stmt × State → Prop where
  | assign (x a s) :
    SmallStep (Stmt.assign x a, s) (Stmt.skip, s[x ↦ a s])
  | comp_step (S S' T s s') (hS : SmallStep (S, s) (S', s')) :
    SmallStep (S; T, s) (S'; T, s')
  | comp_skip (T s) :
    SmallStep (Stmt.skip; T, s) (T, s)
  | if_true (B S T s) (hcond : B s) :
    SmallStep (Stmt.ifThenElse B S T, s) (S, s)
  | if_false (B S T s) (hcond : ¬ B s) :
    SmallStep (Stmt.ifThenElse B S T, s) (T, s)
  | whileDo (B S s) :
    SmallStep (Stmt.whileDo B S, s)
      (Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip, s)
  -- Nueva regla `forDo`
  | forDo (x M N S s) :
    SmallStep (Stmt.forDo x M N S, s)
      (Stmt.assign x M ; Stmt.ifThenElse (fun s => s x ≤ N s)
                                         (S; Stmt.forDo x (fun s => s x + 1) N S)
                                         Stmt.skip, s)

infixr:100 " ⇒ " => SmallStep
infixr:100 " ⇒* " => RTC SmallStep

#print RTC

/- ## Propiedades de la semántica de Paso Pequeño -/

/- ### Ejercicio 3 (2 pts.) -/

theorem SmallStep_final (S s) :
  (¬ ∃T t, (S, s) ⇒ (T, t)) ↔ S = Stmt.skip :=
  by
    induction S with
    | skip =>
      simp
      intros T t hstep
      cases hstep
    | assign x a =>
      simp
      use Stmt.skip
      use (s[x ↦ a s])
      apply SmallStep.assign
    | comp S T ihS ihT =>
      simp
      cases Classical.em (S = Stmt.skip) with
      | inl h =>
        rw [h]
        use T
        use s
        apply SmallStep.comp_skip
      | inr h =>
        simp [h] at ihS
        let ⟨S', hS₀⟩ := ihS
        let ⟨s', hS⟩ := hS₀
        use (S'; T)
        use s'
        apply SmallStep.comp_step
        assumption
    | ifThenElse B S T ihS ihT =>
      simp
      cases Classical.em (B s) with
      | inl h =>
        use S
        use s
        apply SmallStep.if_true
        assumption
      | inr h =>
        use T
        use s
        apply SmallStep.if_false
        assumption
    | whileDo B S ih =>
      simp
      use (Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip)
      use s
      apply SmallStep.whileDo
    | forDo x M N S ih =>
      -- Demuestra el caso `forDo` borrando el `sorry`
      sorry

/- ### Ejercicio 4 (2 pts.) -/

theorem SmallStep_deterministic {Ss Ll Rr}
    (hl : Ss ⇒ Ll) (hr : Ss ⇒ Rr) :
  Ll = Rr :=
  by
    induction hl generalizing Rr with
    | assign x a s =>
      cases hr with
      | assign _ _ _ => rfl
    | comp_step S S₁ T s s₁ hS₁ ih =>
      cases hr with
      | comp_step S S₂ _ _ s₂ hS₂ =>
        have hipotesis_cool :=
          ih hS₂
        aesop
      | comp_skip => cases hS₁
    | comp_skip T s =>
      cases hr with
      | comp_step _ S _ _ s' hskip => cases hskip
      | comp_skip                  => rfl
    | if_true B S T s hB =>
      cases hr with
      | if_true  => rfl
      | if_false => aesop
    | if_false B S T s hB =>
      cases hr with
      | if_true  => aesop
      | if_false => rfl
    | whileDo B S s =>
      cases hr with
      | whileDo => rfl
    | forDo x M N S s =>
      -- Demuestra el caso `forDo` borrando el `sorry`
      sorry

theorem SmallStep_skip {S s t} :
  ¬ ((Stmt.skip, s) ⇒ (S, t)) :=
  by
    intro h
    cases h

@[simp] theorem SmallStep_comp_Iff {S T s Ut} :
  (S; T, s) ⇒ Ut ↔
  (∃S' t, (S, s) ⇒ (S', t) ∧ Ut = (S'; T, t))
  ∨ (S = Stmt.skip ∧ Ut = (T, s)) :=
  by
    apply Iff.intro
    . intro hST
      cases hST with
      | comp_step _ S' _ _ s' hS =>
        apply Or.intro_left
        use S'
        use s'
      | comp_skip =>
        apply Or.intro_right
        aesop
    . intro hor
      cases hor with
      | inl hex =>
        let ⟨S', hex'⟩ := hex
        let ⟨s', hand⟩ := hex'
        let ⟨hS, hUt⟩ := hand
        rw [hUt]
        apply SmallStep.comp_step
        assumption
      | inr hand =>
        let ⟨hS, hUt⟩ := hand
        rw [hS, hUt]
        apply SmallStep.comp_skip

@[simp] theorem SmallStep_if_Iff {B S T s Us} :
  (Stmt.ifThenElse B S T, s) ⇒ Us ↔
  (B s ∧ Us = (S, s)) ∨ (¬ B s ∧ Us = (T, s)) :=
  by
    apply Iff.intro
    . intro h
      cases h with
      | if_true _ _ _ _ hB  => aesop
      | if_false _ _ _ _ hB => aesop
    . intro hor
      cases hor with
      | inl hand =>
        let ⟨hB, hUs⟩ := hand
        rw [hUs]
        apply SmallStep.if_true
        assumption
      | inr hand =>
        let ⟨hB, hUs⟩ := hand
        rw [hUs]
        apply SmallStep.if_false
        assumption

/- ### Equivalencia entre la semántica de Paso Grande y Paso Pequeño -/

theorem RTC_SmallStep_comp {S T s u}
  (h : (S, s) ⇒* (Stmt.skip, u)) :
  (S; T, s) ⇒* (Stmt.skip; T, u) :=
  by
    apply RTC.lift (fun Ss ↦ (Prod.fst Ss; T, Prod.snd Ss)) _ h
    intro Ss Ss' hrtc
    let (S, s) := Ss
    let (S', s') := Ss'
    apply SmallStep.comp_step
    simp
    assumption

-- Algunos hints:
#print RTC.head
#print RTC.tail
#print RTC.single
#print RTC.trans
#print RTC_SmallStep_comp

/- ### Ejercicio 5 (2 pts.) -/

theorem RTC_SmallStep_of_BigStep {Ss t} (hS : Ss ⟹ t) :
  Ss ⇒* (Stmt.skip, t) :=
  by
    induction hS with
    | skip => exact RTC.refl
    | assign =>
      apply RTC.single
      apply SmallStep.assign
    | comp S T s t u hS hT ihS ihT =>
      apply RTC.trans
      . exact RTC_SmallStep_comp ihS
      . apply RTC.head
        apply SmallStep.comp_skip
        assumption
    | if_true B S T s t hB hst ih =>
      apply RTC.head
      . apply SmallStep.if_true
        assumption
      . assumption
    | if_false B S T s t hB hst ih =>
      apply RTC.head
      . apply SmallStep.if_false
        assumption
      . assumption
    | while_true B S s t u hB hS hw ihS ihw =>
      apply RTC.head
      . apply SmallStep.whileDo
      . apply RTC.head
        . apply SmallStep.if_true
          assumption
        . apply RTC.trans
          . exact RTC_SmallStep_comp ihS
          . apply RTC.head
            apply SmallStep.comp_skip
            assumption
    | while_false B S s hB =>
      apply RTC.tail
      apply RTC.single
      apply SmallStep.whileDo
      apply SmallStep.if_false
      assumption
    | for_false _ _ _ _ _ _ hassign hcond hassign_ih =>
      -- Demuestra el caso `for_false` borrando el `sorry`
      sorry
    | for_true _ _ _ _ _ _ _ _ hassign hcond hbody hrest hassign_ih hbody_ih hrest_ih =>
      -- Demuestra el caso `for_true` borrando el `sorry`
      sorry

/- ### Ejercicio 6 (2 pts.) -/

theorem BigStep_of_SmallStep_of_BigStep {Ss₀ Ss₁ s₂}
    (h₁ : Ss₀ ⇒ Ss₁) :
  Ss₁ ⟹ s₂ → Ss₀ ⟹ s₂ :=
  by
    induction h₁ generalizing s₂ with
    | assign x a s               => simp
    | comp_step S S' T s s' hS ih => aesop
    | comp_skip T s               => simp
    | if_true B S T s hB         => aesop
    | if_false B S T s hB        => aesop
    | whileDo B S s              => aesop
      -- Demuestra el caso `forDo` borrando el `sorry`
    | forDo x M N S s            => sorry

theorem BigStep_of_RTC_SmallStep {Ss t} :
  Ss ⇒* (Stmt.skip, t) → Ss ⟹ t :=
  by
    intro hS
    induction hS using RTC.head_induction_on with
    | refl =>
      apply BigStep.skip
    | head Ss Ss' hST hsmallT ih =>
      let (S', s') := Ss'
      apply BigStep_of_SmallStep_of_BigStep hST
      apply ih

theorem BigStep_Iff_RTC_SmallStep {Ss t} :
  Ss ⟹ t ↔ Ss ⇒* (Stmt.skip, t) :=
  Iff.intro RTC_SmallStep_of_BigStep BigStep_of_RTC_SmallStep

end SyV
