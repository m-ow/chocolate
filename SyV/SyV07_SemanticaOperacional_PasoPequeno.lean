/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import SyV.SyVPrelude
import SyV.SyV06_SemanticaOperacional_PasoGrande


/- # Clase 7: Semántica Operacional de Paso Pequeño -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace SyV


/- ## Semántica de Paso Pequeño

Una semántica de paso grande

* no nos permite razonar sobre estados intermedios;

* no nos permite expresar la no-terminación o el entrelazado de
  estados (al tener varios hilos).

La __semántica de paso pequeño__ (también llamada
__semántica operacional estructural__) resuelve los problemas
antes mencionados.

Un juicio tiene la forma `(S, s) ⇒ (T, t)`:

    Empezando en un estado `s`, al ejecutar un paso de `S` nos
    lleva al estado `t`, con el programa `T` aún por ejecutar.

Una ejecución es una cadena finita o infinita
`(S₀, s₀) ⇒ (S₁, s₁) ⇒ …`.

Un par `(S, s)` se llama una __configuración__. Decimos que es
__final__ si no es posible realizar una transición de la forma
`(S, s) ⇒ _`.

Ejemplo:

      `(x := x + y; y := 0, [x ↦ 3, y ↦ 5])`
    `⇒ (skip; y := 0,       [x ↦ 8, y ↦ 5])`
    `⇒ (y := 0,             [x ↦ 8, y ↦ 5])`
    `⇒ (skip,               [x ↦ 8, y ↦ 0])`

Reglas de derivación:

    ————————————————————————————————— Assign
    (x := a, s) ⇒ (skip, s[x ↦ s(a)])

    (S, s) ⇒ (S', s')
    ———-——————————————————— Comp-Step
    (S; T, s) ⇒ (S'; T, s')

    ————————————————————— Comp-Skip
    (skip; S, s) ⇒ (S, s)

    ———————————————————————————————— If-True   si s(B) es verdadero
    (if B then S else T, s) ⇒ (S, s)

    ———————————————————————————————— If-False   si s(B) es falso
    (if B then S else T, s) ⇒ (T, s)

    ——————————————————————————————————————————————————————————————— While
    (while B do S, s) ⇒ (if B then (S; while B do S) else skip, s)

No hay regla para `skip` (¿por qué?). -/

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

infixr:100 " ⇒ " => SmallStep
infixr:100 " ⇒* " => RTC SmallStep

#print RTC

#print RTC.head
#print RTC.refl

theorem sillyLoop_from_1_SmallStep :
  (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ⇒*
  (Stmt.skip, (fun _ ↦ 0)) :=
  by
    rw [sillyLoop]
    apply RTC.head
    . apply SmallStep.whileDo
    . apply RTC.head
      . apply SmallStep.if_true
        aesop
      . apply RTC.head
        . apply SmallStep.comp_step
          apply SmallStep.comp_skip
        . apply RTC.head
          . apply SmallStep.comp_step
            apply SmallStep.assign
          . apply RTC.head
            . apply SmallStep.comp_skip
            . apply RTC.head
              . apply SmallStep.whileDo
              . apply RTC.head
                . apply SmallStep.if_false
                  simp
                . simp
                  apply RTC.refl

/- Dada una semántica de paso pequeño, podemos **definir** una
semántica de paso grande:

    `(S, s) ⟹ t` si y sólo si `(S, s) ⇒* (skip, t)`

donde `r*` denota la cerradura reflexiva y transitiva de una
relación `r`.

De forma alternativa, si ya hemos definido una semántica de
paso grande, podemos **demostrar** el anterior teorema sobre
la equivalencia para validar nuestras definiciones.

La principal desventaja de la semántica de paso pequeño es que
ahora tenemos dos relaciones: `⇒` y `⇒*`; y razonar sobre ellas
tiende a ser más complicado.


## Propiedades de la semántica de Paso Pequeño

Podemos demostrar que una configuración `(S, s)` es final si y
sólo si `S = skip`. Esto asegura que no hemos olvidado una regla
de derivación. -/

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
        have hSs₁₂ :=
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

/- Podemos definir reglas de inversión también para la semántica
de paso pequeño. Aquí hay tres ejemplos: -/

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

/- ### Equivalencia entre la semántica de Paso Grande y Paso Pequeño

Un resultado importante es la conexión entre la semántica de paso
grande y paso pequeño:

    `(S, s) ⟹ t ↔ (S, s) ⇒* (Stmt.skip, t)`
-/

/- Ida de la demostración principal. -/
#print RTC.lift

-- Lema
theorem RTC_SmallStep_comp {S T s u}
  (h : (S, s) ⇒* (Stmt.skip, u)) :
  (S; T, s) ⇒* (Stmt.skip; T, u) :=
  by
    apply RTC.lift (fun Ss ↦ (Prod.fst Ss; T, Prod.snd Ss)) _ h
    intro Ss Ss' hrtc
    let (S, s) := Ss
    let (S', s') := Ss'
    apply SmallStep.comp_step
    assumption

#print RTC.single
#print RTC.tail

-- Teorema
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

/- Regreso de la demostración principal. -/

-- Lema
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

-- Teorema
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

-- Demostración Principal
theorem BigStep_Iff_RTC_SmallStep {Ss t} :
  Ss ⟹ t ↔ Ss ⇒* (Stmt.skip, t) :=
  Iff.intro RTC_SmallStep_of_BigStep BigStep_of_RTC_SmallStep

end SyV
