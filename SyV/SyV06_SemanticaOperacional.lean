/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import SyV.SyVPrelude


/- # Clase 6: Semántica Operacional -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace SyV


/- ## Lenguaje WHILE

Definimos un estado `s` como una función de nombres de variables
en valores (`String → ℕ`).

__WHILE__ es un lenguaje imperativo minimalista con la siguiente
gramática:

    S  ::=  skip                 -- no-operación
         |  x := a               -- asignaciones
         |  S; S                 -- composición secuencial
         |  if B then S else S   -- enunciado condicional
         |  while B do S         -- ciclo while

donde `S` es un enunciado (también llamado "comando" o "programa"),
`x` es una variable, `a` una expresión aritmética, y `B` una
expresión booleana. -/

#print State

inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → ℕ) → Stmt
  | comp       : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo    : (State → Prop) → Stmt → Stmt

infixr:90 "; " => Stmt.comp

/- En la gramática descartamos deliberadamente la sintaxis de las
expresiones aritméticas y booleanas. En Lean, tenemos 2 opciones:

* Podemos usar un tipo como `AExp` que vimos en la segunda clase
  y de forma similar para expresiones booleanas.

* Podemos decidir que una expresión aritmética sea simplemente una
  función que va de estados a números naturales (`State → ℕ`) y
  las expresiones booleanas son predicados
  (`State → Prop` o `State → Bool`).

Esto corresponde a la diferencia entre una incrustación profunda
y superficial (deep/shallow embedding).

* Un __deep embedding__ de alguna sintaxis (expresiones, fórmulas,
  programas, etc.) consiste en definir un árbol de sintaxis
  abstracta dentro del asistente de pruebas (como fue el caso
  de `AExp`) con su propia semántica (una función `eval`).

* Por otro lado, un __shallow embedding__ reutiliza los
  mecanismos correspondientes de la lógica (es decir, términos,
  funciones, tipos predicados).

Una incrustación profunda nos permite razonar sobre la sintaxis
(y su semántica). Una incrustación superficial es más ligera,
pues podemos usarla directamente, sin la necesidad de definir su
propia semántica.

En este caso utilizaremos una incrustación profunda para programas
(por ser el caso interesante), y una incrustación superficial para
asignaciones y expresiones booleanas (pues son la parte aburrida).

El programa

  while x > y do
    skip;
    x := x - 1

se modela como -/

def sillyLoop : Stmt :=
  Stmt.whileDo (fun s ↦ s "x" > s "y")
    (Stmt.skip;
     Stmt.assign "x" (fun s ↦ s "x" - 1))


/- ## Semántica de Paso Grande

Una __semántica operacional__ corresponde a una versión ideal
de un intérprete (especificada en un lenguaje al estilo Prolog).
Hay dos variantes principales:

* semántica de paso grande;

* semántica de paso pequeño.

En una __semántica de paso grande__ (también llamada
__semántica natural__), los juicios son de la forma `(S, s) ⟹ t`:

    A partir de un estado `s`, al ejecutar `S`
    terminamos en el estado `t`.

Ejemplo:

    `(x := x + y; y := 0, [x ↦ 3, y ↦ 5]) ⟹ [x ↦ 8, y ↦ 0]`

Reglas de derivación:

    ——————————————— Skip
    (skip, s) ⟹ s

    ——————————————————————————— Assign
    (x := a, s) ⟹ s[x ↦ s(a)]

    (S, s) ⟹ t   (T, t) ⟹ u
    ——————————————————————————— Comp
    (S; T, s) ⟹ u

    (S, s) ⟹ t
    ————————————————————————————— If-True   si s(B) es verdadero
    (if B then S else T, s) ⟹ t

    (T, s) ⟹ t
    ————————————————————————————— If-False   si s(B) es falso
    (if B then S else T, s) ⟹ t

    (S, s) ⟹ t   (while B do S, t) ⟹ u
    —————————————————————————————————————— While-True   si s(B) es verdadero
    (while B do S, s) ⟹ u

    ————————————————————————— While-False   si s(B) es falso
    (while B do S, s) ⟹ s

Arriba, `s(e)` denota el valor de la expresión `e` en el estado
`s` y `s[x ↦ s(e)]` denota el estado que es idéntico a `s`
excepto que la variable `x` está ligada al valor `s(e)`.

En Lean, los juicios corresponden a predicados inductivos, y las
reglas de derivación corresponden a las reglas de introducción
de predicados. Utilizando un predicado inductivo en vez de una
función recursiva nos permite lidiar con la no-terminación
(por ejemplo, un `while` divergente) y con el no-determinismo
(por ejemplo, en presencia de concurrencia). -/

inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
    BigStep (Stmt.skip, s) s
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

infix:110 " ⟹ " => BigStep

theorem sillyLoop_from_1_BigStep :
  (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ⟹ (fun _ ↦ 0) :=
  by
    rw [sillyLoop]
    apply BigStep.while_true
    . aesop
    . apply BigStep.comp
      . apply BigStep.skip
      . apply BigStep.assign
    . simp
      apply BigStep.while_false
      simp


/- ## Propiedades de la Semántica de Paso Grande

Dada una semántica de paso grande, podemos

* probar propiedades sobre el lenguaje de programación, como
  **demostrar la equivalencia** entre programas y **determinismo**;

* razonar sobre **programas concretos**, probando teoremas
  que relacionan estados finales `t` con estados iniciales `s`. -/

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


theorem BigStep_terminates {S s} :
  ∃t, (S, s) ⟹ t :=
  sorry   -- no demostrable

/- También podemos definir reglas de inversión para la semántica
de paso grande: -/

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
        apply Exists.intro
        apply And.intro <;>
          assumption
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
      apply Exists.intro Stmt.skip
      apply Exists.intro (s[x ↦ a s])
      apply SmallStep.assign
    | comp S T ihS ihT =>
      simp
      cases Classical.em (S = Stmt.skip) with
      | inl h =>
        rw [h]
        apply Exists.intro T
        apply Exists.intro s
        apply SmallStep.comp_skip
      | inr h =>
        simp [h] at ihS
        cases ihS with
        | intro S' hS₀ =>
          cases hS₀ with
          | intro s' hS =>
            apply Exists.intro (S'; T)
            apply Exists.intro s'
            apply SmallStep.comp_step
            assumption
    | ifThenElse B S T ihS ihT =>
      simp
      cases Classical.em (B s) with
      | inl h =>
        apply Exists.intro S
        apply Exists.intro s
        apply SmallStep.if_true
        assumption
      | inr h =>
        apply Exists.intro T
        apply Exists.intro s
        apply SmallStep.if_false
        assumption
    | whileDo B S ih =>
      simp
      apply Exists.intro
        (Stmt.ifThenElse B (S; Stmt.whileDo B S)
           Stmt.skip)
      apply Exists.intro s
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
        apply Exists.intro S'
        apply Exists.intro s'
        aesop
      | comp_skip =>
        apply Or.intro_right
        aesop
    . intro hor
      cases hor with
      | inl hex =>
        cases hex with
        | intro S' hex' =>
          cases hex' with
          | intro s' hand =>
            cases hand with
            | intro hS hUt =>
              rw [hUt]
              apply SmallStep.comp_step
              assumption
      | inr hand =>
        cases hand with
        | intro hS hUt =>
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
        cases hand with
        | intro hB hUs =>
          rw [hUs]
          apply SmallStep.if_true
          assumption
      | inr hand =>
        cases hand with
        | intro hB hUs =>
          rw [hUs]
          apply SmallStep.if_false
          assumption

end SyV
