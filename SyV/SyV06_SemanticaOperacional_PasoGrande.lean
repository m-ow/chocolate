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


end SyV
