/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import SyV.SyVPrelude
import SyV.SyV06_SemanticaOperacional_PasoGrande


/- # Clase 9: Semántica Axiomática

Revisaremos una segunda forma de especificar la semántica de un
lenguaje de programación: semántica axiomática o lógica de Hoare.
Si la semántica operacional corresponde a un intérprete ideal,
la __semántica axiomáitca__ (también llamada __lógica de Hoare__)
corresponde a un "verificador". Esta semántica es particularmente
conveniente para razonar sobre programas concretos. -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace SyV


/- ## Ternas de Hoare

Los juicios básicos de la semántica axiomática se llaman
__ternas de Hoare__. Son de la forma:

    `{P} S {Q}`

donde `S` es un enunciado, y `P` y `Q` (llamados __pre-condición__ y
__post-condición__) son fórmulas lógicas sobre el estado de las
variables.

Se puede leer de la siguiente forma:

    Si `P` se satisface antes de que `S` sea ejecutado, y la
    ejecución termina con normalidad, `Q` se satisface al
    término.

Esto es un enunciado de __corrección parcial__: El programa es
correcto si termina normalmente (es decir, no hay errores durante
la ejecución, no hay ciclos infinitos o divergencia).

Todas las siguientes ternas de Hoare son válidas:

    `{True} b := 4 {b = 4}`
    `{a = 2} b := 2 * a {a = 2 ∧ b = 4}`
    `{b ≥ 5} b := b + 1 {b ≥ 6}`
    `{False} skip {b = 100}`
    `{True} while i ≠ 100 do i := i + 1 {i = 100}`


## Reglas de Hoare

El siguiente es el conjunto completo de reglas para razonar sobre
programas del lenguaje WHILE:

    ———————————— Skip
    {P} skip {P}

    ——————————————————— Assign
    {Q[a/x]} x := a {Q}

    {P} S {R}   {R} S' {Q}
    —————————————————————— Comp
    {P} S; S' {Q}

    {P ∧ B} S {Q}   {P ∧ ¬B} S' {Q}
    ——————————————————————————————— If
    {P} if B then S else S' {Q}

    {I ∧ B} S {I}
    ————————————————————————— While
    {I} while B do S {I ∧ ¬B}

    P' → P   {P} S {Q}   Q → Q'
    ——————————————————————————— Conseq
    {P'} S {Q'}

`Q[a/x]` denota `Q` con `x` reemplazado por `a`.

En la regla `While`, `I` es lo que se llama un __invariante__.

A excepción de `Conseq`, las reglas son dirigidas por la sintaxis:
al mirar el programa, se puede ver inmediatamente qué regla aplicar.

Ejemplos:

    —————————————————————— Assign   —————————————————————— Assign
    {a = 2} b := a {b = 2}          {b = 2} c := b {c = 2}
    —————————————————————————————————————————————————————— Comp
    {a = 2} b := a; c := b {c = 2}


                     —————————————————————— Assign
    x > 10 → x > 5   {x > 5} y := x {y > 5}   y > 5 → y > 0
    ——————————————————————————————————————————————————————— Conseq
    {x > 10} y := x {y > 0}

Se puede demostrar que varias de las __reglas derivadas__ son
correctas según las reglas estándar. Por ejemplo, se pueden derivar
reglas bidireccionales para `skip`, `:=` y `while`:

    P → Q
    ———————————— Skip'
    {P} skip {Q}

    P → Q[a/x]
    —————————————— Assign'
    {P} x := a {Q}

    {P ∧ B} S {P}   P ∧ ¬B → Q
    —————————————————————————— While'
    {P} while B do S {Q}


## Un acercamiento semántico a la lógica de Hoare

Lo que haremos es definir tripletas de Hoare de forma
**semántica** en Lean.

Utilizaremos predicados sobre los estados (`State → Prop`) para
representar pre y post-condiciones, siguiendo el siguiente estilo
de incrustación. -/

def PartialHoare (P : State → Prop) (S : Stmt) (Q : State → Prop)
  : Prop := ∀s t, P s → (S, s) ⟹ t → Q t

macro "{*" P:term " *} " "(" S:term ")" " {* " Q:term " *}" : term =>
  `(PartialHoare $P $S $Q)

namespace PartialHoare

theorem skip_intro {P} :
  {* P *} (Stmt.skip) {* P *} :=
  by
    rw [PartialHoare]
    intro s t hs hst
    cases hst
    assumption

theorem assign_intro (P) {x a} :
  {* fun s ↦ P (s[x ↦ a s]) *} (Stmt.assign x a) {* P *} :=
  by
    intro s t P' hst
    cases hst with
    | assign => assumption

theorem comp_intro {P Q R S T} (hS : {* P *} (S) {* Q *})
    (hT : {* Q *} (T) {* R *}) :
  {* P *} (S; T) {* R *} :=
  by
    intro s t hs hst
    cases hst with
    | comp _ _ _ u d hS' hT' =>
      apply hT
      { apply hS
        { exact hs }
        { assumption } }
      { assumption }

theorem if_intro {B P Q S T}
    (hS : {* fun s ↦ P s ∧ B s *} (S) {* Q *})
    (hT : {* fun s ↦ P s ∧ ¬ B s *} (T) {* Q *}) :
  {* P *} (Stmt.ifThenElse B S T) {* Q *} :=
  by
    intro s t hs hst
    cases hst with
    | if_true _ _ _ _ _ hB hS' =>
      apply hS
      exact And.intro hs hB
      assumption
    | if_false _ _ _ _ _ hB hT' =>
      apply hT
      exact And.intro hs hB
      assumption

theorem while_intro (P) {B S}
    (h : {* fun s ↦ P s ∧ B s *} (S) {* P *}) :
  {* P *} (Stmt.whileDo B S) {* fun s ↦ P s ∧ ¬ B s *} :=
  by
    intro s t hs hst
    generalize ws_eq : (Stmt.whileDo B S, s) = Ss
    rw [ws_eq] at hst
    induction hst generalizing s with
    | skip s'                       => cases ws_eq
    | assign x a s'                 => cases ws_eq
    | comp S T s' t' u hS hT ih      => cases ws_eq
    | if_true B S T s' t' hB hS ih  => cases ws_eq
    | if_false B S T s' t' hB hT ih => cases ws_eq
    | while_true B' S' s' t' u hB' hS hw ih_hS ih_hw =>
      cases ws_eq
      apply ih_hw
      { apply h
        { apply And.intro <;>
            assumption }
        { exact hS } }
      { rfl }
    | while_false B' S' s' hB'      =>
      cases ws_eq
      aesop

theorem consequence {P P' Q Q' S}
    (h : {* P *} (S) {* Q *}) (hp : ∀s, P' s → P s)
    (hq : ∀s, Q s → Q' s) :
  {* P' *} (S) {* Q' *} :=
  fix s t : State
  assume hs : P' s
  assume hst : (S, s) ⟹ t
  show Q' t from
    hq _ (h s t (hp s hs) hst)

theorem consequence_left (P') {P Q S}
    (h : {* P *} (S) {* Q *}) (hp : ∀s, P' s → P s) :
  {* P' *} (S) {* Q *} :=
  consequence h hp (by aesop)

theorem consequence_right (Q) {Q' P S}
    (h : {* P *} (S) {* Q *}) (hq : ∀s, Q s → Q' s) :
  {* P *} (S) {* Q' *} :=
  consequence h (by aesop) hq

theorem skip_intro' {P Q} (h : ∀s, P s → Q s) :
  {* P *} (Stmt.skip) {* Q *} :=
  consequence skip_intro h (by aesop)

theorem assign_intro' {P Q x a}
    (h : ∀s, P s → Q (s[x ↦ a s])):
  {* P *} (Stmt.assign x a) {* Q *} :=
  consequence (assign_intro Q) h (by aesop)

theorem comp_intro' {P Q R S T} (hT : {* Q *} (T) {* R *})
    (hS : {* P *} (S) {* Q *}) :
  {* P *} (S; T) {* R *} :=
  comp_intro hS hT

theorem while_intro' {B P Q S} (I)
    (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
    (hP : ∀s, P s → I s)
    (hQ : ∀s, ¬ B s → I s → Q s) :
  {* P *} (Stmt.whileDo B S) {* Q *} :=
  consequence (while_intro I hS) hP (by aesop)

theorem assign_intro_forward (P) {x a} :
  {* P *}
  (Stmt.assign x a)
  {* fun s ↦ ∃n₀, P (s[x ↦ n₀]) ∧ s x = a (s[x ↦ n₀]) *} :=
  by
    apply assign_intro'
    intro s hP
    apply Exists.intro (s x)
    simp [*]

theorem assign_intro_backward (Q) {x a} :
  {* fun s ↦ ∃n', Q (s[x ↦ n']) ∧ n' = a s *}
  (Stmt.assign x a)
  {* Q *} :=
  by
    apply assign_intro'
    intro s hP
    cases hP with
    | intro n' hQ => aesop

end PartialHoare


/- ## Primer Programa: Intercambio de Dos Variables -/

def SWAP : Stmt :=
  Stmt.assign "t" (fun s ↦ s "a");
  Stmt.assign "a" (fun s ↦ s "b");
  Stmt.assign "b" (fun s ↦ s "t")

theorem SWAP_correct (a₀ b₀ : ℕ) :
  {* fun s ↦ s "a" = a₀ ∧ s "b" = b₀ *}
  (SWAP)
  {* fun s ↦ s "a" = b₀ ∧ s "b" = a₀ *} :=
  by
    apply PartialHoare.comp_intro'
    apply PartialHoare.comp_intro'
    apply PartialHoare.assign_intro
    apply PartialHoare.assign_intro
    apply PartialHoare.assign_intro'
    aesop


/- ## Segundo Programa: Suma de Dos Números -/

def ADD : Stmt :=
  Stmt.whileDo (fun s ↦ s "n" ≠ 0)
    (Stmt.assign "n" (fun s ↦ s "n" - 1);
     Stmt.assign "m" (fun s ↦ s "m" + 1))

theorem ADD_correct (n₀ m₀ : ℕ) :
  {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *}
  (ADD)
  {* fun s ↦ s "n" = 0 ∧ s "m" = n₀ + m₀ *} :=
  PartialHoare.while_intro' (fun s ↦ s "n" + s "m" = n₀ + m₀)
    (by
      apply PartialHoare.comp_intro'
      { apply PartialHoare.assign_intro }
      { apply PartialHoare.assign_intro'
        aesop })
    (by aesop)
    (by aesop)

/- ¿Cómo se nos ocurrió este invariante? El invariante debe:

1. ser verdadera antes de ingresar al ciclo;

2. mantenerse verdadera después de cada iteración del ciclo si
   era verdad antes de la iteración;

3. ser suficientemente precisa para que implique la post-condición
   del ciclo.

El invariante `True` cumple 1 y 2, pero usualmente no cumple 3.
Igualmente, `False` cumple 2 y 3, pero usualmente no cumple 1.
Los invariantes adecuados usualmente son de la forma

__trabajo realizado__ + __trabajo por realizar__ = __resultado deseado__

donde `+` es un operador adecuado. Cuando ingresamos al ciclo,
el __trabajo realizado__ es usualmente `0`. Y cuando salimos del
ciclo, el __trabajo por realizar__ debería ser `0`.

Para el ciclo `ADD`:

* el __trabajo realizado__ es `m`;
* el __trabajo por realizar__ es `n`;
* el __resultado deseado__ es `n₀ + m₀`.


## Un Generador de Condiciones a Verificar

Los __generadores de condiciones a verificar__ (VCGs por sus
siglas en inglés) son programas que aplican reglas de Hoare
automáticamente, produciendo __condiciones a verificar__ que deben
ser demostradas por el usuario. El usuario normalmente va a proveer
el invariante adecuado para los ciclos, como una anotación en sus
programas.

Podemos utilizar la metaprogramación de Lean para definir un
VCG sencillo.

Cientos de herramientas para la verificación de programas se basan
en estos principios.

Los VCGs tipicamente trabajan hacia atrás desde la post-condición,
utilizando reglas de razonamiento hacia atrás (donde la
post-condición `Q` es arbitraria). Esto funciona correctamente
porque `Assign` es una regla que naturalmente se razona hacia atrás. -/

/- Esta definición sirve para anotar los ciclos `While` con
su invariante. -/
def Stmt.invWhileDo (I B : State → Prop) (S : Stmt) : Stmt :=
  Stmt.whileDo B S

namespace PartialHoare

theorem invWhile_intro {B I Q S}
    (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
    (hQ : ∀s, ¬ B s → I s → Q s) :
  {* I *} (Stmt.invWhileDo I B S) {* Q *} :=
  while_intro' I hS (by aesop) hQ

theorem invWhile_intro' {B I P Q S}
    (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
    (hP : ∀s, P s → I s) (hQ : ∀s, ¬ B s → I s → Q s) :
  {* P *} (Stmt.invWhileDo I B S) {* Q *} :=
  while_intro' I hS hP hQ

end PartialHoare

def matchPartialHoare : Expr → Option (Expr × Expr × Expr)
  | (Expr.app (Expr.app (Expr.app
       (Expr.const ``PartialHoare _) P) S) Q) =>
    Option.some (P, S, Q)
  | _ =>
    Option.none

def applyConstant (name : Name) : TacticM Unit :=
  do
    let cst ← mkConstWithFreshMVarLevels name
    liftMetaTactic (fun goal ↦ MVarId.apply goal cst)

partial def vcg : TacticM Unit :=
  do
    let goals ← getUnsolvedGoals
    if goals.length != 0 then
      let target ← getMainTarget
      match matchPartialHoare target with
      | Option.none           => return
      | Option.some (P, S, Q) =>
        if Expr.isAppOfArity S ``Stmt.skip 0 then
          if Expr.isMVar P then
            applyConstant ``PartialHoare.skip_intro
          else
            applyConstant ``PartialHoare.skip_intro'
        else if Expr.isAppOfArity S ``Stmt.assign 2 then
          if Expr.isMVar P then
            applyConstant ``PartialHoare.assign_intro
          else
            applyConstant ``PartialHoare.assign_intro'
        else if Expr.isAppOfArity S ``Stmt.comp 2 then
          andThenOnSubgoals
            (applyConstant ``PartialHoare.comp_intro') vcg
        else if Expr.isAppOfArity S ``Stmt.ifThenElse 3 then
          andThenOnSubgoals
            (applyConstant ``PartialHoare.if_intro) vcg
        else if Expr.isAppOfArity S ``Stmt.invWhileDo 3 then
          if Expr.isMVar P then
            andThenOnSubgoals
              (applyConstant ``PartialHoare.invWhile_intro) vcg
          else
            andThenOnSubgoals
              (applyConstant ``PartialHoare.invWhile_intro')
              vcg
        else
          failure

elab "vcg" : tactic =>
  vcg


/- ## Repasando el Segundo Programa: Suma de Dos Números -/

theorem ADD_correct_vcg (n₀ m₀ : ℕ) :
  {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *}
  (ADD)
  {* fun s ↦ s "n" = 0 ∧ s "m" = n₀ + m₀ *} :=
show {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *}
     (Stmt.invWhileDo (fun s ↦ s "n" + s "m" = n₀ + m₀)
        (fun s ↦ s "n" ≠ 0)
        (Stmt.assign "n" (fun s ↦ s "n" - 1);
         Stmt.assign "m" (fun s ↦ s "m" + 1)))
     {* fun s ↦ s "n" = 0 ∧ s "m" = n₀ + m₀ *} from
  by
    vcg <;> aesop

end SyV
