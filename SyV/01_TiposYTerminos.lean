/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import SyV.SyVPrelude


/- # Introducción

## Asistentes de Pruebas

Los asistentes de pruebas (también conocidos como "interactive theorem provers"):

* verifican y ayudan en el desarrollo de demostraciones formales;
* pueden ser utilizados para probar teoremas importantes, no sólo acertijos lógicos;
* pueden resultar tediosos de utilizar;
* son muy adictivos (igual que los videojuegos).

A selection of proof assistants, classified by logical foundations:
Los siguientes son asistentes de pruebas, clasificados según sus fundamentos lógicos:

* teoría de conjuntos: Isabelle/ZF, Metamath, Mizar;
* teoría de tipos simples: HOL4, HOL Light, Isabelle/HOL;
* **teoría de tipos dependientes**: Agda, Coq, **Lean**, Matita, PVS.


## Historias de éxito

Matemáticas:

* el teorema de los 4 colores (en Coq);
* la conjetura de Kepler (en HOL Light e Isabelle/HOL);
* la definición de los espacios perfectoides (en Lean).

Ciencias de la computación:

* hardware;
* sistemas operativos;
* teoría de lenguajes de programación;
* compiladores;
* seguridad.


## Lean

Lean es un lenguaje de programación y asistente de pruebas, desarrollado principalmente
por Leonardo de Moura (Amazon Web Services) desde el 2012.

Su biblioteca de matemáticas, `mathlib`, es desarrollada por una amplia comunidad
de contribuidores.

Utilizaremos la versión comunitaria de Lean 4. Utilizamos sus bibliotecas básicas,
`mathlib4` y `SyVPrelude`, entre otros. Lean es un projecto de investigación.

Fortalezas:

* una lógica sumamente expresiva basada en la teoría de tipos dependientes
  llamada el **cálculo de construcciones inductivas**;
* extendida con los axiomas de la lógica clásica y tipos cociente;
* un marco de trabajo para la metaprogramación;
* una interfaz de usuario moderna;
* documentación;
* de código abierto;
* y da lugar a muchas bromas (Lean Forward, Lean Together, BooLean, …).
* (Tal vez Coq gana en cuanto a las bromas)


## Nuestro objetivo

Esperamos que al finalizar el curso

* manejes con facilidad la teoría fundamental y las técnicas para las demostraciones
  interactivas;
* tengas familiaridad con su aplicación en algunas áreas;
* desarrolles algunas habilidad prácticas que puedas aplicar en proyectos más grandes
  (sea como un hobby, para una Maestría o Doctorado, o en la industria);
* te sientas con la preparación suficiente para probar otros asistentes de pruebas y
  aprendas lo aprendido.

Este curso no es un únicamente sobre fundamentos lógicos, ni un tutorial sobre Lean.
Lean es nuestra herramienta, no el objeto del curso.


# Clase 01: Tipos y Términos

Comenzamos nuestro viaje estudiando lo básico de Lean, comenzando con los
términos (expresiones) y sus tipos. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace SyV


/- ## Un vistazo de Lean

Como un primer acercamiento:

    Lean = programación funcional + lógica

A continuación veremos la sintaxis de los tipos y términos, que son similares a
aquellos del cálculo-λ con tipos simples, o lenguajes de programación funcionales
con tipos (ML, OCaml, Haskell).


## Tipos

Tipos `σ`, `τ`, `υ`:

* variables de tipos `α`;
* tipos básicos `T`;
* tipos complejos `T σ1 … σN`.

Algunos constructores de tipos `T` se escriben de forma infija, por
ejemplo `→` (tipo función).

La flecha funcional asocia a la derecha:
`σ₁ → σ₂ → σ₃ → τ` = `σ₁ → (σ₂ → (σ₃ → τ))`.

También podemos tener tipos polimórficos. En Lean, las variables de tipos deben
estar ligadas mediante `∀`, por ejemplo, `∀α, α → α`.


## Términos

Términos `t`, `u`:

* constantes `c`;
* variables `x`;
* aplicaciones `t u`;
* funciones anónimas `fun x ↦ t` (también llamadas λ-expresiones).

__Curryficación__: las funciones pueden estar

* completamente aplicadas (por ejemplo, `f x y z` si `f` toma a lo más 3 argumentos);
* parcialmente aplicadas (por ejemplo, `f x y`, `f x`);
* sin aplicar (por ejemplo, `f`).

La aplicación asocia a la izquierda: `f x y z` = `((f x) y) z`.

`#check` imprime el tipo de sus argumentos. -/

#check ℕ
#check ℤ

#check Empty
#check Unit
#check Bool

#check ℕ → ℤ
#check ℤ → ℕ
#check Bool → ℕ → ℤ
#check (Bool → ℕ) → ℤ
#check ℕ → (Bool → ℕ) → ℤ

#check fun x : ℕ ↦ x
#check fun f : ℕ → ℕ ↦ fun g : ℕ → ℕ ↦ fun h : ℕ → ℕ ↦
  fun x : ℕ ↦ h (g (f x))
#check fun (f g h : ℕ → ℕ) (x : ℕ) ↦ h (g (f x))

/- `opaque` defina una constante arbitraria del tipo especificado. -/

opaque a : ℤ
opaque b : ℤ
opaque f : ℤ → ℤ
opaque g : ℤ → ℤ → ℤ

#check fun x : ℤ ↦ g (f (g a x)) (g x b)
#check fun x ↦ g (f (g a x)) (g x b)

#check fun x ↦ x


/- ## Verificación de Tipos e Inferencia de Tipos

La verificación de tipos y la inferencia de tipos son problemas decidibles (aunque
esta propiedad se pierde al agregar características como sobrecarga o subtipos).

Juicio de tipo: `C ⊢ t : σ`, quiere decir que `t` tiene tipo `σ` en el contexto local `C`.

Reglas de tipificado:

    —————————— Cst   si c se declara globalmente con tipo σ
    C ⊢ c : σ

    —————————— Var   si x : σ es la ocurrencia más a la derecha de x en C
    C ⊢ x : σ

    C ⊢ t : σ → τ    C ⊢ u : σ
    ——————————————————————————— App
    C ⊢ t u : τ

    C, x : σ ⊢ t : τ
    ——————————————————————————— Fun
    C ⊢ (fun x : σ ↦ t) : σ → τ

Si la misma variable `x` ocurre en múltiples ocasiones en el contexto `C`, la
ocurrencia más a la derecha oculta a las demás.


## Habitación de Tipos

Dado un tipo `σ`, el problema de la __habitación de tipos__ consiste en encontrar
un término de tal tipo. La habitación de tipos es no decidible.

Procedimiento recursivo:

1. Si `σ` es de la forma `τ → υ`, un habitante candidato es la función anónima
   de la forma `fun x ↦ _`.

2. En otro caso, puedes utilizar cualquier constante o variable `x : τ₁ → ⋯ → τN → σ`
   para construir el término `x _ … _`. -/

opaque α : Type
opaque β : Type
opaque γ : Type

def someFunOfType : (α → β → γ) → ((β → α) → β) → α → γ :=
  fun f g a ↦ f a (g (fun b ↦ a))

/- ## Algunos ejercicios

Da las definiciones para términos cuyo tipo coincide con la firma dada. -/

def I : α → α :=
  sorry

def K : α → β → α :=
  sorry

def C : (α → β → γ) → β → α → γ :=
  sorry

def projFst : α → α → α :=
  sorry

/- Da una respuesta distinta a `projFst`. -/

def projSnd : α → α → α :=
  sorry

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  sorry

end SyV
