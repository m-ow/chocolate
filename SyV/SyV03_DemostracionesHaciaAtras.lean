/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import SyV.SyV02_ProgramasYTeoremas


/- # Clase 3: Demostraciones Hacia Atrás

Una __táctica__ opera sobre la meta de una demostración para probarla
o al crear nuevas sub-metas. Las tácticas son un mecanismo de pruebas
__hacia atrás__: Empiezan desde la meta y continúan hacia las
hipótesis y teoremas disponibles. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace SyV

namespace BackwardProofs


/- ## Modo Táctica

Sintaxis de las demostraciones por tácticas:

    by
      _tactic₁_
      …
      _tacticN_

La palabra reservada `by` le indica a Lean que la demostración es por
tácticas. -/

theorem fst_of_two_props :
  ∀a b : Prop, a → b → a :=
  by
    intro a b
    intro ha hb
    apply ha

/- Nótese que `a → b → a` se leé como `a → (b → a)`.

La proposiciones en Lean son términos de tipo `Prop`. `Prop` es un
tipo, al igual que `Nat` o `List Bool`. De hecho hay una
correspondencia cercana entre proposiciones y tipos, que será
explicada en la siguiente clase.


## Tácticas Básicas

`intro` mueve variables cuantificadas por `∀`, o los supuestos de
implicaciones `→`, desde la conclusión de la meta (después de `⊢`)
hacia las hipótesis de la meta (antes de `⊢`).

`apply` empareja la conclusión de la meta con la conclusión del
teorema especificado y agrega las hipótesis del teorema commo nuevas
sub-metas. -/

theorem fst_of_two_props_params (a b : Prop) (ha : a) (hb : b) :
  a :=
  by apply ha

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
  by
    intro ha
    apply hbc
    apply hab
    trivial

/- La demostración anterior paso por paso:

* Suponemos que tenemos una prueba de `a`.
* La meta es `c`, que podemos demostrar al probar `b` (con `hbc`).
* La meta es `b`, que podemos mostrar si probamos `a` (con `hab`).
* Ya sabemos que se sigue `a` (por `ha`).

Luego, `exact` empareja la conclusión de la meta con el teorema
especificado, cerrando la meta. Usualmente podemos usar `apply` en
tales situaciones, pero `exact` expresa mejor nuestra intención. -/

theorem fst_of_two_props_exact (a b : Prop) (ha : a) (hb : b) :
  a :=
  by exact ha

/- `assumption` encuentra una hipótesis en el contexto local que
coincide con la conclusión de la meta y lo aplica para probarla. -/

theorem fst_of_two_props_assumption (a b : Prop)
    (ha : a) (hb : b) :
  a :=
  by assumption

/- `rfl` prueba `l = r`, donde ambos lados son sintácticamente iguales
salvo cómputo. Por "cómputo" queremos decir: desdoblar definiciones,
β-reducción (la aplicación de `fun` a un argumento), `let`, y más. -/

theorem α_example {α β : Type} (f : α → β) :
  (fun x ↦ f x) = (fun y ↦ f y) :=
  by rfl

theorem β_example {α β : Type} (f : α → β) (a : α) :
  (fun x ↦ f x) a = f a :=
  by rfl

def double (n : ℕ) : ℕ :=
  n + n

theorem δ_example :
  double 5 = 5 + 5 :=
  by rfl

/- `let` introduce una definición con alcance local. Abajo, `n := 2`
existe únicamente en el alcance de la expresión `n + n`. -/

theorem ζ_example :
  (let n : ℕ := 2
   n + n) = 4 :=
  by rfl

theorem η_example {α β : Type} (f : α → β) :
  (fun x ↦ f x) = f :=
  by rfl

/- `(a, b)` es el par cuyo primer componente es `a` y cuyo segundo
componente es `b`. `Prod.fst` es la proyección que extrae al primer
componente de un par. -/

theorem ι_example {α β : Type} (a : α) (b : β) :
  Prod.fst (a, b) = a :=
  by rfl


/- ## Razonando sobre Conectivos Lógicos y Cuantificadores

Reglas de introducción: -/

#check True.intro
#check And.intro
#check Or.inl
#check Or.inr
#check Iff.intro
#check Exists.intro

/- Reglas de eliminación: -/

#check False.elim
#check And.left
#check And.right
#check Or.elim
#check Iff.mp
#check Iff.mpr
#check Exists.elim

/- Definición de `¬` y teoremas relacionados: -/

#print Not
#check Classical.em
#check Classical.byContradiction

/- No hay reglas explícitas para `Not` (`¬`) puesto que `¬ p` se
define como `p → False`. -/

theorem And_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab

/- La prueba de arriba explicada paso por paso:

* Supongamos que sabemos `a ∧ b`.
* La meta es `b ∧ a`.
* Mostramos `b`, que es posible si primero mostramos una conjunción
  con `b` a la derecha.
* Esto es posible, ya tenemos `a ∧ b`.
* Mostramos `a`, que es posible si primero mostramos una conjunción
  con `a` a la izquierda.
* Esto es posible, ya tenemos `a ∧ b`.

El combinador `{ … }` pone el foco en una sub-meta específica.
La táctica dentro debe mostrar por completo la sub-meta. En la
siguiente prueba, `{ … }` se utiliza para cada una de las dos
sub-metas para dar una mejor estructura a la demostración. -/

theorem And_swap_braces :
  ∀a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    { exact And.right hab }
    { exact And.left hab }

/- Nótese como arriba pasamos la hipótesis `hab` directamente a los
teoremas `And.right` y `And.left`, en vez de esperar a que las
hipótesis de los teoremas aparezcan como nuevas sub-metas. Este es
un pequeño paso hacia adelante en una prueba que es mayormente hacia
atrás. -/

opaque f : ℕ → ℕ

theorem f5_if (h : ∀n : ℕ, f n = n) :
  f 5 = 5 :=
  by exact h 5

theorem Or_swap (a b : Prop) :
  a ∨ b → b ∨ a :=
  by
    intro hab
    apply Or.elim hab
    { intro ha
      exact Or.inr ha }
    { intro hb
      exact Or.inl hb }

theorem modus_ponens (a b : Prop) :
  (a → b) → a → b :=
  by
    intro hab ha
    apply hab
    exact ha

theorem Not_Not_intro (a : Prop) :
  a → ¬¬ a :=
  by
    intro ha
    intro hna
    apply hna
    exact ha

theorem Exists_double_iden :
  ∃n : ℕ, double n = n :=
  by
    apply Exists.intro 0
    rfl


/- ## Razonando sobre la Igualdad -/

#check Eq.refl
#check Eq.symm
#check Eq.trans
#check Eq.subst

/- Las reglas de arriba se pueden usar directamente: -/

theorem Eq_trans_symm {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) :
  a = c :=
  by
    apply Eq.trans
    { exact hab }
    { apply Eq.symm
      exact hcb }

/- `rw` aplica una ecuación como una regla de reescritura de
izquierda a derecha, una sóla vez. Para aplicar una ecuación de
derecha a izquierda, usa sobre el nombre el prefijo `←`. -/

theorem Eq_trans_symm_rw {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) :
  a = c :=
  by
    rw [hab]
    rw [hcb]

/- `rw` puede expandir una definición. Abajo, `¬¬ a` se vuelve
`¬ a → False`, y `¬ a` se vuelve `a → False`. -/

theorem a_proof_of_negation (a : Prop) :
  a → ¬¬ a :=
  by
    rw [Not]
    rw [Not]
    intro ha
    intro hna
    apply hna
    exact ha

/- `simp` aplica un conjunto estándar de reglas de reescritura (el
__conjunto de simplificación__) de forma exhaustiva. El conjunto
puede extenderse utilizando el atributo `@[simp]`. Los teoremas
pueden agregarse temporalmente al conjunto de simplificación con la
sintaxis `simp [_theorem₁_, …, _theoremN_]`. -/

theorem cong_two_args_1p1 {α : Type} (a b c d : α)
    (g : α → α → ℕ → α) (hab : a = b) (hcd : c = d) :
  g a c (1 + 1) = g b d 2 :=
  by simp [hab, hcd]

/- `ac_rfl` es similar a `rfl`, pero puede deducir incluyendo las
leyes de asociatividad y conmutatividad del `+`, `*`, y otros
operadores binarios. -/

theorem abc_Eq_cba (a b c : ℕ) :
  a + b + c = c + b + a :=
  by ac_rfl


/- ## Tácticas de Limpieza

`clear` remueve variables o hipótesis sin utilizar.

`rename` cambia el nombre de una variable o hipótesis. -/

theorem cleanup_example (a b c : Prop) (ha : a) (hb : b)
    (hab : a → b) (hbc : b → c) :
  c :=
  by
    clear ha hab a
    apply hbc
    clear hbc c
    rename b => h
    exact h

end BackwardProofs

end SyV
