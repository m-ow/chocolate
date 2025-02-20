/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import SyV.SyV02_ProgramasYTeoremas


/- # Clase 4: Inducción Matemática y Demostraciones Hacia Adelante
-/


set_option autoImplicit false
set_option tactic.hygienic false

namespace SyV

namespace ForwardProofs

/- ## Construcciones Estructuradas

Las pruebas estructuradas son azúcar sintáctica encima de los
__términos de prueba__ de Lean.

La forma más simple de demostración estructurada es simplemente
el nombre de un teorema, posiblemente con sus argumentos.

Como ejemplo: -/

-- Teorema Auxiliar

theorem add_comm (m n : ℕ) :
  add m n = add n m :=
  sorry

-- Demostración hacia adelante

theorem add_comm_zero_left (n : ℕ) :
  add 0 n = add n 0 :=
  add_comm 0 n

-- La demostración hacia atrás equivalente sería:

theorem add_comm_zero_left_by_exact (n : ℕ) :
  add 0 n = add n 0 :=
  by exact add_comm 0 n

/- `fix` y `assume` mueven las variables cuantificadas con `∀`
y suposiciones desde la meta hacia el contexto local.
Podemos ver estas como versiones estructuradas de la táctica
`intro`.

`show` repite la meta a demostrar. Esto es útil como documentación
o para reescribir la meta (a algo equivalente bajo cómputo). -/

theorem fst_of_two_props :
  ∀a b : Prop, a → b → a :=
  fix a b : Prop
  assume ha : a
  assume hb : b
  show a from
    ha

theorem fst_of_two_props_show (a b : Prop) (ha : a) (hb : b) :
  a :=
  show a from
    ha

theorem fst_of_two_props_no_show (a b : Prop) (ha : a) (hb : b) :
  a :=
  ha

/- `have` prueba un teorema intermedio, que puede referir el
contexto local. -/

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
  assume ha : a
  have hb : b :=
    hab ha
  have hc : c :=
    hbc hb
  show c from
    hc

theorem prop_comp_inline (a b c : Prop) (hab : a → b)
  (hbc : b → c) :
  a → c :=
  assume ha : a
  show c from
    hbc (hab ha)


/- ## Razonamiento Hacia Adelante sobre Conectivos y Cuantificadores -/

theorem And_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
  assume hab : a ∧ b
  have ha : a :=
    And.left hab
  have hb : b :=
    And.right hab
  show b ∧ a from
    And.intro hb ha

theorem or_swap (a b : Prop) :
  a ∨ b → b ∨ a :=
  assume hab : a ∨ b
  show b ∨ a from
    Or.elim hab
      (assume ha : a
       show b ∨ a from
         Or.inr ha)
      (assume hb : b
       show b ∨ a from
         Or.inl hb)

def double (n : ℕ) : ℕ :=
  n + n

theorem nat_exists_double_iden :
  ∃n : ℕ, double n = n :=
  Exists.intro 0
    (show double 0 = 0 from
     by rfl)

theorem not_not_intro (a : Prop) :
  a → ¬¬ a :=
  assume ha : a
  assume hna : ¬ a
  show False from
    hna ha

/- Así como puedes aplicar razonamiento hacia adelante dentro
de una prueba hacia atrás, puedes aplicar razonamiento hacia
atrás dentro de una prueba hacia adelante
(indicando el fragmento con `by`). -/

/- ## Demostraciones por Cálculo

En la práctica matemática, usualmente utilizamos cadenas de
igualdades transtivas, desigualdades, o equivalencias
(por ejemplo, `a ≥ b ≥ c`). En Lean, tales demostraciones
por cálculos se realizan con `calc`. -/

theorem two_mul_example (m n : ℕ) :
  2 * m + n = m + n + m :=
calc
  2 * m + n = m + m + n := by rw [Nat.two_mul]
          _ = m + n + m := by ac_rfl

/- `calc` evita algo de repetición, algunas etiquetas `have`,
y algunos argumentos de transitividad: -/

theorem two_mul_example_have (m n : ℕ) :
  2 * m + n = m + n + m :=
  have hmul : 2 * m + n = m + m + n :=
    by rw [Nat.two_mul]
  have hcomm : m + m + n = m + n + m :=
    by ac_rfl
  show _ from
    Eq.trans hmul hcomm


/- ## Razonamiento Hacia Adelante Con Tácticas

Los comandos de demostraciones estructuradas como `have`, `let` y
`calc` también están disponibles como tácticas. Incluso en modo
táctica, puede ser útil dar los resultados intermedios y
definiciones a manera de razonamiento hacia adelante. -/

theorem prop_comp_tactical (a b c : Prop) (hab : a → b)
  (hbc : b → c) :
  a → c :=
  by
    intro ha
    have hb : b :=
      hab ha
    let c' := c
    have hc : c' :=
      hbc hb
    exact hc

end ForwardProofs

namespace Induction

/- ## Demostraciones por Inducción Matemática

`induction` realiza inducción sobre una variable especificada.
Da lugar a una sub-meta con nombre por cada constructor. -/

theorem add_zero (n : ℕ) :
  add 0 n = n :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

theorem add_succ (m n : ℕ) :
  add (Nat.succ m) n = Nat.succ (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

theorem add_comm (m n : ℕ) :
  add m n = add n m :=
  by
    induction n with
    | zero       => simp [add, add_zero]
    | succ n' ih => simp [add, add_succ, ih]


/- ## Inducción por Emparejamiento de Patrones y Recursión

Una demostración por inducción es lo mismo que un término de
prueba dado recursivamente. Por ello, una alternativa a la táctica
`induction` es usar emparejamiento (o caza) de patrones y recursión:

* la hipótesis de inducción es el nombre del teorema que se
  está probando;

* la buena-fundación (o fundamentación [well-foundedness]) del
  argumento se demuestra automáticamente. -/

#check reverse

theorem reverse_append {α : Type} :
  ∀xs ys : List α,
    reverse (xs ++ ys) = reverse ys ++ reverse xs
  | [],      ys => by simp [reverse]
  | x :: xs, ys => by simp [reverse, reverse_append xs]

theorem reverse_append_tactical {α : Type} (xs ys : List α) :
  reverse (xs ++ ys) = reverse ys ++ reverse xs :=
  by
    induction xs with
    | nil           => simp [reverse]
    | cons x xs' ih => simp [reverse, ih]

theorem reverse_reverse {α : Type} :
  ∀xs : List α, reverse (reverse xs) = xs
  | []      => by rfl
  | x :: xs =>
    by simp [reverse, reverse_append, reverse_reverse xs]

end Induction

namespace InductiveTypes

/- ## Tipos Inductivos

Recordemos la definición del tipo `Nat`: -/

#print Nat

/- Mantras:

* **No basura**: El tipo no contiene valores más allá de aquellos
  que pueden expresarse utilizando los constructores.

* **No confusión**: Los valores construidos de formas distintas,
  son distintos.

Para `Nat`:

* "No basura" significa que no hay valores especiales, por
  ejemplo `–1` o `ε`, que no pueden ser expresados utilizando
  una combinación finita de `Nat.zero` y `Nat.succ`.

* "No confusión" es lo que asegura que `Nat.zero` ≠ `Nat.succ n`.

Además, los tipos inductivos siempre son finitos:
  `Nat.succ (Nat.succ …)` no es un valor.


## Inducción Estructural

La __Inducción estructural__ es una generalización de la inducción
matemática para tipos inductivos. Para probar una propiedad `P[m]`
sobre todos los números naturales, basta probar el caso base

    `P[0]`

y el paso inductivo

    `∀k, P[k] → P[k + 1]`

Para listas, el caso base es

    `P[[]]`

y el paso inductivo es

    `∀y ys, P[ys] → P[y :: ys]`

En general, hay una submeta por constructor, y la hipótesis
inductiva está disponible para todos los argumentos de constructores
del tipo sobre el que se está haciendo inducción. -/

theorem Nat.succ_neq_self (n : ℕ) :
  Nat.succ n ≠ n :=
by
  induction n with
  | zero       => simp
  | succ n' ih => simp [ih]


/- ## Recursión Estructural

La __Recursión Estructural__ es una forma de recursión que nos
permite ir desenvolviendo uno o más constructores del valor
sobre el cuál estamos haciendo recursión. Tales funciones tienen
la garantía de llamarse a sí mismas sólo una cantidad finita de
veces antes de que la recursión se detiene. Este es un prerequisito
para establecer que la función termina. -/

def fact : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * fact n

def factThreeCases : ℕ → ℕ
  | 0     => 1
  | 1     => 1
  | n + 1 => (n + 1) * factThreeCases n

/- Para funciones con recursión estructural, Lean puede probar en
automático que terminan. Para esquemas de recursión más generales,
la verificación de que termina puede fallar.
En algunos casos, es por una buena razón, como en este ejemplo: -/

/-
-- fails
def illegal : ℕ → ℕ
  | n => illegal n + 1
-/

/- ## Emparejamiento de Patrones sobre Expresiones

    `match` _term₁_, …, _termM_ `with`
    | _pattern₁₁_, …, _pattern₁M_ => _result₁_
        ⋮
    | _patternN₁_, …, _patternNM_ => _resultN_

`match` permite realizar emparejamiento de patrones no-recursivos
sobre términos. -/

def bcount {α : Type} (p : α → Bool) : List α → ℕ
  | []      => 0
  | x :: xs =>
    match p x with
    | true  => bcount p xs + 1
    | false => bcount p xs

def min (a b : ℕ) : ℕ :=
  if a ≤ b then a else b


/- ## Estructuras

Lean proveé una sintaxis conveniente para definir récords, o
estructuras. Estas son en esencia tipos inductivos no recursivos. -/

structure RGB where
  red   : ℕ
  green : ℕ
  blue  : ℕ

#check RGB.mk
#check RGB.red
#check RGB.green
#check RGB.blue

namespace RGB_as_inductive

/- La estructura RGB anterior es equivalente al siguiente
conjunto de definiciones: -/

inductive RGB : Type where
  | mk : ℕ → ℕ → ℕ → RGB

def RGB.red : RGB → ℕ
  | RGB.mk r _ _ => r

def RGB.green : RGB → ℕ
  | RGB.mk _ g _ => g

def RGB.blue : RGB → ℕ
  | RGB.mk _ _ b => b

end RGB_as_inductive

/- También podemos crear nuevas estructuras al extender otras
que ya existen: -/

structure RGBA extends RGB where
  alpha : ℕ

/- Un `RGBA` es un `RGB` con el campo extra `alpha : ℕ`. -/

#print RGBA

def pureRed : RGB :=
  RGB.mk 0xff 0x00 0x00

def pureGreen : RGB :=
  { red   := 0x00
    green := 0xff
    blue  := 0x00 }

def semitransparentGreen : RGBA :=
  { pureGreen with
    alpha := 0x7f }

#print pureRed
#print pureGreen
#print semitransparentGreen

def shuffle (c : RGB) : RGB :=
  { red   := RGB.green c
    green := RGB.blue c
    blue  := RGB.red c }

/- Definición alternativa utilizando emparejamiento de patrones: -/

def shufflePattern : RGB → RGB
  | RGB.mk r g b => RGB.mk g b r

theorem shuffle_shuffle_shuffle (c : RGB) :
  shuffle (shuffle (shuffle c)) = c :=
  by rfl

end InductiveTypes

end SyV
