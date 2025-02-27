/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import SyV.SyV02_ProgramasYTeoremas
import SyV.SyV04_DemostracionesHaciaAdelanteEInduccion


/- # Clase 5: Type Classes y Predicados Inductivos
-/


set_option autoImplicit false
set_option tactic.hygienic false

namespace SyV

namespace DependentTypes

/- ## El Principio PcT

La flecha `→` puede utilizarse como el símbolo de implicación o
como el constructor para el tipo función.
Este par de conceptos no sólo se ve igual en los símbolos, sino
que son exactamente lo mismo por el principio PcT:

* PcT = Proposiciones como Tipos;
* PcT = Pruebas como Términos.

## Tipos Dependientes

Los tipos dependientes son de las principales características
que dan a Lean su poder expresivo.

Supongamos que se tiene una función `elige` que toma un número
`n : ℕ` y retorna un número entre `0` y `n`. Conceptualmente,
`elige` tiene el siguiente tipo dependiente:

    `(n : ℕ) → {i : ℕ // i ≤ n}`

Podemos entender a este tipo como una familia `ℕ`-indexada,
donde el tipo de cada miembro depende del índice:

    `elige n : {i : ℕ // i ≤ n}`

Además, como ya sabemos, un tipo puede dependender de otro tipo,
por ejemplo, `List` (o `fun α ↦ List α`), y `fun α ↦ α → α`.

Un término puede depender de un tipo, por ejemplo,
`fun α ↦ fun (x : α) ↦ x` (una función identidad polimórfica).

Por supuesto, un término también puede depender de otro término
(como las funciones normales simples).

En general, diremos que un __tipo dependiente__ depende de un
término. Esto es a lo que nos referimos al decir que la teoría
de tipos simples no admite tipos dependientes. -/

inductive Vec (α : Type) : ℕ → Type where
  | nil                                : Vec α 0
  | cons (a : α) {n : ℕ} (v : Vec α n) : Vec α (n + 1)

#check Vec.nil
#check Vec.cons

#check Vec.cons True (Vec.cons False (Vec.nil))

end DependentTypes

namespace TypeClasses

/- ## Type Classes (Clases de Tipos)

Una __type class__ es una estructura para tipos que combina
constantes abstractas y sus propiedades. Un tipo puede ser
declarado como instancia de una type class al proveer una
definición concreta para sus constantes y las demostraciones
de que se adhiere a las propiedades declaradas.
Según el tipo, Lean puede obtener la instancia adecuada. -/

#print Inhabited

instance Nat.Inhabited : Inhabited ℕ :=
  { default := 0 }

instance List.Inhabited {α : Type} : Inhabited (List α) :=
  { default := [] }

#eval (Inhabited.default : ℕ)
#eval (Inhabited.default : List Int)

def head {α : Type} [Inhabited α] : List α → α
  | []     => Inhabited.default
  | x :: _ => x

#eval head ([] : List ℕ)

#print IsCommutative

instance IsCommutative_add : Std.Commutative add :=
  { comm := Induction.add_comm }

#print IsAssociative

theorem add_assoc (l m n : ℕ) :
  add (add l m) n = add l (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

instance IsAssociative_add : Std.Associative add :=
  { assoc := add_assoc }

theorem mul_add (l m n : ℕ) :
  mul l (add m n) = add (mul l m) (mul l n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih =>
      simp [add, mul, ih]
      -- Ahora podemos usar ac_rfl
      ac_rfl

end TypeClasses

namespace InductivePredicates

/- ## Predicados Inductivos

### Números Par

Es común para los matemáticos definir algo como "el conjunto
más pequeño que cumple ...". Por ejemplo:

    El conjunto `E` de números naturales pares se define
    como el conjunto más pequeño cerrado bajo las siguientes
    reglas:
    (1) `0 ∈ E` y
    (2) Para cada `k ∈ ℕ`, si `k ∈ E` entonces `k + 2 ∈ E`.

En Lean podemos definir el correspondiente predicado
"es par" de la siguiente manera: -/

inductive Even : ℕ → Prop where
  | zero    : Even 0
  | add_two : ∀k : ℕ, Even k → Even (k + 2)

/- Esto debe lucir familiar. Utilizamos antes la misma
sintaxis, excepto con `Type` en vez de `Prop`, para los
tipos inductivos.

El comando anterior introduce un nuevo predicado unario
`Even`, al igual que 2 constructores, `Even.zero` y
`Even.add_two`, que pueden ser utilizados para construir
términos de prueba. Gracias a la garantía de "no basura"
de las definiciones inductivas, `Even.zero` y `Even.add_two`
son las únicas formas de construir pruebas de `Even`.

Por el principio PcT, `Even` puede verse como un tipo
inductivo, mientras los valores son términos de prueba. -/

theorem Even_4 : Even 4 :=
  have Even_0 : Even 0 :=
    Even.zero
  have Even_2 : Even 2 :=
    Even.add_two _ Even_0
  show Even 4 from
    Even.add_two _ Even_2

/- ¿Por qué no simplemente definir `Even` como una
    función recursiva? -/

def evenRec : ℕ → Bool
  | 0     => true
  | 1     => false
  | k + 2 => evenRec k

/- Hay ventajas y desventajas para ambos estilos.

La versión recursiva requiere que especifiquemos un caso
de falsedad (1), y requiere que probemos (o hagamos evidente)
la terminación. Por otro lado, como es computacional,
funciona bien junto con `rfl`, `simp`, `#reduce`, y `#eval`.

La versión inductiva se considera más abstracta y elegante.
Cada regla se enuncia de forma independiente de las demás.

Otra forma de definir `Even` sería sin recursión: -/

def evenNonrec (k : ℕ) : Prop :=
  k % 2 = 0

/- Para algunos esta podría ser la definición más
satisfactoria. Pero la versión inductiva es conveniente e
intuitiva como un ejemplo para ilustrar definiciones
inductivas realistas. -/

/- ### Cerradura Reflexiva y Transitiva

Dada una relación `R`, podemos dar su cerradura reflexiva
y transitiva. Esto lo modelamos como un predicado binario
`Star R`. -/

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
where
  | base (a b : α)    : R a b → Star R a b
  | refl (a : α)      : Star R a a
  | trans (a b c : α) : Star R a b → Star R b c → Star R a c

/- La primera regla incrusta `R` en `Star R`.
La segunda regla brinda la cerradura reflexiva.
La tercera regla brinda la cerradura transitiva.

La definición es elegante, y eso se ve al intentar
implementarla como una función recursiva: -/

def starRec {α : Type} (R : α → α → Bool) :
  α → α → Bool :=
  sorry

/- ## Inducción sobre Reglas

Así como podemos hacer inducción sobre un término, podemos
también hacer inducción sobre un término de prueba.

Esto se llama __inducción sobre reglas__, porque la
inducción se realiza sobre las reglas inductivas (es decir,
sobre los constructores del término de prueba).
Gracias al principio PcT, esto funciona de la manera
esperada. -/

theorem mod_two_Eq_zero_of_Even (n : ℕ) (h : Even n) :
  n % 2 = 0 :=
  by
    induction h with
    | zero            => rfl
    | add_two k hk ih => simp [ih]


/- `cases` realiza un análisis de casos sobre el término
especificado. Esto da lugar a tantas sub-metas como hay
constructores en la definición del tipo. La táctica se
comporta igual que la táctica `induction` excepto en que
no produce una hipótesis inductiva. -/

#check linarith
#check Nat.ctor_eq_zero
#check Nat.succ_eq_add_one

theorem Not_Even_two_mul_add_one (m n : ℕ)
    (hm : m = 2 * n + 1) :
  ¬ Even m :=
  sorry

theorem Star_Star_Iff_Star {α : Type} (R : α → α → Prop)
    (a b : α) :
  Star (Star R) a b ↔ Star R a b :=
  sorry

#check funext
#check propext

@[simp] theorem Star_Star_Eq_Star {α : Type}
    (R : α → α → Prop) :
  Star (Star R) = Star R :=
  sorry

/- ### Palindromos -/

inductive Palindrome {α : Type} : List α → Prop where
  | nil : Palindrome []
  | single (x : α) : Palindrome [x]
  | sandwich (x : α) (xs : List α) (hxs : Palindrome xs) :
    Palindrome ([x] ++ xs ++ [x])

theorem Palindrome_aa {α : Type} (a : α) :
  Palindrome [a, a] :=
  Palindrome.sandwich a _ Palindrome.nil

theorem Palindrome_aba {α : Type} (a b : α) :
  Palindrome [a, b, a] :=
  Palindrome.sandwich a _ (Palindrome.single b)

theorem reverse_append {α : Type} :
  ∀xs ys : List α,
    reverse (xs ++ ys) = reverse ys ++ reverse xs :=
    sorry

theorem Palindrome_reverse {α : Type} (xs : List α)
    (hxs : Palindrome xs) :
  Palindrome (reverse xs) :=
  sorry

end InductivePredicates

end SyV
