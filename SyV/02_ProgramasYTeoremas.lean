/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import SyV.SyVPrelude


/- # Clase 2: Programas y Teoremas -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace SyV


/- ## Definiciones de Tipos

Un __tipo inductivo__ (también conocido como __tipo de dato inductivo__,
__tipo de datos algebraico__, o simplemente __tipo de datos__) es un tipo que
consiste de todos los valores que pueden construirse usando un número finito de
aplicaciones de sus __constructores__, y nada más.


### Números Naturales -/

namespace MyNat

/- Definición del tipo `Nat` (= `ℕ`) para números naturales, utilizando notación unaria: -/

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

#check Nat
#check Nat.zero
#check Nat.succ

/- `#print` muestra la definición de su argumento. -/

#print Nat

end MyNat

/- Afuera del namespace `MyNat`, `Nat` se refiere al tipo definido en la
biblioteca estándar de Lean, a menos que lleve el prefijo `MyNat`. -/

#print Nat
#print MyNat.Nat

/- ### Expresiones Aritméticas -/

inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp


#check AExp.num 9
#check AExp.add (AExp.num 6) (AExp.var "x")

/- ### Listas -/

namespace MyList

inductive List (α : Type) where
  | nil  : List α
  | cons : α → List α → List α

#check List
#check List.nil
#check List.cons
#print List

end MyList

#print List
#print MyList.List


/- ## Definiciones de Funciones

La sintaxis para definir funciones que operan sobre un tipo de dato inductivo es
muy compacta: Definimos una única función y utilizamos __caza de patrones__ para
extraer el argumento del constructor. -/

def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

/- Cuando hay múltiples argumentos, se separan los patrones por `,`: -/

def add : ℕ → ℕ → ℕ
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)

/- `#eval` and `#reduce` evaluate and output the value of a term. -/

#eval add 2 7
#reduce add 2 7
#print add

def mul : ℕ → ℕ → ℕ
  | _, Nat.zero   => Nat.zero
  | m, Nat.succ n => add m (mul m n)

#eval mul 2 7

#print mul

def power : ℕ → ℕ → ℕ
  | _, Nat.zero   => 1
  | m, Nat.succ n => mul m (power m n)

#eval power 2 5

/- `add`, `mul`, y `power` son ejemplos artificiales. Estas operaciones ya se
encuentran disponibles en Lean como `+`, `*`, y `^`.

Si no es necesario hacer caza de patrones sobre un argumento, puede moverse
a la izquierda de `:` y volverse un argumento con nombre: -/

def powerParam (m : ℕ) : ℕ → ℕ
  | Nat.zero   => 1
  | Nat.succ n => mul m (powerParam m n)

#eval powerParam 2 5

def iter (α : Type) (z : α) (f : α → α) : ℕ → α
  | Nat.zero   => z
  | Nat.succ n => f (iter α z f n)

#check iter

def powerIter (m n : ℕ) : ℕ :=
  iter ℕ 1 (mul m) n

#eval powerIter 2 5

def addIter (m n : ℕ) : ℕ :=
  iter ℕ m Nat.succ n

#eval addIter 9 32

def append (α : Type) : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (append α xs ys)

/- Puesto que `append` debe funcionar para cualquier tipo de listas, el tipo
de sus elementos está dado como un argumento. Por ello, el tipo debe ser provisto
en cada llamada (o utilizar `_` si Lean puede inferir el tipo). -/

#check append
#eval append ℕ [3, 1] [4, 1, 5]
#check append ℕ [3, 1] [4, 1, 5]
#eval append _ [3, 1] [4, 1, 5]
#check append _ [3, 1] [4, 1, 5]

/- Si el argumento de tipo está entre `{ }` en vez de `( )`, el tipo es implícito
y no se necesita proveer en cada llamada (dado que Lean pueda inferirlo). -/

def appendImplicit {α : Type} : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (appendImplicit xs ys)

#eval appendImplicit [3, 1] [4, 1, 5]
#check appendImplicit [3, 1] [4, 1, 5]

/- Prefijar un nombre de definición con `@` da la definición correspondiente con
todos los argumentos implícitos como si fuera explícitos. Esto es útil en casos
donde Lean no puede instanciar por sí solo los argumentos implícitos. -/

#check @appendImplicit
#eval @appendImplicit ℕ [3, 1] [4, 1, 5]
#eval @appendImplicit _ [3, 1] [4, 1, 5]

/- Aliases:

    `[]`          := `List.nil`
    `x :: xs`     := `List.cons x xs`
    `[x₁, …, xN]` := `x₁ :: … :: xN :: []` -/

def appendPretty {α : Type} : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: appendPretty xs ys

def reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => reverse xs ++ [x]

def eval (env : String → ℤ) : AExp → ℤ
  | AExp.num i     => i
  | AExp.var x     => env x
  | AExp.add e₁ e₂ => eval env e₁ + eval env e₂
  | AExp.sub e₁ e₂ => eval env e₁ - eval env e₂
  | AExp.mul e₁ e₂ => eval env e₁ * eval env e₂
  | AExp.div e₁ e₂ => eval env e₁ / eval env e₂

#eval eval (fun x ↦ 7) (AExp.div (AExp.var "y") (AExp.num 2))

/- Lean únicamente acepta definiciones de funciones para las cuáles puede
probar que terminan. En particular, acepta funciones con __recursión estructural__,
que consiste en remover exactamente un constructor a la vez.


## Declaración de Teoremas

Nota la similaridad con los comandos `def`. `theorem` es como `def` excepto
que el resultado es una proposición en vez de un dato o una función. -/

namespace SorryTheorems

theorem add_comm (m n : ℕ) :
  add m n = add n m :=
  sorry

theorem add_assoc (l m n : ℕ) :
  (l + m) + n = l + (m + n) :=
  sorry

theorem mul_comm (m n : ℕ) :
  mul m n = mul n m :=
  sorry

theorem mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) :=
  sorry

theorem mul_add (l m n : ℕ) :
  mul l (add m n) = add (mul l m) (mul l n) :=
  sorry

theorem reverse_reverse {α : Type} (xs : List α) :
  reverse (reverse xs) = xs :=
  sorry

/- Los axiomas son como teoremas pero sin demostración. Las declaraciones
`opaque` son como definiciones pero sin cuerpo. -/

opaque a : ℤ
opaque b : ℤ

axiom a_less_b :
  a < b

end SorryTheorems

/- ## Ejercicio 1: Función Predecesor

Define la función `pred` con tipo `ℕ → ℕ` tal que devuelve el predecesor de
su argumento, o 0 si el argumento es 0. Por ejemplo:

    `pred 7 = 6`
    `pred 0 = 0` -/

def pred : ℕ → ℕ
  | Nat.zero => Nat.zero
  | Nat.succ n => n

/- Verifica que tu función se comporta como se espera. -/

#eval pred 0    -- expected: 0
#eval pred 1    -- expected: 0
#eval pred 2    -- expected: 1
#eval pred 3    -- expected: 2
#eval pred 10   -- expected: 9
#eval pred 99   -- expected: 98

/- ## Ejercicio 2: Map

Define una función genérica `map` que aplica una función a
cada elemento de una lista. -/

def map {α : Type} {β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: (map f xs)


#eval map (fun n ↦ n + 10) [1, 2, 3]   -- expected: [11, 12, 13]

/- Declara (sin dar la demostración) las que se conocen como
propiedades functoriales de `map` como teoremas. Esquemáticamente:

     map (fun x ↦ x) xs = xs
     map (fun x ↦ g (f x)) xs = map g (map f xs)

Intenta dar nombres descriptivos para tus teoremas. También, asegúrate de
declarar la segunda propiedad tan generalmente como sea posible, para tipos
arbitrarios. -/

theorem map_id_fun {α : Type} (xs : List α) :
  map (fun x ↦ x) xs = xs := sorry

theorem map_comp {α β γ : Type} (xs : List α) (f : α → β) (g : β → γ) :
   map (fun x ↦ g (f x)) xs = map g (map f xs) := sorry

end SyV
