/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import SyV.SyVPrelude

/- # Clase 8: Ejercicios Extra -/

set_option autoImplicit false
set_option tactic.hygienic false

namespace DemostracionesHaciaAtras

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

theorem Peirce_of_EM : ExcludedMiddle → Peirce := sorry

theorem DN_of_Peirce : Peirce → DoubleNegation := sorry

theorem EM_of_DN : DoubleNegation → ExcludedMiddle := sorry

theorem Peirce_of_DN : DoubleNegation → Peirce := sorry

theorem EM_of_Peirce : Peirce → ExcludedMiddle := sorry

theorem DN_of_EM : ExcludedMiddle → DoubleNegation := sorry

end DemostracionesHaciaAtras



namespace Listas

#print List

def head {α : Type} [Inhabited α] : List α → α
  | []     => Inhabited.default
  | x :: _ => x

theorem head_head_cases {α : Type} [Inhabited α]
    (xs : List α) : head [head xs] = head xs := sorry

theorem head_head_match {α : Type} [Inhabited α]
    (xs : List α) : head [head xs] = head xs := sorry

theorem injection_example {α : Type} (x y : α) (xs ys : List α)
    (h : x :: xs = y :: ys) : x = y ∧ xs = ys := sorry

theorem distinctness_example {α : Type} (y : α) (ys : List α)
    (h : [] = y :: ys) : false := sorry

def map {α β : Type} (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: map f xs

def mapArgs {α β : Type} : (α → β) → List α → List β
  | _, []      => []
  | f, x :: xs => f x :: mapArgs f xs

#check List.map

theorem map_ident {α : Type} (xs : List α) :
  map (fun x ↦ x) xs = xs := sorry

theorem map_comp {α β γ : Type} (f : α → β) (g : β → γ) (xs : List α) :
  map g (map f xs) = map (fun x ↦ g (f x)) xs := sorry

theorem map_append {α β : Type} (f : α → β)
    (xs ys : List α) :
  map f (xs ++ ys) = map f xs ++ map f ys := sorry

end Listas



namespace Arboles

#print Tree

def Tree.map {α β : Type} (f : α → β) : Tree α → Tree β
  | Tree.nil => Tree.nil
  | Tree.node a l r => Tree.node (f a) (map f l) (map f r)

#check Tree

theorem Tree.map_eq_empty_iff {α β : Type} (f : α → β) :
  ∀t : Tree α, Tree.map f t = Tree.nil ↔ t = Tree.nil := sorry

def mirror {α : Type} : Tree α → Tree α
  | Tree.nil        => Tree.nil
  | Tree.node a l r => Tree.node a (mirror r) (mirror l)

theorem mirror_Eq_nil_Iff {α : Type} :
  ∀t : Tree α, mirror t = Tree.nil ↔ t = Tree.nil := sorry

inductive IsFull {α : Type} : Tree α → Prop where
  | nil : IsFull Tree.nil
  | node (a : α) (l r : Tree α)
      (hl : IsFull l) (hr : IsFull r)
      (hiff : l = Tree.nil ↔ r = Tree.nil) :
    IsFull (Tree.node a l r)

theorem IsFull_singleton {α : Type} (a : α) :
  IsFull (Tree.node a Tree.nil Tree.nil) := sorry

theorem IsFull_mirror {α : Type} (t : Tree α)
    (ht : IsFull t) : IsFull (mirror t) := sorry

theorem IsFull_mirror_struct_induct {α : Type} (t : Tree α) :
  IsFull t → IsFull (mirror t) := sorry

theorem map_mirror {α β : Type} (f : α → β) :
  ∀t : Tree α, IsFull t → IsFull (Tree.map f t) := sorry

end Arboles



namespace Regex

/- ## Regex

Se define un `Regex` mediante la siguiente gramática:

    R  ::=  ∅       -- `nothing`: empareja con nada
         |  ε       -- `empty`: empareja con la cadena vacía
         |  a       -- `atom`: empareja con el atómo `a`
         |  R ⬝ R    -- `concat`: empareja con la concatenación de dos regex
         |  R + R   -- `alt`: empareja alguno de los dos regex
         |  R*      -- `star`: empareja una cantidad arbitraria de repeticiones de un regex
-/

inductive Regex (α : Type) : Type
  | nothing : Regex α
  | empty   : Regex α
  | atom    : α → Regex α
  | concat  : Regex α → Regex α → Regex α
  | alt     : Regex α → Regex α → Regex α
  | star    : Regex α → Regex α

/- El predicado `Matches r s` indica que la expresión regular `r` se empareja
con la cadena `s` (una cadena es una lista de átomos). -/

inductive Matches {α : Type} : Regex α → List α → Prop
| empty :
  Matches Regex.empty []
| atom (a : α) :
  Matches (Regex.atom a) [a]
| concat (r₁ r₂ : Regex α) (s₁ s₂ : List α) (h₁ : Matches r₁ s₁)
    (h₂ : Matches r₂ s₂) :
  Matches (Regex.concat r₁ r₂) (s₁ ++ s₂)
| alt_left (r₁ r₂ : Regex α) (s : List α) (h : Matches r₁ s) :
  Matches (Regex.alt r₁ r₂) s
| alt_right (r₁ r₂ : Regex α) (s : List α) (h : Matches r₂ s) :
  Matches (Regex.alt r₁ r₂) s
| star_base (r : Regex α) :
  Matches (Regex.star r) []
| star_step (r : Regex α) (s s' : List α) (h₁ : Matches r s)
    (h₂ : Matches (Regex.star r) s') :
  Matches (Regex.star r) (s ++ s')

@[simp] theorem Matches_atom {α : Type} {s : List α} {a : α} :
  Matches (Regex.atom a) s ↔ s = [a] := sorry

@[simp] theorem Matches_nothing {α : Type} {s : List α} :
  ¬ Matches Regex.nothing s := sorry

@[simp] theorem Matches_empty {α : Type} {s : List α} :
  Matches Regex.empty s ↔ s = [] := sorry

@[simp] theorem Matches_concat {α : Type} {s : List α} {r₁ r₂ : Regex α} :
  Matches (Regex.concat r₁ r₂) s
  ↔ (∃s₁ s₂, Matches r₁ s₁ ∧ Matches r₂ s₂ ∧ s = s₁ ++ s₂) := sorry

@[simp] theorem Matches_alt {α : Type} {s : List α} {r₁ r₂ : Regex α} :
  Matches (Regex.alt r₁ r₂) s ↔ (Matches r₁ s ∨ Matches r₂ s) := sorry

theorem Matches_star {α : Type} {s : List α} {r : Regex α} :
  Matches (Regex.star r) s ↔
  (s = [] ∨ (∃s₁ s₂, Matches r s₁ ∧ Matches (Regex.star r) s₂ ∧ s = s₁ ++ s₂)) := sorry

end Regex
