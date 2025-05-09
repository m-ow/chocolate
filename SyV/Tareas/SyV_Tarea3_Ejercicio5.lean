import SyV.SyVPrelude

set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace SyV

inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → ℕ) → Stmt
  | comp       : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo    : (State → Prop) → Stmt → Stmt
  -- Nueva instrucción `for`
  | forDo    : String → (State → ℕ) → (State → ℕ) → Stmt → Stmt

infixr:90 "; " => Stmt.comp

/- ## Semántica de Paso Grande -/

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
  -- Nueva regla para el caso `false` del `for`
  | for_false (x M N S s₀ s₁)
     (hassgn : BigStep (Stmt.assign x M, s₀) s₁)
     (hcond : ¬ ((fun s => s x ≤ N s) s₁)) :
    BigStep (Stmt.forDo x M N S, s₀) s₁
  -- Nueva regla para el caso `true` del `for`
  | for_true (x M N S s₀ s₁ s₂ s₃)
      (hassign : BigStep (Stmt.assign x M, s₀) s₁)
      (hcond : (fun s => s x ≤ N s) s₁)
      (hbody : BigStep (S, s₁) s₂)
      (hrest : BigStep (Stmt.forDo x (fun s ↦ (s x) + 1) N S, s₂) s₃) :
    BigStep (Stmt.forDo x M N S, s₀) s₃

infix:110 " ⟹ " => BigStep


def PartialHoare (P : State → Prop) (S : Stmt) (Q : State → Prop)
  : Prop := ∀s t, P s → (S, s) ⟹ t → Q t

macro "{*" P:term " *} " "(" S:term ")" " {* " Q:term " *}" : term =>
  `(PartialHoare $P $S $Q)

namespace PartialHoare

theorem for_intro (P I) {x M N S}
    (h1 : {* P *} (Stmt.assign x M) {* I *})
    (h2 : {* fun s ↦ I s ∧ (fun s => s x ≤ N s) s *} (S) {* I *}) :
  {* P *} (Stmt.forDo x M N S) {* fun s ↦ I s ∧ (fun s => s x > N s) s *} :=
  by
    intro s t hs hst
    generalize fs_eq : (Stmt.forDo x M N S, s) = Ss
    rw [fs_eq] at hst
    induction hst generalizing s with
    | skip => cases fs_eq
    | assign => cases fs_eq
    | comp => cases fs_eq
    | if_true => cases fs_eq
    | if_false => cases fs_eq
    | while_true => cases fs_eq
    | while_false => cases fs_eq
    | for_false => aesop
    | for_true =>
      cases fs_eq
      apply hrest_ih
      . exact hs
      -- Nos quedamos atascados en esta parte
      . sorry

end PartialHoare

end SyV
