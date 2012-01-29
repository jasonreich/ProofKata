{- Lets try locally nameless -}
module Sestoft where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.Vec using (Vec; map)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

update : ∀{A : Set} → (ℕ → A) → ℕ → A → ℕ → A
update f k v k' with k ≟ k'
update f k v .k | yes refl = v
update f k v k' | no  prf  = f k'

module Language (Free : Set) where
  data Var (n : ℕ) : Set where
    bnd : (v : Fin n) → Var n
    fre : (v : Free)  → Var n

  vmap : ∀{m n} → (Fin m → Fin n) → Var m → Var n
  vmap f (bnd v) = bnd (f v)
  vmap f (fre v) = fre v

  data Expr (n : ℕ) : Set where
    ƛ       : (x : Expr (suc n)) → Expr n
    _$_     : (x : Expr n) (v : Var n) → Expr n
    var     : (v : Var n) → Expr n
    lεt_ιn_ : ∀ (x : Expr (suc n)) (y : Expr (suc n)) → Expr n

  ⟨_⟩ : ∀{n} → Fin n → Expr n
  ⟨ i ⟩ = var (bnd i)

  Closed = Expr 0
  Open = Expr 1

  subst' : ∀ n → Var (suc n) → Free → Var n
  subst' n       (bnd v) ρ = test' n v
    where test' : ∀ m → Fin (suc m) → Var m
          test' zero zero = fre ρ
          test' zero (suc ())
          test' (suc m) zero = bnd zero
          test' (suc m) (suc i) = vmap suc (test' m i)
  subst' _       (fre v) ρ = fre v

  subst : ∀ n → Expr (suc n) → Free → Expr n
  subst n (ƛ x) ρ = ƛ (subst (suc n) x ρ)
  subst n (x $ v) ρ = subst n x ρ $ subst' n v ρ
  subst n (var v) ρ = var (subst' n v ρ)
  subst n (lεt x ιn y) ρ = lεt subst (suc n) x ρ ιn subst (suc n) y ρ

  _[_/0] = subst 0

module Launchbury where
  open Language ℕ

  record Context : Set where
    field
      nxt  : ℕ
      heap : ℕ → Closed

  _[_↦_] : Context → ℕ → Closed → Context
  Γ [ v ↦ x ] = record 
    { nxt  = Context.nxt Γ
    ; heap = update (Context.heap Γ) v x }

  _[*↦_] : Context → Closed → Context
  Γ [*↦ x ] = record 
    { nxt  = suc (Context.nxt Γ)
    ; heap = update (Context.heap Γ) (Context.nxt Γ) x }

  data ⟨_∶_⟩⇓⟨_∶_⟩ (Γ : Context) : Closed → Context → Closed → Set where
    lam : ∀{x} 
        → ⟨ Γ ∶ ƛ x ⟩⇓⟨ Γ ∶ ƛ x ⟩
    app : ∀{x v Δ y Θ z}
        → ⟨ Γ ∶ x ⟩⇓⟨ Δ ∶ ƛ y ⟩
        → ⟨ Δ ∶ y [ v /0] ⟩⇓⟨ Θ ∶ z ⟩
        → ⟨ Γ ∶ x $ fre v ⟩⇓⟨ Θ ∶ z ⟩
    var : ∀ {v Δ y}
        → ⟨ Γ ∶ Context.heap Γ v ⟩⇓⟨ Δ ∶ y ⟩
        → ⟨ Γ ∶ var (fre v) ⟩⇓⟨ Δ [ v ↦ y ] ∶ y ⟩
    lεt : ∀{x y Δ z}
        → let v = Context.nxt Γ in
          ⟨ Γ [*↦ x [ v /0] ] ∶ y [ v /0] ⟩⇓⟨ Δ ∶ z ⟩
        → ⟨ Γ ∶ lεt x ιn y ⟩⇓⟨ Δ ∶ z ⟩

module Mark1 where
  open Language ℕ

  open import Data.List using (List; []; _∷_)
  open import Data.Star using (Star; ε)

  data StckElem : Set where
    upd : ℕ → StckElem
    app : ℕ → StckElem

  Stack = List StckElem

  record State : Set where
    constructor ⟨_,_,_,_⟩
    field
      nxt  : ℕ
      heap : ℕ → Closed
      ctrl : Closed
      stck : Stack

  _[_↦_] = update {Closed}

  data _⇒_ : State → State → Set where
    app₁ : ∀{nxt Γ x v s}
         → ⟨ nxt , Γ , x $ fre v , s ⟩ 
                 ⇒ 
           ⟨ nxt , Γ , x , app v ∷ s ⟩
    app₂ : ∀{nxt Γ x v s}
         → ⟨ nxt , Γ , ƛ x , app v ∷ s ⟩ 
                 ⇒ 
           ⟨ nxt , Γ , x [ v /0] , s ⟩
    var₁ : ∀{nxt Γ v s}
         → ⟨ nxt , Γ , var (fre v) , s ⟩ 
                 ⇒ 
           ⟨ nxt , Γ , Γ v , upd v ∷ s ⟩
    var₂ : ∀{nxt Γ x v s}
         → ⟨ nxt , Γ , ƛ x , upd v ∷ s ⟩ 
                 ⇒ 
           ⟨ nxt , Γ [ v ↦ ƛ x ] , ƛ x , s ⟩
    lεt  : ∀{nxt Γ x y s}
         → ⟨ nxt , Γ , lεt x ιn y , s ⟩ 
                 ⇒ 
           ⟨ suc nxt , Γ [ nxt ↦ x [ nxt /0] ] , y [ nxt /0] , s ⟩

  _⇒*_ = Star _⇒_
  open Launchbury using (⟨_∶_⟩⇓⟨_∶_⟩; lam; app; var; lεt)
