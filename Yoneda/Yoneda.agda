module Yoneda where

open import Category.Functor using (RawFunctor; module RawFunctor)
open import Function using (id; _∘_)
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- The Yoneda functor
Yoneda : ∀(F : Set → Set) (A : Set₁) → Set₁
Yoneda F A = ∀{R} → (A → R) → F R

-- Yes. It is definitely a functor.
ymap : ∀{F : Set → Set} {A B : Set₁} → (A → B) → Yoneda F A → Yoneda F B
ymap = λ f y k → y (k ∘ f)

law-ymap-id : ∀ {F : Set → Set} {A R} (f : Yoneda F A) (x : A → R) 
            → ymap id f x ≡ f x
law-ymap-id f x = refl

law-ymap-comp : ∀ {F : Set → Set} {A B C R} (f : Yoneda F A) (x : C → R) 
                (g : A → B) (h : B → C)
              → (ymap (h ∘ g) f) x ≡ (ymap h (ymap g f)) x
law-ymap-comp f g h x = refl

YonedaFunctor : ∀ F → RawFunctor (Yoneda F)
YonedaFunctor F = record { _<$>_ = ymap }

-- I can raise any functor up to a Yoneda wrapped functor
liftYoneda : ∀ {F A} → RawFunctor F → F A → Yoneda F (Lift A)
liftYoneda functor x f = f ∘ lift <$> x
  where open RawFunctor functor

-- I can extract any functor that is Yoneda wrapped
lowerYoneda : ∀ {F A} → Yoneda F (Lift A) → F A
lowerYoneda f = f lower

-- Mutual inverses
module Proofs {F : Set → Set} (functor : RawFunctor F) where
  _<$>f_ : ∀{A B : Set} → (A → B) → _ → _
  _<$>f_ = RawFunctor._<$>_ functor
  _<$>y_ : ∀{A B : Set₁} → (A → B) → _ → _
  _<$>y_ = RawFunctor._<$>_ (YonedaFunctor F)

  postulate
    -- Forgotten functor law but we're sure its right.
    fmap-id : ∀ {A : Set} (xs : F A) → id <$>f xs ≡ xs

  lift→lower : ∀ {A} (xs : F A) 
             → lowerYoneda (liftYoneda functor xs) ≡ xs
  lift→lower xs rewrite fmap-id xs = refl

  lower→lift : ∀ {A R : Set} (f : Yoneda F (Lift A)) (g : Lift A → R)
             → liftYoneda functor (lowerYoneda f) g ≡ f g
  lower→lift f g = {!!}