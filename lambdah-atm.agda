-- A handler calculus with explicit answer types
-- and restricted answer-type modification

module LambdaH-ATM where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality

-- Types and effects
data VTy  : Set
data CTy : Set
data Eff    : Set

data VTy where
  Nat : VTy
  _⇒_ : VTy → CTy → VTy

infixr 3 _⇒_ 

data CTy where
  _!_  : VTy → Eff → CTy

infix 4 _!_

data Eff where
  ι    : Eff
  _⇒op_,_,_,_ : VTy → VTy → CTy → CTy → CTy → Eff

infix 5 _⇒op_,_,_,_

-- Type well-formedness
wfv : VTy → Set
wfc : CTy → Set
wfe : Eff → Set

wfv Nat = ⊤
wfv (A ⇒ C) = wfv A × wfc C

wfc (A ! ε) = wfv A × wfe ε

wfe ι = ⊤
wfe (A ⇒op B , C , D , E) =
  wfv A × wfv B × wfc C × wfc D × wfc E × (E ≡ C ⊎ E ≡ D)

-- Expressions
data Val  (var : VTy → Set) : VTy → Set
data Comp (var : VTy → Set) : CTy → Set

data Val var where
  Var : {A : VTy} → var A → wfv A → Val var A
  Abs : {A : VTy} {C : CTy} →
        (var A → Comp var C) → Val var (A ⇒ C)

data Comp var where
  Ret    : {A A' B' : VTy} {C D : CTy} →
           Val var A → Comp var (A ! A' ⇒op B' , C , D , C)
  App    : {A : VTy} {C : CTy} →
           Val var (A ⇒ C) → Val var A → Comp var C
  Let    : {A A' B B' : VTy} {C D E : CTy} →
           Comp var (A ! A' ⇒op B' , C , D , E) →
           (var A → Comp var (B ! A' ⇒op B' , C , D , C)) →
           Comp var (B ! A' ⇒op B' , C , D , E)
  Op     : {A B : VTy} {C D : CTy} →
           Val var A → Comp var (B ! A ⇒op B , C , D , D)
  Handle : {A A' B' : VTy} {C D E : CTy} →
           Comp var (A ! A' ⇒op B' , C , D , E) →
           (var A → Comp var C) →
           (var A' -> var (B' ⇒ C) → Comp var D) →
           Comp var E

-- CPS interpreter
〚_〛v : VTy → Set
〚_〛c : CTy → Set

〚 Nat 〛v = ℕ
〚 A ⇒ C 〛v = 〚 A 〛v → 〚 C 〛c

〚 A ! ι 〛c =
  (〚 A 〛v → ⊥) → ⊥
〚 A ! A' ⇒op B' , C , D , E 〛c =
  (〚 A 〛v → (〚 A' 〛v → (〚 B' 〛v → 〚 C 〛c) → 〚 D 〛c) → 〚 C 〛c) →
  (〚 A' 〛v → (〚 B' 〛v → 〚 C 〛c) → 〚 D 〛c) → 〚 E 〛c

cpsv : {A : VTy} → Val 〚_〛v A → 〚 A 〛v
cpsc : {C : CTy} → Comp 〚_〛v C → 〚 C 〛c

cpsv (Var x p) = x

cpsv (Abs f) = λ x → cpsc (f x)

cpsc (Ret v) = λ k → k (cpsv v)

cpsc (App v₁ v₂) = (cpsv v₁) (cpsv v₂)

cpsc (Let c₁ c₂) = λ k → (cpsc c₁) (λ v₁ → cpsc (c₂ v₁) k)

cpsc (Op v) =
  λ k → λ h → h (cpsv v) (λ x → k x h)
  
cpsc (Handle c cr ch) =
  (cpsc c) (λ x → λ h → cpsc (cr x)) (λ x → λ k → cpsc (ch x k))
