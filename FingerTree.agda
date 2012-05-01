module FingerTree where

import Level
open import Function
open import Algebra

open import Data.Empty
open import Data.Product hiding (map)
open import Data.Nat hiding (compare)
open import Data.Nat.Properties
open import Data.Vec renaming (map to mapVec)

open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR

import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_)

import MonoidSolver

open StrictTotalOrder strictTotalOrder using (compare)
open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans)

-- TODO: get rid of the foldr where foldr₁ (or left) would work
-- TODO: avoid all the mess that comes from all the cases of Digit and make it inductive
-- TODO: avoid full monoids and just use semigroups

module Digit where
  record Digit (A : Set) : Set where
    constructor digit
    field
      {n}    : ℕ
      vec    : Vec A (1 + n)
      n-good : 1 + n ≤ 4

  one : {A : Set} (a : A) → Digit A
  one a = digit (a ∷ []) (s≤s z≤n)

  two : {A : Set} (a b : A) → Digit A
  two a b = digit (a ∷ b ∷ []) (s≤s (s≤s z≤n))

  three : {A : Set} (a b c : A) → Digit A
  three a b c = digit (a ∷ b ∷ c ∷ []) (s≤s (s≤s (s≤s z≤n)))

  four : {A : Set} (a b c d : A) → Digit A
  four a b c d = digit (a ∷ b ∷ c ∷ d ∷ []) (s≤s (s≤s (s≤s (s≤s z≤n))))

  map : {A B : Set} → (A → B) → Digit A → Digit B
  map f (digit vec eq) = digit (mapVec f vec) eq

  module Measured (M : Monoid Level.zero Level.zero) where
    open Monoid M renaming (Carrier to V)

    measure : {A : Set} → (A → V) → Digit A → V
    measure f (digit vec eq) = foldr _ _∙_ ε (mapVec f vec)

module Node (M : Monoid Level.zero Level.zero) where
  open Monoid M renaming (Carrier to V)

  record Node (A : Set) (f : A → V) : Set where
    constructor node
    field
      {n}     : ℕ
      m       : V
      vec     : Vec A (2 + n)
      n-good  : 2 + n ≤ 3
      .m-good : m ≈ foldr _ _∙_ ε (mapVec f vec)

  node′ : ∀ {n} {A : Set} {f : A → V} (xs : Vec A (2 + n)) {pf : True ((2 + n) ≤? 3)} → Node A f
  node′ xs {pf} = node _ xs (toWitness pf) refl

  node2 : {A : Set} {f : A → V} (x y : A) → Node A f
  node2 x y = node _ (x ∷ y ∷ []) (s≤s (s≤s z≤n)) refl

  node3 : {A : Set} {f : A → V} (x y z : A) → Node A f
  node3 x y z = node _ (x ∷ y ∷ z ∷ []) (s≤s (s≤s (s≤s z≤n))) refl

  measure : {A : Set} {f : A → V} → Node A f → V
  measure = Node.m

  {-
  fastMap : {A B : Set} {f : A → V} {g : B → V} (h : A → B) → Node A f → Node B g
  fastMap h (Dummy.node2 m x y eq) = Dummy.node2 m (h x) (h y) {!!}
  fastMap h (Dummy.node3 m x y z eq) = Dummy.node3 m (h x) (h y) (h z) {!!}
  -}


module MapNode (M1 M2 : Monoid Level.zero Level.zero) where
  private
    module M1 = Monoid M1
    module M2 = Monoid M2
    module N1 = Node M1
    module N2 = Node M2

  map : {A B : Set} {f : A → M1.Carrier} {g : B → M2.Carrier} (h : A → B) → N1.Node A f → N2.Node B g
  map h (Node.node m (x ∷ x₁ ∷ []) n-good m-good) = Node.node _ (h x ∷ h x₁ ∷ []) n-good M2.refl
  map h (Node.node m (x ∷ x₁ ∷ x₂ ∷ []) n-good m-good) = Node.node _ (h x ∷ h x₁ ∷ h x₂ ∷ []) n-good M2.refl
  map h (Node.node m (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ vec) (s≤s (s≤s (s≤s ()))) m-good)


module Main (M : Monoid Level.zero Level.zero) where
  open Monoid M renaming (Carrier to V)

  open Digit
  open Digit.Measured M renaming (measure to measureDigit)
  open Node M renaming (measure to measureNode)

  private
    module Dummy where
      mutual
        data FingerTree (A : Set) (f : A → V) : Set where
          empty  : FingerTree A f
          single : (x : A) → FingerTree A f
          deep   : (m : V) (l : Digit A) (t : FingerTree (Node A f) measureNode) (r : Digit A)
                   .(eq : m ≈ measureDigit f l ∙ measureTree t ∙ measureDigit f r) → FingerTree A f

        measureTree : {A : Set} {f : A → V} → FingerTree A f → V
        measureTree empty = ε
        measureTree {f = f} (single x) = f x
        measureTree (deep m l t r eq) = m

  open Dummy public using (FingerTree; module FingerTree; measureTree)

  empty : {A : Set} {f : A → V} → FingerTree A f
  empty = Dummy.empty

  single : {A : Set} {f : A → V} (x : A) → FingerTree A f
  single = Dummy.single

  deep : {A : Set} {f : A → V} (l : Digit A) (t : FingerTree (Node A f) measureNode) (r : Digit A) → FingerTree A f
  deep l t r = Dummy.deep _ l t r refl -- yay, value inference!


  {-
  open Digit renaming (map to mapDigit)

  fastMap : {A B : Set} → (A → B) → FingerTree A {!!} → FingerTree B {!!}
  fastMap f Dummy.empty = Dummy.empty
  fastMap f (Dummy.single x) = Dummy.single (f x)
  fastMap f (Dummy.deep m l x r eq) = Dummy.deep m {!mapDigit f l!} {!!} {!!} {!!}
  -}

  open EqR (record { isEquivalence = isEquivalence })

  open MonoidSolver M

  suc≰id : ∀ {n} → suc n ≤ n → ⊥
  suc≰id (s≤s s) = suc≰id s

  mutual
    _◃_ : {A : Set} {f : A → V} → A → FingerTree A f → FingerTree A f
    a ◃ Dummy.empty = Dummy.single a
    a ◃ Dummy.single b = deep (one a) empty (one b)
    a ◃ Dummy.deep m (digit {n} vec n-good) t r eq with compare n 3
    _◃_ {f = f} a (Dummy.deep m (digit vec n-good) t r eq) | tri< x ¬y ¬z = Dummy.deep (f a ∙ m) (digit (a ∷ vec) (s≤s x)) t r
           (begin
             f a ∙ m
           ≈⟨ ∙-cong refl eq ⟩
             f a ∙ (foldr _ _∙_ ε (mapVec f vec) ∙ measureTree t ∙ measureDigit f r)
           ≈⟨ solve 4 (λ a b c d → a ⊙ (b ⊙ c ⊙ d) ⊜ (a ⊙ b) ⊙ c ⊙ d) refl _ _ _ _ ⟩
             (f a ∙ foldr _ _∙_ ε (mapVec f vec)) ∙ measureTree t ∙ measureDigit f r
           ≈⟨ refl ⟩
             foldr _ _∙_ ε  (mapVec f (a ∷ vec)) ∙ measureTree t ∙ measureDigit f r
           ∎)
    _◃_ {f = f} a (Dummy.deep m (digit (b ∷ vec) n-good) t r eq) | tri≈ ¬x PropEq.refl ¬z = Dummy.deep (f a ∙ m) (two a b) (node′ vec ◃ t) r {!!}
    a ◃ Dummy.deep m (digit vec n-good) t r eq | tri> ¬x ¬y z = ⊥-elim (suc≰id (≤-trans n-good z))

    .measureTree-◃ : {A : Set} {f : A → V} (a : A) (t : FingerTree A f) → measureTree (a ◃ t) ≈ f a ∙ measureTree t
    measureTree-◃ {f = f} a Dummy.empty = sym (proj₂ identity (f a))
    measureTree-◃ {f = f} a (Dummy.single x) = solve 2 (λ x₁ x₂ → x₁ ⊙ :0 ⊙ :0 ⊙ (x₂ ⊙ :0) ⊜ x₁ ⊙ x₂) refl _ _
    measureTree-◃ a (Dummy.deep m (digit {n} vec n-good) t r eq) with compare n 3
    measureTree-◃ a (Dummy.deep m (digit vec n-good) t r eq) | tri< x ¬y ¬z = refl
    measureTree-◃ a (Dummy.deep m (digit (b ∷ vec) n-good) t r eq) | tri≈ ¬x PropEq.refl ¬z = refl
    measureTree-◃ a (Dummy.deep m (digit vec n-good) t r eq) | tri> ¬x ¬y z = ⊥-elim (suc≰id (≤-trans n-good z))

{-
{-
module MapTree (M1 M2 : Monoid Level.zero Level.zero) where
  private
    module M1 = Monoid M1
    module M2 = Monoid M2
    module FT1 = Main M1
    module FT2 = Main M2
    open FT1 renaming (FingerTree to FT1)
    open FT2 renaming (FingerTree to FT2)

    open Digit renaming (map to mapDigit)
    open MapNode M1 M2 renaming (map to mapNode)

  map : {A B : Set} {f : A → M1.Carrier} {g : B → M2.Carrier} (h : A → B) → FT1 A f → FT2 B g
  map h FT1.FingerTree.empty = FT2.empty
  map h (FT1.FingerTree.single x) = FT2.single (h x)
  map h (FT1.FingerTree.deep m l t r eq) = FT2.deep (mapDigit h l) (map (mapNode h) t) (mapDigit h r)
-}
-}