module FingerTree where

import Level
open import Function
open import Algebra

open import Data.Product hiding (map)

import Relation.Binary.EqReasoning as EqR

import MonoidSolver

-- TODO: avoid all the mess that comes from all the cases of Digit and make it inductive
-- TODO: avoid full monoids and just use semigroups

module Digit where
  data Digit (A : Set) : Set where
    one   : (a : A) → Digit A
    two   : (a b : A) → Digit A
    three : (a b c : A) → Digit A
    four  : (a b c d : A) → Digit A

  map : {A B : Set} → (A → B) → Digit A → Digit B
  map f (one a) = one (f a)
  map f (two a b) = two (f a) (f b)
  map f (three a b c) = three (f a) (f b) (f c)
  map f (four a b c d) = four (f a) (f b) (f c) (f d)

  module Measured (M : Monoid Level.zero Level.zero) where
    open Monoid M renaming (Carrier to V)

    measure : {A : Set} → (A → V) → Digit A → V
    measure f (one a) = f a
    measure f (two a b) = f a ∙ f b
    measure f (three a b c) = f a ∙ f b ∙ f c
    measure f (four a b c d) = f a ∙ f b ∙ f c ∙ f d

module Node (M : Monoid Level.zero Level.zero) where
  open Monoid M renaming (Carrier to V)

  private
    module Dummy where
      data Node (A : Set) (f : A → V) : Set where
        node2 : (m : V) (x y : A) .(eq : m ≈ f x ∙ f y) → Node A f
        node3 : (m : V) (x y z : A) .(eq : m ≈ f x ∙ f y ∙ f z) → Node A f

  open Dummy public using (Node; module Node)
  
  node2 : {A : Set} {f : A → V} (x y : A) → Node A f
  node2 x y = Node.node2 _ x y refl

  node3 : {A : Set} {f : A → V} (x y z : A) → Node A f
  node3 x y z = Node.node3 _ x y z refl

  measure : {A : Set} {f : A → V} → Node A f → V
  measure (Node.node2 m x y eq) = m
  measure (Node.node3 m x y z eq) = m

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
  map h (N1.Node.node2 m x y eq) = N2.node2 (h x) (h y)
  map h (N1.Node.node3 m x y z eq) = N2.node3 (h x) (h y) (h z)

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

  mutual
    _◃_ : {A : Set} {f : A → V} → A → FingerTree A f → FingerTree A f
    a ◃ Dummy.empty = Dummy.single a
    a ◃ Dummy.single b = deep (one a) empty (one b)
    _◃_ {f = f} a (Dummy.deep m (one b) t r eq) = Dummy.deep (f a ∙ m) (two a b) t r 
           (begin 
           f a ∙ m                                                           ≈⟨ ∙-cong refl eq ⟩
           f a ∙ (f b ∙ measureTree t ∙ measureDigit f r)                     ≈⟨ solve 4
                                                                                 (λ x x₁ x₂ x₃ →
                                                                                    x ⊙ (x₁ ⊙ x₂ ⊙ x₃) ⊜ x ⊙ x₁ ⊙ x₂ ⊙ x₃)
                                                                                 refl _ _ _ _ ⟩
           f a ∙  f b ∙ measureTree t ∙ measureDigit f r                      ≈⟨ refl ⟩
           measureDigit f (two a b) ∙ measureTree t ∙ measureDigit f r        ∎)
    _◃_ {f = f} a (Dummy.deep m (two b c) t r eq) = Dummy.deep (f a ∙ m) (three a b c) t r 
           (begin
             f a ∙ m                                                           ≈⟨ ∙-cong refl eq ⟩
             f a ∙ (f b ∙ f c ∙ measureTree t ∙ measureDigit f r)               ≈⟨ solve 5 
                                                                                   (λ x x₁ x₂ x₃ x₄ →
                                                                                      x ⊙ (x₁ ⊙ x₂ ⊙ x₃ ⊙ x₄) ⊜ x ⊙ x₁ ⊙ x₂ ⊙ x₃ ⊙ x₄) 
                                                                                   refl _ _ _ _ _ ⟩
             f a ∙  f b ∙ f c ∙ measureTree t ∙ measureDigit f r                ≈⟨ refl ⟩
             measureDigit f (three a b c) ∙ measureTree t ∙ measureDigit f r   ∎)
    _◃_ {f = f} a (Dummy.deep m (three b c d) t r eq) = Dummy.deep (f a ∙ m) (four a b c d) t r
           (begin
             f a ∙ m                                                          ≈⟨ ∙-cong refl eq ⟩
             f a ∙ (f b ∙ f c ∙ f d ∙ measureTree t ∙ measureDigit f r)         ≈⟨ solve 6
                                                                                   (λ x x₁ x₂ x₃ x₄ x₅ →
                                                                                      x ⊙ (x₁ ⊙ x₂ ⊙ x₃ ⊙ x₄ ⊙ x₅) ⊜ x ⊙ x₁ ⊙ x₂ ⊙ x₃ ⊙ x₄ ⊙ x₅)
                                                                                  refl _ _ _ _ _ _ ⟩
             f a ∙  f b ∙ f c ∙ f d ∙ measureTree t ∙ measureDigit f r          ≈⟨ refl ⟩
             measureDigit f (four a b c d) ∙ measureTree t ∙ measureDigit f r  ∎)
    _◃_ {f = f} a (Dummy.deep m (four b c d e) t r eq) = Dummy.deep (f a ∙ m) (two a b) (node3 c d e ◃ t) r
           (begin
             f a ∙ m ≈⟨ ∙-cong refl eq ⟩
             f a ∙ (f b ∙ f c ∙ f d ∙ f e ∙ measureTree t ∙ measureDigit f r) ≈⟨ solve 7 
                                                                                (λ x x₁ x₂ x₃ x₄ x₅ x₆ →
                                                                                   x ⊙ (x₁ ⊙ x₂ ⊙ x₃ ⊙ x₄ ⊙ x₅ ⊙ x₆) ⊜ x ⊙ x₁ ⊙ (x₂ ⊙ x₃ ⊙ x₄ ⊙ x₅) ⊙ x₆)
                                                                                refl _ _ _ _ _ _ _ ⟩
             f a ∙ f b ∙ (f c ∙ f d ∙ f e ∙ measureTree t) ∙ measureDigit f r ≈⟨ refl ⟩
             f a ∙ f b ∙ (measureNode (node3 c d e) ∙ measureTree t) ∙ measureDigit f r ≈⟨ ∙-cong (∙-cong refl (sym (measureTree-◃ (node3 c d e) t))) refl ⟩
             f a ∙ f b ∙ measureTree (node3 c d e ◃ t) ∙ measureDigit f r ≈⟨ refl ⟩
             measureDigit f (two a b) ∙ measureTree (node3 c d e ◃ t) ∙ measureDigit f r ∎)

    .measureTree-◃ : {A : Set} {f : A → V} (a : A) (t : FingerTree A f) → measureTree (a ◃ t) ≈ f a ∙ measureTree t
    measureTree-◃ {f = f} a Dummy.empty = sym (proj₂ identity (f a))
    measureTree-◃ {f = f} a (Dummy.single x) = ∙-cong (proj₂ identity (f a)) refl
    measureTree-◃ {f = f} a (Dummy.deep m (one b) t r eq) = refl
    measureTree-◃ {f = f} a (Dummy.deep m (two b c) t r eq) = refl
    measureTree-◃ {f = f} a (Dummy.deep m (three b c d) t r eq) = refl
    measureTree-◃ {f = f} a (Dummy.deep m (four b c d e) t r eq) = refl

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