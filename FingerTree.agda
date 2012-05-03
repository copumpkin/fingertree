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

-- TODO: avoid full monoids and just use semigroups where possible


foldMap₁ : ∀ {n} {a b} {A : Set a} {B : Set b} → (B → B → B) → (A → B) → Vec A (1 + n) → B
foldMap₁ _∙_ f (x ∷ []) = f x
foldMap₁ _∙_ f (x ∷ x₁ ∷ xs) = f x ∙ foldMap₁ _∙_ f (x₁ ∷ xs)

module FoldMap₁ {b c} (S : Semigroup b c) where
  open Semigroup S renaming (Carrier to B)

  foldMap₁-cons : ∀ {n} {a} {A : Set a} (f : A → B) x (ys : Vec A (1 + n)) → f x ∙ foldMap₁ _∙_ f ys ≈ foldMap₁ _∙_ f (x ∷ ys)
  foldMap₁-cons f x (y ∷ []) = refl
  foldMap₁-cons f x (y ∷ y₁ ∷ ys) = refl

  foldMap₁-snoc : ∀ {n} {a} {A : Set a} (f : A → B) (xs : Vec A (1 + n)) y → foldMap₁ _∙_ f xs ∙ f y ≈ foldMap₁ _∙_ f (xs ∷ʳ y)
  foldMap₁-snoc f (x ∷ []) y = refl
  foldMap₁-snoc f (x ∷ x₁ ∷ xs) y = trans (assoc _ _ _) (∙-cong refl (foldMap₁-snoc f (x₁ ∷ xs) y))

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
    measure f (digit vec eq) = foldMap₁ _∙_ f vec

module Node (M : Monoid Level.zero Level.zero) where
  open Monoid M renaming (Carrier to V)

  record Node (A : Set) (f : A → V) : Set where
    constructor node
    field
      {n}     : ℕ
      m       : V
      vec     : Vec A (2 + n)
      n-good  : 2 + n ≤ 3
      .m-good : m ≈ foldMap₁ _∙_ f vec

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
  open FoldMap₁ (record { isSemigroup = isSemigroup })

  suc≰id : ∀ {n} → suc n ≤ n → ⊥
  suc≰id (s≤s s) = suc≰id s

  mutual
    _◂_ : {A : Set} {f : A → V} → A → FingerTree A f → FingerTree A f
    a ◂ Dummy.empty = Dummy.single a
    a ◂ Dummy.single b = deep (one a) empty (one b)
    a ◂ Dummy.deep m (digit {n} vec n-good) t r eq with compare n 3
    _◂_ {f = f} a (Dummy.deep m (digit vec n-good) t r eq) | tri< x ¬y ¬z = Dummy.deep (f a ∙ m) (digit (a ∷ vec) (s≤s x)) t r
           (begin
             f a ∙ m
           ≈⟨ ∙-cong refl eq ⟩
             f a ∙ (foldMap₁ _∙_ f vec ∙ measureTree t ∙ measureDigit f r)
           ≈⟨ solve 4 (λ a b c d → a ⊙ (b ⊙ c ⊙ d) ⊜ (a ⊙ b) ⊙ c ⊙ d) refl _ _ _ _ ⟩
             (f a ∙ foldMap₁ _∙_ f vec) ∙ measureTree t ∙ measureDigit f r
           ≈⟨ ∙-cong (∙-cong (foldMap₁-cons f a vec) refl) refl ⟩
             foldMap₁ _∙_ f (a ∷ vec) ∙ measureTree t ∙ measureDigit f r
           ∎)
    _◂_ {f = f} a (Dummy.deep m (digit (b ∷ vec) n-good) t r eq) | tri≈ ¬x PropEq.refl ¬z = Dummy.deep (f a ∙ m) (two a b) (node′ vec ◂ t) r
           (begin
             f a ∙ m
           ≈⟨ ∙-cong refl eq ⟩
             f a ∙ (foldMap₁ _∙_ f (b ∷ vec) ∙ measureTree t ∙ measureDigit f r)
           ≈⟨ ∙-cong refl (∙-cong (∙-cong (sym (foldMap₁-cons f b vec)) refl) refl) ⟩
             f a ∙ (f b ∙ foldMap₁ _∙_ f vec ∙ measureTree t ∙ measureDigit f r)
           ≈⟨ solve 5 (λ a b c d e → a ⊙ (b ⊙ c ⊙ d ⊙ e) ⊜ a ⊙ b ⊙ (c ⊙ d) ⊙ e) refl _ _ _ _ _ ⟩
             f a ∙ f b ∙ (foldMap₁ _∙_ f vec ∙ measureTree t) ∙ measureDigit f r
           ≈⟨ ∙-cong (∙-cong refl (sym (measureTree-◂ (node′ vec) t))) refl ⟩
             f a ∙ f b ∙ measureTree (node′ vec ◂ t) ∙ measureDigit f r
           ∎)
    a ◂ Dummy.deep m (digit vec n-good) t r eq | tri> ¬x ¬y z = ⊥-elim (suc≰id (≤-trans n-good z))

    .measureTree-◂ : {A : Set} {f : A → V} (a : A) (t : FingerTree A f) → measureTree (a ◂ t) ≈ f a ∙ measureTree t
    measureTree-◂ a Dummy.empty = sym (proj₂ identity _)
    measureTree-◂ a (Dummy.single x) = ∙-cong (proj₂ identity _) refl
    measureTree-◂ a (Dummy.deep m (digit {n} vec n-good) t r eq) with compare n 3
    measureTree-◂ a (Dummy.deep m (digit vec n-good) t r eq) | tri< x ¬y ¬z = refl
    measureTree-◂ a (Dummy.deep m (digit (b ∷ vec) n-good) t r eq) | tri≈ ¬x PropEq.refl ¬z = refl
    measureTree-◂ a (Dummy.deep m (digit vec n-good) t r eq) | tri> ¬x ¬y z = ⊥-elim (suc≰id (≤-trans n-good z))

  -- If I were really clever, I could probably unify this with the proof above. But It might be more complication than it's worth...
  mutual
    _▹_ : {A : Set} {f : A → V} → FingerTree A f → A → FingerTree A f
    Dummy.empty ▹ a = Dummy.single a
    Dummy.single a ▹ b = deep (one a) empty (one b)
    Dummy.deep m l t (digit {n} vec n-good) eq ▹ a with compare n 3
    _▹_ {f = f} (Dummy.deep m l t (digit vec n-good) eq) a | tri< x ¬y ¬z = Dummy.deep (m ∙ f a) l t (digit (vec ∷ʳ a) (s≤s x))
           (begin
             m ∙ f a
           ≈⟨ ∙-cong eq refl ⟩
             measureDigit f l ∙ measureTree t ∙ foldMap₁ _∙_ f vec ∙ f a
           ≈⟨ solve 4 (λ a b c d → a ⊙ b ⊙ c ⊙ d ⊜ a ⊙ b ⊙ (c ⊙ d)) refl _ _ _ _ ⟩
             measureDigit f l ∙ measureTree t ∙ (foldMap₁ _∙_ f vec ∙ f a)
           ≈⟨ ∙-cong refl (foldMap₁-snoc f vec a) ⟩
             measureDigit f l ∙ measureTree t ∙ foldMap₁ _∙_ f (vec ∷ʳ a)
           ∎)
    _▹_ {f = f} (Dummy.deep m l t (digit vec n-good) eq) a | tri≈ ¬x PropEq.refl ¬z with initLast vec
    _▹_ {f = f} (Dummy.deep m l t (digit .(ys ∷ʳ y) n-good) eq) a | tri≈ ¬x PropEq.refl ¬z | ys , y , PropEq.refl = Dummy.deep (m ∙ f a) l (t ▹ node′ ys) (two y a)
           (begin
             m ∙ f a
           ≈⟨ ∙-cong eq refl ⟩
             measureDigit f l ∙ measureTree t ∙ foldMap₁ _∙_ f (ys ∷ʳ y) ∙ f a
           ≈⟨ ∙-cong (∙-cong refl (sym (foldMap₁-snoc f ys y))) refl ⟩
             measureDigit f l ∙ measureTree t ∙ (foldMap₁ _∙_ f ys ∙ f y) ∙ f a
           ≈⟨ solve 5 (λ a b c d e → a ⊙ b ⊙ (c ⊙ d) ⊙ e ⊜ a ⊙ (b ⊙ c) ⊙ (d ⊙ e)) refl _ _ _ _ _ ⟩
             measureDigit f l ∙ (measureTree t ∙ foldMap₁ _∙_ f ys) ∙ (f y ∙ f a)
           ≈⟨ ∙-cong (∙-cong refl (measureTree-▹ t (node′ ys))) refl ⟩
             measureDigit f l ∙ measureTree (t ▹ node′ ys) ∙ (f y ∙ f a)
           ∎)
    Dummy.deep m l t (digit vec n-good) eq ▹ a | tri> ¬x ¬y z = ⊥-elim (suc≰id (≤-trans n-good z))

    .measureTree-▹ : {A : Set} {f : A → V} (t : FingerTree A f) (a : A) → measureTree t ∙ f a ≈ measureTree (t ▹ a) 
    measureTree-▹ Dummy.empty a = proj₁ identity _
    measureTree-▹ (Dummy.single x) a = ∙-cong (sym (proj₂ identity _)) refl
    measureTree-▹ (Dummy.deep m l t (digit {n} vec n-good) eq) a with compare n 3
    measureTree-▹ (Dummy.deep m l t (digit vec n-good) eq) a | tri< x ¬y ¬z = refl
    measureTree-▹ (Dummy.deep m l t (digit vec n-good) eq) a | tri≈ ¬x PropEq.refl ¬z with initLast vec
    measureTree-▹ (Dummy.deep m l t (digit .(ys ∷ʳ y) n-good) eq) a | tri≈ ¬x PropEq.refl ¬z | ys , y , PropEq.refl = refl
    measureTree-▹ (Dummy.deep m l t (digit vec n-good) eq) a | tri> ¬x ¬y z = ⊥-elim (suc≰id (≤-trans n-good z))

  -- This craziness is probably way more work than is needed considering we only ever go up to 12, but it feels 
  -- icky to write out all the cases manually :(
  ~div3 : ℕ → ℕ
  ~div3 0 = 1
  ~div3 1 = 1
  ~div3 2 = 2
  ~div3 (suc (suc (suc n))) = suc (~div3 n)

  ~div3≥1 : ∀ n → ~div3 n ≥ 1
  ~div3≥1 zero = s≤s z≤n
  ~div3≥1 (suc zero) = s≤s z≤n
  ~div3≥1 (suc (suc zero)) = s≤s z≤n
  ~div3≥1 (suc (suc (suc n))) = s≤s z≤n

  ~div3-monotonic : _≤_ =[ ~div3 ]⇒ _≤_
  ~div3-monotonic {j = j} z≤n = ~div3≥1 j
  ~div3-monotonic (s≤s {n = n} z≤n) = ~div3≥1 (suc n)
  ~div3-monotonic (s≤s (s≤s {n = zero} z≤n)) = s≤s (s≤s z≤n)
  ~div3-monotonic (s≤s (s≤s {n = suc n} z≤n)) = s≤s (~div3≥1 n)
  ~div3-monotonic (s≤s (s≤s (s≤s i≤j))) = s≤s (~div3-monotonic i≤j)

  splitNodes : ∀ {n} {A : Set} {f : A → V} → Vec A (2 + n) → Vec (Node A f) (~div3 n)
  splitNodes {0} (x ∷ x₁ ∷ _) = node2 x x₁ ∷ []
  splitNodes {1} (x ∷ x₁ ∷ x₂ ∷ _) = node3 x x₁ x₂ ∷ []
  splitNodes {2} (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ _) = node2 x x₁ ∷ node2 x₂ x₃ ∷ []
  splitNodes {suc (suc (suc n))} (x ∷ x₁ ∷ x₂ ∷ xs) = node3 x x₁ x₂ ∷ splitNodes xs

  append3 : ∀ {x y z} {A : Set} → Vec A (suc x) → Vec A y → Vec A (suc z) → Vec A (2 + x + y + z)
  append3 {x} {y} {z} xs ys zs = PropEq.subst (Vec _) 
                                   (S.solve 3 (λ a b c → (con 1 :+ a) :+ (b :+ (con 1 :+ c)) := con 2 :+ a :+ b :+ c) PropEq.refl x y z)
                                   {!xs ++ ys ++ zs!}
    where
    module S = SemiringSolver
    open S

  mutual
    appendTree : ∀ {n} {A : Set} {f : A → V} → n ≤ 4 → FingerTree A f → Vec A n → FingerTree A f → FingerTree A f
    appendTree pf Dummy.empty ys z = foldr _ _◂_ z ys
    appendTree pf x ys Dummy.empty = foldl _ _▹_ x ys
    appendTree pf (Dummy.single x) ys z = x ◂ foldr _ _◂_ z ys
    appendTree pf x ys (Dummy.single z) = foldl _ _▹_ x ys ▹ z
    appendTree pf (Dummy.deep m l x r eq) ys (Dummy.deep m′ l′ x′ r′ eq′) = deep l (addDigits pf x r ys l′ x′) r′

    addDigits : ∀ {n} {A : Set} {f : A → V} 
              → n ≤ 4
              → FingerTree (Node A f) measureNode → Digit A 
              → Vec A n
              → Digit A → FingerTree (Node A f) measureNode
              → FingerTree (Node A f) measureNode
    addDigits {n} pf x (digit vec (s≤s {n₁} n-good)) ys (digit {n₂} vec′ (s≤s n-good′)) z
      = appendTree (~div3-monotonic {n₁ + n + n₂} {10} ((n-good +-mono pf) +-mono n-good′)) x (splitNodes (append3 vec ys vec′)) z

  _▹◂_ : {A : Set} {f : A → V} → FingerTree A f → FingerTree A f → FingerTree A f
  x ▹◂ y = appendTree z≤n x [] y



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
