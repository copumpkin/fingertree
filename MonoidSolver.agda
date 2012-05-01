------------------------------------------------------------------------
-- This module automates the process of producing equivalence proofs
-- on arbitrary Monoids using the Reflection module provided in Agda's
-- standard library.
--
-- Proofs involving associativity can be frustratingly mechanical, but this
-- module primarily serves as an introduction to the Reflection module.
--
-- For a more advanced use of the Reflection module, see Algebra.RingSolver
-- I have also implemented a Solver module for CommutativeMonoids.
--
-- What is a monoid?
-- A "Carrier" set of values
-- An equivalence _≈_
-- An associative, binary operation _∙_ which respects _≈_
-- An identity element ε
--
-- By the end of this module, we'll be able to automate proofs like:
-- ∀ a b c d → (a ∙ b) ∙ (c ∙ d) ≈ a ∙ (b ∙ c) ∙ d
------------------------------------------------------------------------

-- stolen from Eric Mertens's http://www.galois.com/~emertens/monoidsolver/MonoidSolver.html

open import Algebra using (Monoid; module Monoid)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; lookup)
open import Data.List using (List; _∷_; []; [_]; _++_; foldr)
open import Data.Product using (proj₁; proj₂)
open import Level using (Level)
import Relation.Binary.EqReasoning as Eq

module MonoidSolver {a ℓ : Level} (M : Monoid a ℓ) where

open Monoid M using (Carrier; _∙_; _≈_; ε; ∙-cong; assoc; identity; refl; setoid; sym)
open Eq setoid using (begin_; _≈⟨_⟩_; _∎)

-- The Syntax type allows us to reflect the shape of the proof
-- we wish to automate. We will "reflect" our goal into a Syntax
-- value and use this convert our proof obligation to a much
-- simpler one on normal forms. The 'n' is the number of unique
-- variables in the expression.

data Syntax (n : ℕ) : Set where
  _⊙_ : Syntax n → Syntax n → Syntax n
  var : Fin n → Syntax n
  :0 : Syntax n

infixl 7 _⊙_

-- This semantic evaluation function constructs a value
-- of Carrier which preserves the shape of the Syntax
-- tree. This is the shape of the proof we want to have.

⟦_⟧ : {n : ℕ} → Syntax n → Vec Carrier n → Carrier
⟦ x₁ ⊙ x₂ ⟧ ρ = ⟦ x₁ ⟧ ρ ∙ ⟦ x₂ ⟧ ρ
⟦ var i   ⟧ ρ = lookup i ρ
⟦ :0      ⟧ _ = ε

private
  flatten : {n : ℕ} → Syntax n → Vec Carrier n → List Carrier
  flatten (x₁ ⊙ x₂) ρ = flatten x₁ ρ ++ flatten x₂ ρ
  flatten (var i)   ρ = [ lookup i ρ ]
  flatten :0        _ = []

  sum : List Carrier → Carrier
  sum = foldr _∙_ ε

-- This normalized semantic evaluation function constructs a
-- value of Carrier which is semantically equivalent to the
-- one produced by ⟦_⟧, however all occurences of _∙_ are
-- made right-associative and all ε elements are eliminated.
-- This is the shape of the proof we want to provide.

⟦_⇓⟧ : {n : ℕ} → Syntax n → Vec Carrier n → Carrier
⟦ x ⇓⟧ ρ = sum (flatten x ρ)

private
  sum-++ : (xs ys : List Carrier) → sum (xs ++ ys) ≈ sum xs ∙ sum ys
  sum-++ []       ys = sym (proj₁ identity _)
  sum-++ (x ∷ xs) ys = begin
    x ∙  sum (xs ++ ys)   ≈⟨ ∙-cong refl (sum-++ xs ys) ⟩
    x ∙ (sum xs ∙ sum ys) ≈⟨ sym (assoc _ _ _) ⟩
    x ∙  sum xs ∙ sum ys  ∎

-- By proving that these two semantic evaluation functions produce
-- semantically equivalent values we'll be able to use equivalence
-- proofs about the normalized forms to talk about the equivalence
-- of the original values.

correct : {n : ℕ} (s : Syntax n) (ρ : Vec Carrier n) → ⟦ s ⇓⟧ ρ ≈ ⟦ s ⟧ ρ
correct :0        ρ = refl
correct (var i)   ρ = proj₂ identity (lookup i ρ)
correct (x₁ ⊙ x₂) ρ = begin
   ⟦ x₁      ⊙  x₂ ⇓⟧ ρ ≈⟨ sum-++ (flatten x₁ ρ) (flatten x₂ ρ) ⟩
   ⟦ x₁ ⇓⟧ ρ ∙ ⟦ x₂ ⇓⟧ ρ ≈⟨ ∙-cong (correct x₁ ρ) (correct x₂ ρ) ⟩
   ⟦ x₁  ⟧ ρ ∙ ⟦ x₂  ⟧ ρ ∎ 

import Relation.Binary.Reflection as R
open R setoid var ⟦_⟧ ⟦_⇓⟧ correct public using (prove; close; solve; solve₁; _⊜_)

private
  -- Now for a simple example
  Example = ∀ a b c d → (a ∙ b) ∙ (c ∙ d) ≈ a ∙ (b ∙ c) ∙ d

  -- A manual proof using equational reasoning looks like this.
  manual : Example
  manual a b c d = begin
    (a ∙ b) ∙ (c ∙ d) ≈⟨ sym (assoc (a ∙ b) c d) ⟩
     a ∙ b  ∙  c ∙ d  ≈⟨ ∙-cong (assoc a b c) refl ⟩
     a ∙ (b ∙ c) ∙ d  ∎

  -- Let's see the solver in action!
  automatic : Example
  automatic = solve 4 (λ a b c d → (a ⊙ b) ⊙ (c ⊙ d) ⊜ a ⊙ (b ⊙ c) ⊙ d) refl
                                -- ^ Here we reflect the shape of the proof we want