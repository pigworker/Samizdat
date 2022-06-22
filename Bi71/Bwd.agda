module Bwd where

open import Basics

data Bwd (X : Set) : Set where
  []   : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

infixl 50 _-,_

Nat = Bwd One
