module Interpreter where

open import Data.Char
open import Data.Bool
open import Data.Nat
import Data.Unit as U
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Nullary.Core
import Data.String as Str
open import Data.Nat.Show
import Data.List as List

infix 3 _:::_,_
infix 2 _∈_
infix 1 _⊢_

data `Set : Set where
  `Nat  : `Set
  `Bool : `Set
  `_⇨_  : `Set → `Set → `Set
  `Unit : `Set
  `_×_  : `Set → `Set → `Set
  `_+_  : `Set → `Set → `Set

#_ : `Set → Set
# `Nat = ℕ
# `Bool = Bool
# (` t ⇨ s) = # t → # s
# `Unit = U.Unit
# (` t × s) = # t × # s
# (` t + s) = # t ⊎ # s
 
data Γ : Set where
  ·         : Γ 
  _:::_,_   : Char → `Set → Γ → Γ 

data _∈_ :  Char → Γ → Set where
  H  : ∀ {x x′ Δ t } → {{eq : (x == x′) ≡ true}} → x ∈ x′ ::: t , Δ
  TH : ∀ {x y Δ t } → {{eq : (x == y) ≡ false}} → x ∈ Δ → x ∈ y ::: t , Δ

!Γ_[_] : ∀ {x} → (Δ : Γ) → x ∈ Δ → `Set
!Γ_[_] · ()
!Γ _ ::: t , Δ [ H ]     = t
!Γ _ ::: _ , Δ [ TH i ]  = !Γ Δ [ i ]

data _⊢_ : Γ → `Set → Set where
  `false           : ∀ {Δ} → Δ ⊢ `Bool
  `true            : ∀ {Δ} → Δ ⊢ `Bool
  `n_              : ∀ {Δ} → ℕ → Δ ⊢ `Nat
  ``_[_]           : ∀ {Δ} → (x : Char) → (i : x ∈ Δ) → Δ ⊢ !Γ Δ [ i ]
  `_₋_              : ∀ {Δ t s} → Δ ⊢ ` t ⇨ s → Δ ⊢ t → Δ ⊢ s
  `λ_`:_⇨_         : ∀ {Δ tr} → (x : Char) → (tx : `Set) 
                        → x ::: tx , Δ ⊢ tr → Δ ⊢ ` tx ⇨ tr
  `_+_             : ∀ {Δ} → Δ ⊢ `Nat → Δ ⊢ `Nat → Δ ⊢ `Nat
  `_*_             : ∀ {Δ} → Δ ⊢ `Nat →  Δ ⊢ `Nat → Δ ⊢ `Nat
  `_∧_             : ∀ {Δ} → Δ ⊢ `Bool → Δ ⊢ `Bool → Δ ⊢ `Bool
  `_∨_             : ∀ {Δ} → Δ ⊢ `Bool →  Δ ⊢ `Bool → Δ ⊢ `Bool
  `_≤_             : ∀ {Δ} → Δ ⊢ `Nat → Δ ⊢ `Nat →  Δ ⊢ `Bool
  `¬_              : ∀ {Δ} → Δ ⊢ `Bool →  Δ ⊢ `Bool 
  `_,_             : ∀ {Δ t s} → Δ ⊢ t →  Δ ⊢ s →  Δ ⊢ ` t × s
  `fst             : ∀ {Δ t s} → Δ ⊢ ` t × s → Δ ⊢ t
  `snd             : ∀ {Δ t s} → Δ ⊢ ` t × s → Δ ⊢ s
  `left            : ∀ {Δ t s} → Δ ⊢ t → Δ ⊢ ` t + s
  `right           : ∀ {Δ t s} → Δ ⊢ s → Δ ⊢ ` t + s
  `case_`of_||_    : ∀ {Δ t s u} → Δ ⊢ ` t + s 
                        → Δ ⊢ ` t ⇨ u → Δ ⊢ ` s ⇨ u → Δ ⊢ u
  `tt              : ∀ {Δ} → Δ ⊢ `Unit
  `let_`=_`in_     : ∀ {Δ th tb} → (x : Char) 
                       → Δ ⊢ th → x ::: th , Δ ⊢ tb → Δ ⊢ tb
  `if_`then_`else_ : ∀ {Δ t} → Δ ⊢ `Bool → Δ ⊢ t → Δ ⊢ t → Δ ⊢ t

data ⟨_⟩ : Γ → Set₁ where
  []   : ⟨ · ⟩
  _∷_  : ∀ {x t Δ} → # t → ⟨ Δ ⟩ → ⟨ x ::: t , Δ ⟩

!_[_] : ∀ {x Δ} → ⟨ Δ ⟩ → (i : x ∈ Δ) → # !Γ Δ [ i ]
!_[_] [] ()
!_[_] (val ∷ env) H      = val
!_[_] (val ∷ env) (TH i) = ! env [ i ]

interpret : ∀ {t} → · ⊢ t → # t
interpret = interpret' []
  where interpret' : ∀ {Δ t} → ⟨ Δ ⟩ → Δ ⊢ t → # t
        interpret' env `true = true
        interpret' env `false = false
        interpret' env `tt = U.unit
        interpret' env (`n n) = n
        interpret' env `` x [ idx ] = ! env [ idx ]
        interpret' env (` f ₋ x) = (interpret' env f) (interpret' env x)
        interpret' env (`λ _ `: tx ⇨ body) = λ (x : # tx) → interpret' (x ∷ env) body
        interpret' env (` l + r) = interpret' env l + interpret' env r
        interpret' env (` l * r) = interpret' env l * interpret' env r
        interpret' env (` l ∧ r) = interpret' env l ∧ interpret' env r
        interpret' env (` l ∨ r) = interpret' env l ∨ interpret' env r
        interpret' env (` l ≤ r) with interpret' env l ≤? interpret' env r 
        interpret' env (` l ≤ r) | yes p = true
        interpret' env (` l ≤ r) | no ¬p = false
        interpret' env (`¬ x) = not (interpret' env x)
        interpret' env (` f , s) = interpret' env f ,′ interpret' env s
        interpret' env (`fst p) with interpret' env p
        interpret' env (`fst p) | f , s = f
        interpret' env (`snd p) with interpret' env p
        interpret' env (`snd p) | f , s = s
        interpret' env (`left v) = inj₁ (interpret' env v)
        interpret' env (`right v) = inj₂ (interpret' env v)
        interpret' env (`case s `of le || re) with interpret' env s
        interpret' env (`case s `of le || re) | inj₁ l = (interpret' env le) l
        interpret' env (`case s `of le || re) | inj₂ r = (interpret' env re) r
        interpret' env (`let _ `= h `in b) = let hval = interpret' env h in interpret' (hval ∷ env) b
        interpret' env (`if b `then et `else ef) with interpret' env b
        interpret' env (`if b `then et `else ef) | true = interpret' env et
        interpret' env (`if b `then et `else ef) | false = interpret' env ef

testSimpleLambda : · ⊢ `Nat
testSimpleLambda = ` (`λ 'x' `: `Nat ⇨ ` `` 'x' [ H ] + `` 'x' [ H ]) ₋ `n 10

testNestedLambda : · ⊢ `Nat
testNestedLambda = ` ` (`λ 'x' `: `Nat ⇨ (`λ 'y' `: `Nat ⇨ ` `` 'x' [ TH H ] * `` 'y' [ H ])) ₋ `n 10 ₋ `n 15

-- Should not work because the inner x is not bound to a boolean, and it should not be possible to refer to the outside x using Elem
--testNamingNotWorking : · ⊢ `Bool
--testNamingNotWorking = ` ` `λ 'x' `: `Bool ⇨ (`λ 'x' `: `Unit ⇨ `` 'x' [ {!!} ]) ₋ `true ₋ `tt

testNamingWorking : · ⊢ `Unit
testNamingWorking = ` ` `λ 'x' `: `Bool ⇨ (`λ 'x' `: `Unit ⇨ `` 'x' [ H ]) ₋ `true ₋ `tt

testSum1 : · ⊢ `Nat
testSum1 = `let 'n' `= `case `left (`n 10) `of 
                              `λ 'n' `: `Nat ⇨ `` 'n' [ H ]
                           || `λ 'b' `: `Bool ⇨ `if `` 'b' [ H ] `then `n 1 `else `n 0 
           `in `` 'n' [ H ]  

testSum2 : · ⊢ `Nat
testSum2 = `let 'n' `= `case `right `true `of
                              `λ 'n' `: `Nat ⇨ `` 'n' [ H ]
                           || `λ 'b' `: `Bool ⇨ `if `` 'b' [ H ] `then `n 1 `else `n 0
           `in `` 'n' [ H ]  

testProduct1 : · ⊢ `Bool
testProduct1 = `fst (` `true , (` `n 10 , `tt ))

testProduct2 : · ⊢ ` `Nat × `Unit
testProduct2 = `snd (` `true , (` `n 10 , `tt ))

testDeMorganFullOr : · ⊢ `Bool
testDeMorganFullOr = `let 's' `= `λ 'x' `: `Bool ⇨ `λ 'y' `: `Bool ⇨ `¬ (` `` 'x' [ TH H ] ∨ `` 'y' [ H ])
                     `in ` ` `` 's' [ H ] ₋ `true ₋ `true
testDeMorganBrokenAnd : · ⊢ `Bool
testDeMorganBrokenAnd = `let 's' `= `λ 'x' `: `Bool ⇨ `λ 'y' `: `Bool ⇨ ` `¬ `` 'x' [ TH H ] ∧ `¬ `` 'y' [ H ]
                        `in ` ` `` 's' [ H ] ₋ `true ₋ `true
