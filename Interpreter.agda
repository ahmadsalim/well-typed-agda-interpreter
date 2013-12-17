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
  ε       : Γ 
  _of_,_   : Char → `Set → Γ → Γ 

data Elem :  Char → Γ → Set where
  H  : ∀ {x x′ e t } → {{eq : (x == x′) ≡ true}} → Elem x (x′ of t , e)
  TH : ∀ {x y e t } → {{eq : (x == y) ≡ false}} → Elem x e → Elem x (y of t , e)

lookupΓ : ∀ {x} → (e : Γ) → Elem x e → `Set
lookupΓ ε ()
lookupΓ (_ of t , env) H        = t
lookupΓ (_ of _ , env) (TH idx) = lookupΓ env idx

data Expr : Γ → `Set → Set where
  `false       : ∀ {e} → Expr e `Bool
  `true        : ∀ {e} → Expr e `Bool
  `n_          : ∀ {e} → ℕ    → Expr e `Nat
  ``_[_]       : ∀ {e} → (x : Char) → (idx : Elem x e) → Expr e (lookupΓ e idx)
  `_·_         : ∀ {e t s} → Expr e (` t ⇨ s) → Expr e t → Expr e s
  `λ_`of_⇨_     : ∀ {e tr} → (x : Char) → (tx : `Set) → Expr (x of tx , e) tr → Expr e (` tx ⇨ tr) 
  `_+_         : ∀ {e} → Expr e `Nat → Expr e `Nat → Expr e `Nat
  `_*_         : ∀ {e} → Expr e `Nat → Expr e `Nat → Expr e `Nat
  `_∧_         : ∀ {e} → Expr e `Bool → Expr e `Bool → Expr e `Bool
  `_∨_         : ∀ {e} → Expr e `Bool → Expr e `Bool → Expr e `Bool
  `_≤_         : ∀ {e} → Expr e `Nat → Expr e `Nat → Expr e `Bool
  `¬_          : ∀ {e} → Expr e `Bool → Expr e `Bool 
  `_,_         : ∀ {e t s} → Expr e t → Expr e s → Expr e (` t × s)
  `fst         : ∀ {e t s} → Expr e (` t × s) → Expr e t
  `snd         : ∀ {e t s} → Expr e (` t × s) → Expr e s
  `left        : ∀ {e t s} → Expr e t → Expr e (` t + s)
  `right       : ∀ {e t s} → Expr e s → Expr e (` t + s)
  `case_`of_||_ : ∀ {e t s u} → Expr e (` t + s) → Expr e (` t ⇨ u) → Expr e (` s ⇨ u) → Expr e u
  `tt          : ∀ {e} → Expr e `Unit
  `let_:=_`in_ : ∀ {e th tb} → (x : Char) → Expr e th → Expr (x of th , e) tb → Expr e tb
  `if_`then_`else_ : ∀ {e t} → Expr e `Bool → Expr e t → Expr e t → Expr e t

data Env : Γ → Set₁ where
  []    : Env ε
  _∷_  : ∀ {x t e} → # t → Env e → Env (x of t , e)

lookupEnv : ∀ {x} → (e : Γ) → Env e → (idx : Elem x e) → # lookupΓ e idx
lookupEnv ε [] ()
lookupEnv (_ of _ , tenv) (val ∷ env) H = val
lookupEnv (_ of _ , tenv) (val ∷ env) (TH i) = lookupEnv tenv env i 

printType  : `Set → Str.String
printType `Nat = "Nat"
printType `Bool = "Bool"
printType (` t ⇨ s) = printType t Str.++ " -> " Str.++ printType s
printType `Unit = "()"
printType (` t × s) = "(" Str.++ printType t Str.++ " , " Str.++ printType s Str.++ ")"
printType (` t + s) = "(" Str.++ printType t Str.++ " | " Str.++ printType s Str.++ ")"

print : ∀ {e t} → Expr e t → Str.String
print `false = "false"
print `true = "true"
print (`n x) = show x
print `` x [ idx ] = Str.fromList (x List.∷ List.[])
print (` f · x) = "(" Str.++ print f Str.++ " " Str.++ print x Str.++ ")"
print (`λ x `of tx ⇨ expr) = "(λ " Str.++ Str.fromList (x List.∷ List.[]) Str.++ " : " Str.++ printType tx Str.++ " -> " Str.++ print expr Str.++ ")"
print (` l + r) = "(" Str.++ print l Str.++ ") + (" Str.++ print r Str.++ ")"
print (` l * r) = "(" Str.++ print l Str.++ ") * (" Str.++ print r Str.++ ")"
print (` l ∧ r) = "(" Str.++ print l Str.++ ") ∧ (" Str.++ print r Str.++ ")"
print (` l ∨ r) = "(" Str.++ print l Str.++ ") ∨ (" Str.++ print r Str.++ ")"
print (` l ≤ r) = "(" Str.++ print l Str.++ ") ≤ (" Str.++ print r Str.++ ")"
print (`¬ v) = "¬" Str.++ print v
print (` l , r) = "(" Str.++ print l Str.++ " , " Str.++ print r Str.++ ")"
print (`fst expr) = "(fst " Str.++ print expr Str.++ ")"
print (`snd expr) = "(snd " Str.++ print expr Str.++ ")"
print (`left expr) = "(left " Str.++ print expr Str.++ ")"
print (`right expr) = "(right " Str.++ print expr Str.++ ")"
print (`case v `of le || re) = "(case " Str.++
                               print v Str.++
                               "of" Str.++ print le Str.++ "||" Str.++ print re Str.++ ")"
print `tt = "()"
print (`let x := t `in b) = "(let " Str.++ Str.fromList (x List.∷ List.[]) Str.++ " = " Str.++ print t Str.++ " in " Str.++ print b Str.++ " )"
print (`if b `then et `else ef) = "(if " Str.++ print b Str.++ " then " Str.++ print et Str.++ " else " Str.++ print ef Str.++ ")"

interpret : ∀ {t} → Expr ε t → # t
interpret = interpret' []
  where interpret' : ∀ {e t} → Env e → Expr e t → # t
        interpret' env `true = true
        interpret' env `false = false
        interpret' env (`n n) = n
        interpret' {tenv} env `` x [ idx ] = lookupEnv tenv env idx
        interpret' env (` f · x) = (interpret' env f) (interpret' env x)
        interpret' env (`λ _ `of tx ⇨ body) = λ (x : # tx) → interpret' (x ∷ env) body
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
        interpret' env `tt = U.unit
        interpret' env (`let _ := h `in b) = interpret' (hval ∷ env) b
          where hval = interpret' env h
        interpret' env (`if b `then et `else ef) with interpret' env b
        interpret' env (`if b `then et `else ef) | true = interpret' env et
        interpret' env (`if b `then et `else ef) | false = interpret' env ef

testSimpleLambda : Expr ε `Nat
testSimpleLambda = ` (`λ 'x' `of `Nat ⇨ ` `` 'x' [ H ] + `` 'x' [ H ]) · `n 10

testNestedLambda : Expr ε `Nat
testNestedLambda = ` ` (`λ 'x' `of `Nat ⇨ (`λ 'y' `of `Nat ⇨ ` `` 'x' [ TH H ] + `` 'y' [ H ])) · `n 10 · `n 15

-- Should not work because the inner x is not bound to a boolean, and it should not be possible to refer to the outside x using Elem
--testNaming : Expr ε `Bool
--testNaming = ` ` `λ 'x' `of `Bool ⇨ (`λ 'x' `of `Unit ⇨ `` 'x' [ {!!} ]) · `true · `tt

testSum1 : Expr ε `Nat
testSum1 = `let 'n' := `case `left (`n 10) `of (`λ 'n' `of `Nat ⇨ `` 'n' [ H ]) || (`λ 'b' `of `Bool ⇨ (`if (`` 'b' [ H ]) `then `n 1 `else `n 0))  `in `` 'n' [ H ]  

testSum2 : Expr ε `Nat
testSum2 = `let 'n' := `case `right `true `of (`λ 'n' `of `Nat ⇨ `` 'n' [ H ]) || (`λ 'b' `of `Bool ⇨ (`if (`` 'b' [ H ]) `then `n 1 `else `n 0))  `in `` 'n' [ H ]  
