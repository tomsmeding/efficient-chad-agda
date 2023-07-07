module setup where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality
open import Agda.Builtin.Float
open import Agda.Builtin.IO
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

open import Function.Base using (id; _$_; _∘_; case_of_)
open import Relation.Binary.PropositionalEquality

open import Data.Bool using (Bool; if_then_else_)
open import Data.Empty
open import Data.Fin using (Fin; zero; suc)
open import Data.List hiding (drop)
open import Data.List.Properties using (length-map)
open import Data.Nat
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _≤_ to _≤ℕ_)
open import Data.Integer hiding (suc)
open import Data.Integer.Properties
  using (+-mono-≤; neg-mono-≤; ≤ᵇ⇒≤)
open import Data.Integer.Solver
  using (module +-*-Solver)
open +-*-Solver using (solve; _:-_; :-_; con; _:=_) renaming (_:+_ to _#+_; _:*_ to _#*_)
open import Data.Product using (_×_)
open import Data.Sum using (inj₁; inj₂)

open import spec
import spec.LACM as LACM
open LACM using (LACM)


fin-raise : ∀ {n} -> Fin n -> Fin (ℕ.suc n)
fin-raise zero = zero
fin-raise (suc i) = suc (fin-raise i)

drop : ∀ {n} {a : Set n} -> (l : List a) -> Fin (ℕ.suc (length l)) -> List a
drop l zero = l
drop (_ ∷ xs) (suc n) = drop xs n

variable
  tag : PDTag

weakenSim
  : {Γ Γ' : Env tag} {σ : Typ tag}
 -> ({τ : Typ tag} -> Idx Γ       τ -> Idx Γ'       τ)
 -> ({τ : Typ tag} -> Idx (σ ∷ Γ) τ -> Idx (σ ∷ Γ') τ)
weakenSim f Z = Z
weakenSim f (S i) = S (f i)

weakenTrans
  : {Γ Γ' : Env tag} {σ : Typ tag}
 -> ({τ : Typ tag} -> Idx Γ       τ -> Term tag Γ'       τ)
 -> ({τ : Typ tag} -> Idx (σ ∷ Γ) τ -> Term tag (σ ∷ Γ') τ)
weakenTrans f Z = var Z
weakenTrans f (S i) = sink1 (f i)

φ-positive : (τ : LTyp) -> (x : LinRep τ) -> + 0 ≤ φ τ x
φ-positive LUn x = +≤+ z≤n
φ-positive LR x = +≤+ z≤n
φ-positive (σ :*! τ) nothing = +≤+ z≤n
φ-positive (σ :*! τ) (just (x , y)) =
  +-mono-≤ (+-mono-≤ (+≤+ z≤n) (φ-positive σ x)) (φ-positive τ y)
φ-positive (σ :+! τ) nothing = +≤+ z≤n
φ-positive (σ :+! τ) (just (inj₁ x)) = +-mono-≤ (+≤+ z≤n) (φ-positive σ x)
φ-positive (σ :+! τ) (just (inj₂ y)) = +-mono-≤ (+≤+ z≤n) (φ-positive τ y)

size-positive : (τ : LTyp) -> (x : LinRep τ) -> + 0 ≤ + size τ x
size-positive LUn _ = +≤+ z≤n
size-positive LR _ = +≤+ z≤n
size-positive (σ :*! τ) nothing = +≤+ z≤n
size-positive (σ :*! τ) (just (x , y)) = +-mono-≤ (+-mono-≤ (+≤+ z≤n) (size-positive σ x)) (size-positive τ y)
size-positive (σ :+! τ) nothing = +≤+ z≤n
size-positive (σ :+! τ) (just (inj₁ x)) = +-mono-≤ (+≤+ z≤n) (size-positive σ x)
size-positive (σ :+! τ) (just (inj₂ y)) = +-mono-≤ (+≤+ z≤n) (size-positive τ y)

dprim-cheap : {σ τ : Typ Pr}
           -> (op : Primop Pr σ τ) -> (x : Rep (D1τ σ)) -> (dy : LinRep (D2τ' τ))
           -> let x' : Rep (dut σ)
                  x' = subst Rep (fst (niceprim op)) x
                  y , cprimal = eval (push x' empty) (prim (duPrim op) (var Z))
                  dx , cdual = eval (push dy (push x empty)) (dprim' op)
              in cdual - φ (D2τ' τ) dy + φ (D2τ' σ) dx ≤ + 7 * cprimal
dprim-cheap ADD x dy = ≤ᵇ⇒≤ tt
dprim-cheap MUL x dy = ≤ᵇ⇒≤ tt
dprim-cheap NEG x dy = ≤ᵇ⇒≤ tt
dprim-cheap (LIT _) x dy = ≤ᵇ⇒≤ tt
dprim-cheap SIGN x nothing = ≤ᵇ⇒≤ tt
dprim-cheap SIGN x (just (inj₁ nothing)) = ≤ᵇ⇒≤ tt
dprim-cheap SIGN x (just (inj₁ (just (inj₁ dy)))) = ≤ᵇ⇒≤ tt
dprim-cheap SIGN x (just (inj₁ (just (inj₂ dy)))) = ≤ᵇ⇒≤ tt
dprim-cheap SIGN x (just (inj₂ dy)) = ≤ᵇ⇒≤ tt
dprim-cheap IADD x dy = ≤ᵇ⇒≤ tt
dprim-cheap IMUL x dy = ≤ᵇ⇒≤ tt
dprim-cheap INEG x dy = ≤ᵇ⇒≤ tt

eval-d1prim : ∀ {σ τ} -> (op : Primop Pr σ τ) -> (x : Rep σ)
           -> evalprim (d1Prim op) (primal σ x) ≡ primal τ (evalprim op x)
eval-d1prim ADD x = refl
eval-d1prim MUL x = refl
eval-d1prim NEG x = refl
eval-d1prim (LIT _) x = refl
eval-d1prim SIGN x with primFloatLess x 0.0
... | true      = refl
... | false with primFloatLess 0.0 x
...     | true  = refl
...     | false = refl
eval-d1prim IADD x = refl
eval-d1prim IMUL x = refl
eval-d1prim INEG x = refl

zerov' : {Γ : Env Du} -> (τ : Typ Pr) -> (env : Val Du Γ) -> (Rep (D2τ τ) × ℤ) × (snd (eval env (zerot {Γ} τ)) ≤ + 2)
zerov' τ@Un         env = eval env (zerot τ) , +≤+ (s≤s z≤n)
zerov' τ@Inte       env = eval env (zerot τ) , +≤+ (s≤s z≤n)
zerov' τ@R          env = eval env (zerot τ) , +≤+ (s≤s (s≤s z≤n))
zerov' τ@(σ₁ :* σ₂) env = eval env (zerot τ) , +≤+ (s≤s z≤n)
zerov' τ@(σ₁ :+ σ₂) env = eval env (zerot τ) , +≤+ (s≤s z≤n)

zero-small-φ : {Γ : Env Du} -> (env : Val Du Γ) -> (τ : Typ Pr) -> φ (D2τ' τ) (fst (eval env (zerot τ))) ≡ + 1
zero-small-φ env Un = refl
zero-small-φ env Inte = refl
zero-small-φ env R = refl
zero-small-φ env (σ :* τ) = refl
zero-small-φ env (σ :+ τ) = refl

zero-small-cost : {Γ : Env Du} -> (env : Val Du Γ) -> (τ : Typ Pr) -> snd (eval env (zerot τ)) ≤ + 2
zero-small-cost env Un = ≤ᵇ⇒≤ tt
zero-small-cost env Inte = ≤ᵇ⇒≤ tt
zero-small-cost env R = ≤ᵇ⇒≤ tt
zero-small-cost env (σ :* τ) = ≤ᵇ⇒≤ tt
zero-small-cost env (σ :+ τ) = ≤ᵇ⇒≤ tt

zero-small-φ-v : (τ : Typ Pr) -> φ (D2τ' τ) (fst (zerov (D2τ' τ))) ≡ + 1
zero-small-φ-v Un = refl
zero-small-φ-v Inte = refl
zero-small-φ-v R = refl
zero-small-φ-v (σ :* τ) = refl
zero-small-φ-v (σ :+ τ) = refl

zero-small-cost-v : (τ : Typ Pr) -> snd (zerov (D2τ' τ)) ≤ + 2
zero-small-cost-v Un = ≤ᵇ⇒≤ tt
zero-small-cost-v Inte = ≤ᵇ⇒≤ tt
zero-small-cost-v R = ≤ᵇ⇒≤ tt
zero-small-cost-v (σ :* τ) = ≤ᵇ⇒≤ tt
zero-small-cost-v (σ :+ τ) = ≤ᵇ⇒≤ tt

run-bind2 : ∀ {Γ : Env Pr} {a b : Set} -> (m1 : LACM (map D2τ' Γ) a) -> (k : a -> LACM (map D2τ' Γ) b × ℤ)
         -> (env : LEtup (map D2τ' Γ))
         -> let _ , env' , c = LACM.run (LACM.bind m1 k) env
                r1 , env1 , c1 = LACM.run m1 env
                m2 , ccall = k r1
                r2 , env2 , c2 = LACM.run m2 env1
            in (env' ≡ env2) × (c ≡ c1 + ccall + c2 - + length Γ)
run-bind2 {Γ} m1 k env =
  let p1 , p2 = LACM.run-bind m1 k env
      p3 = cong (\l -> snd (snd (LACM.run m1 env)) + snd (k (fst (LACM.run m1 env))) + snd (snd (LACM.run (fst (k (fst (LACM.run m1 env)))) (fst (snd (LACM.run m1 env))))) - + l) (length-map D2τ' Γ)
      p4 = trans p2 p3
  in p1 , p4

run-scope2 : ∀ {Γ : LEnv} {a : Set} {τ : LTyp}
          -> (m1 : LACM (τ ∷ Γ) a) -> (m2 : LACM (τ ∷ Γ) a) -> m1 ≡ m2
          -> (inval : LinRep τ)
          -> (env : LEtup Γ)
          -> let (outval1 , x1) , env1 , c1 = LACM.run (LACM.scope inval m1) env
                 x2 , (outval2 , env2) , c2 = LACM.run m2 (inval , env)
             in (x1 ≡ x2) × (outval1 ≡ outval2) × (env1 ≡ env2) × (c1 ≡ c2)
run-scope2 m1 m2 prf inval env rewrite prf = LACM.run-scope m2 inval env

φ-of-addLEτ : {Γ : LEnv} {τ : LTyp} -> (idx : Idx Γ τ) -> (val : LinRep τ) -> (env : LEtup Γ)
           -> φ' Γ (addLEτ idx val env) ≡ φ' Γ env - φ τ (env Eτ!! idx) + φ τ (addLEτ idx val env Eτ!! idx)
φ-of-addLEτ {_ ∷ Γ} {τ} Z val env =
  solve 3 (\fp ft fx -> fp #+ ft := fx #+ ft :- fx #+ fp) refl
    (φ τ (fst (plusv τ val (fst env))))
    (φ' Γ (snd env))
    (φ τ (fst env))
φ-of-addLEτ {σ ∷ Γ} {τ} (S idx) val (x , env) rewrite φ-of-addLEτ idx val env =
  solve 4 (\a b c d -> a #+ (b :- c #+ d) := a #+ b :- c #+ d) refl
    (φ σ x)
    (φ' Γ env)
    (φ τ (env Eτ!! idx))
    (φ τ (addLEτ idx val env Eτ!! idx))

plusv-amortises : {τ : LTyp} (a b : LinRep τ)
               -> snd (plusv τ a b) - φ τ a - φ τ b + φ τ (fst (plusv τ a b)) ≤ + 0
plusv-amortises {LUn} a b = +≤+ z≤n
plusv-amortises {LR} a b = +≤+ z≤n
plusv-amortises {σ :*! τ} nothing nothing = +≤+ z≤n
plusv-amortises {σ :*! τ} nothing (just (x , y)) =
  subst (_≤ + 0)
    (solve 1 (\a -> con (+ 0) := con (+ 0) #+ :- a #+ a) refl (+ 1 + φ σ x + φ τ y))
    (+≤+ z≤n)
plusv-amortises {σ :*! τ} (just (x , y)) nothing =
  subst (_≤ + 0)
    (solve 1 (\a -> con (+ 0) := con (+ 1) :- a :- con (+ 1) #+ a) refl (+ 1 + φ σ x + φ τ y))
    (+≤+ z≤n)
plusv-amortises {σ :*! τ} (just (a , b)) (just (x , y)) =
  let k1 = plusv-amortises a x
      k2 = plusv-amortises b y
      k3 = +-mono-≤ k1 k2
  in subst (_≤ + 0)
       (solve 8 (\p1 p2 fa fb fx fy f1 f2 ->
          p1 :- fa :- fx #+ f1 #+ (p2 :- fb :- fy #+ f2)
          := con (+ 1) #+ p1 #+ p2 :- (con (+ 1) #+ fa #+ fb) :- (con (+ 1) #+ fx #+ fy) #+ (con (+ 1) #+ f1 #+ f2))
          refl
          (snd (plusv σ a x)) (snd (plusv τ b y)) (φ σ a) (φ τ b) (φ σ x) (φ τ y) (φ σ (fst (plusv σ a x))) (φ τ (fst (plusv τ b y))))
       k3
plusv-amortises {σ :+! τ} x nothing =
  subst (_≤ + 0)
    (solve 1 (\n -> con (+ 0) := con (+ 1) :- n :- con (+ 1) #+ n) refl
       (φ (σ :+! τ) x))
    (+≤+ z≤n)
plusv-amortises {σ :+! τ} nothing y@(just _) =
  subst (_≤ + 0)
    (solve 1 (\n -> con (+ 0) := con (+ 1) :- con (+ 1) :- n #+ n) refl
       (φ (σ :+! τ) y))
    (+≤+ z≤n)
plusv-amortises {σ :+! τ} (just (inj₁ x)) (just (inj₁ y)) =
  subst (_≤ + 0)
    (solve 4 (\a b c d -> a :- b :- c #+ d := con (+ 1) #+ a :- (con (+ 1) #+ b) :- (con (+ 1) #+ c) #+ (con (+ 1) #+ d)) refl
       (snd (plusv σ x y)) (φ σ x) (φ σ y) (φ σ (fst (plusv σ x y))))
    (plusv-amortises x y)
plusv-amortises {σ :+! τ} (just (inj₂ x)) (just (inj₂ y)) =
  subst (_≤ + 0)
    (solve 4 (\a b c d -> a :- b :- c #+ d := con (+ 1) #+ a :- (con (+ 1) #+ b) :- (con (+ 1) #+ c) #+ (con (+ 1) #+ d)) refl
       (snd (plusv τ x y)) (φ τ x) (φ τ y) (φ τ (fst (plusv τ x y))))
    (plusv-amortises x y)
plusv-amortises {σ :+! τ} (just (inj₁ x)) (just (inj₂ y)) =
  subst (_≤ + 0)
    (solve 2 (\φx φy -> :- (φx #+ φy) := con (+ 1) :- (con (+ 1) #+ φx) :- (con (+ 1) #+ φy) #+ con (+ 1)) refl
       (φ σ x) (φ τ y))
    (neg-mono-≤ (+-mono-≤ (φ-positive σ x) (φ-positive τ y)))
plusv-amortises {σ :+! τ} (just (inj₂ x)) (just (inj₁ y)) =
  subst (_≤ + 0)
    (solve 2 (\φx φy -> :- (φx #+ φy) := con (+ 1) :- (con (+ 1) #+ φx) :- (con (+ 1) #+ φy) #+ con (+ 1)) refl
       (φ τ x) (φ σ y))
    (neg-mono-≤ (+-mono-≤ (φ-positive τ x) (φ-positive σ y)))

lemma-addLEτ-plusv : {Γ : LEnv} {τ : LTyp} -> (idx : Idx Γ τ) (val : LinRep τ) (env : LEtup Γ)
                  -> addLEτ idx val env Eτ!! idx ≡ fst (plusv τ val (env Eτ!! idx))
lemma-addLEτ-plusv Z val env = refl
lemma-addLEτ-plusv (S i) val (x , env) = lemma-addLEτ-plusv i val env

zero-env-small-cost : {Γ' : Env Du} (env : Val Du Γ') -> (Γ : Env Pr) -> snd (eval env (zero-env-term Γ)) ≤ + 1 + + 3 * + length Γ
zero-env-small-cost _ [] = +≤+ (s≤s z≤n)
zero-env-small-cost env (τ ∷ Γ) =
  let k1 : + 1 ≤ + 1
      k1 = +≤+ (s≤s z≤n)
      k2 : snd (eval env (zerot τ)) ≤ + 2
      k2 = zero-small-cost env τ
      k3 : snd (eval env (zero-env-term Γ)) ≤ + 1 + + 3 * + length Γ
      k3 = zero-env-small-cost env Γ
      k4 : + 1 + snd (eval env (zerot τ)) + snd (eval env (zero-env-term Γ))
           ≤ + 3 + (+ 1 + + 3 * + length Γ)
      k4 = +-mono-≤ (+-mono-≤ k1 k2) k3
      answer : + 1 + snd (eval env (zerot τ)) + snd (eval env (zero-env-term Γ))
               ≤ + 1 + + 3 * (+ 1 + + length Γ)
      answer = subst (\x -> + 1 + snd (eval env (zerot τ)) + snd (eval env (zero-env-term Γ)) ≤ x) 
                     (solve 1 (\l -> con (+ 3) #+ (con (+ 1) #+ con (+ 3) #* l)
                                     := con (+ 1) #+ con (+ 3) #* (con (+ 1) #+ l))
                        refl (+ length Γ))
                     k4
  in answer
