module spec.LACM where

open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)

open import Data.Integer using (ℤ; _+_; +_; _-_)
open import Data.List using (_∷_; length)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:-_; :-_; con; _:=_)

open import spec.linear-types


-- In Agda, an 'abstract' block prevents the contained definitions from
-- _reducing_ outside of the block. In effect, this means that outside of the
-- 'abstract' block, only the type signatures of its definitions are visible,
-- not the bodies. We use this to ensure that the complexity proof depends only
-- on the semantics and the complexities of the LACM interpretation, not its
-- actual implementation.
abstract
  -- Local accumulation monad.
  LACM : LEnv -> Set -> Set
  LACM Γ a = LEtup Γ -> a × LEtup Γ × ℤ

  -- The methods of the monad, including pure and bind.

  pure : ∀ {Γ : LEnv} {a : Set} -> a -> LACM Γ a
  pure x e = x , e , one

  -- Note that the continuation should also return the cost of evaluating the
  -- continuation; this cost will be included in the cost returned by 'run'
  -- when handling the top-level monadic computation.
  bind : ∀ {Γ : LEnv} {a b : Set} -> LACM Γ a -> (a -> LACM Γ b × ℤ) -> LACM Γ b
  bind f g e =
    let x , e1 , c1 = f e
        m2 , ccall = g x
        y , e2 , c2 = m2 e1
    in y , e2 , one + c1 + ccall + c2

  -- Returns computation result, the output environment, and the cost of
  -- evaluating the monadic computation.
  run : ∀ {Γ : LEnv} {a : Set} -> LACM Γ a -> LEtup Γ -> a × LEtup Γ × ℤ
  run {Γ} f e =
    let r , e' , c = f e
    in r , e' , one + + length Γ + c

  -- Add the given value to the value at the given index in the state.
  add : ∀ {Γ : LEnv} {τ : LTyp} -> Idx Γ τ -> LinRep τ -> LACM Γ ⊤
  add {τ = τ} Z x (y , e) =
    let z , cz = plusv τ x y
    in tt , (z , e) , one + cz
  add (S i) x (y , e) =  -- supposed to be O(1) access, so we don't cost this traversal
    let r , e' , c = add i x e
    in r , (y , e') , c

  -- Temporarily add a new cell to the state. The final value of this cell is
  -- returned inside the monad when 'scope' finishes.
  scope : ∀ {Γ : LEnv} {τ : LTyp} {a : Set}
       -> LinRep τ -> LACM (τ ∷ Γ) a -> LACM Γ (LinRep τ × a)
  scope x f e =
    let r , (x' , e') , c = f (x , e)
    in (x' , r) , e' , one + c

  -- Properties about the monad methods that we need when reasoning about LACM
  -- in the complexity proof. These four lemmas "push" 'run' down inside
  -- 'pure', 'bind', 'add' and 'scope', and thereby define properties both
  -- about the _semantics_ of the monad, as well as its _complexity_.
  --
  -- The cost counts are used abstractly here: a cost of 1 indicates some O(1)
  -- work, not necessarily one single step in the underlying machine. Or,
  -- alternatively: it is assumed that the underlying machine has support for
  -- these (side-effectful) operations and can execute them in the indicated
  -- number of "steps". Ultimately, this matters little, because this proof is
  -- only concerned with complexity, not absolute performance (which would need
  -- to be benchmarked on an actual machine anyway).

  run-pure : ∀ {Γ : LEnv} {a : Set} -> (x : a)
          -> (env : LEtup Γ)
          -> let _ , env' , c = run {Γ} (pure x) env
             in (env' ≡ env) × (c ≡ one + + length Γ + one)

  run-bind : ∀ {Γ : LEnv} {a b : Set} -> (m1 : LACM Γ a) -> (k : a -> LACM Γ b × ℤ)
          -> (env : LEtup Γ)
          -> let _ , env' , c = run (bind m1 k) env
                 r1 , env1 , c1 = run m1 env
                 m2 , ccall = k r1
                 r2 , env2 , c2 = run m2 env1
             in (env' ≡ env2) × (c ≡ c1 + ccall + c2 - + length Γ)

  run-add : ∀ {Γ : LEnv} {τ : LTyp}
         -> (idx : Idx Γ τ) -> (val : LinRep τ)
         -> (env : LEtup Γ)
         -> let tt , env' , c = run (add idx val) env
            in (env' ≡ addLEτ idx val env)
               × (c ≡ + 2 + snd (plusv τ val (env Eτ!! idx)) + + length Γ)

  run-scope : ∀ {Γ : LEnv} {a : Set} {τ : LTyp}
           -> (m : LACM (τ ∷ Γ) a) -> (inval : LinRep τ)
           -> (env : LEtup Γ)
           -> let (outval1 , x1) , env1 , c1 = run (scope inval m) env
                  x2 , (outval2 , env2) , c2 = run m (inval , env)
              in (x1 ≡ x2) × (outval1 ≡ outval2) × (env1 ≡ env2) × (c1 ≡ c2)

  -- Proofs for the above properties -- these are elided in the paper appendix.

  run-pure x env = refl , refl

  run-bind {Γ} m1 k env =
    refl ,
    let r1 , env1 , c1 = m1 env
        m2 , ccall = k r1
        _ , _ , c2 = m2 env1
    in solve 4 (\lΓ c1 ccall c2 ->
                   con (+ 1) :+ lΓ :+ ((con (+ 1) :+ c1 :+ ccall) :+ c2)
                   := (con (+ 1) :+ lΓ :+ c1) :+ ccall :+ (con (+ 1) :+ lΓ :+ c2) :- lΓ)
         refl
         (+ length Γ) c1 ccall c2

  run-add {Γ} {τ} Z val env =
    refl
    , solve 2 (\lΓ cp -> con (+ 1) :+ lΓ :+ (con (+ 1) :+ cp) := con (+ 2) :+ cp :+ lΓ) refl
        (+ length Γ) (snd (plusv τ val (env Eτ!! Z)))
  run-add {σ ∷ Γ} {τ} (S i) val (x , env) =
    let p1 , p2 = run-add i val env
    in cong (x ,_) p1
       , trans
           (solve 2 (\lΓ ca -> con (+ 2) :+ lΓ :+ ca := con (+ 1) :+ lΓ :+ ca :+ con (+ 1)) refl
              (+ length Γ) (snd (snd (add i val env))))
           (trans
             (cong (_+ + 1) p2)
             (solve 2 (\a b -> con (+ 2) :+ a :+ b :+ con (+ 1) := con (+ 2) :+ a :+ (con (+ 1) :+ b)) refl (snd (plusv τ val (env Eτ!! i))) (+ length Γ)))

  run-scope {Γ} m val env =
    let p = solve 2 (\lΓ c -> con (+ 1) :+ lΓ :+ (con (+ 1) :+ c) := con (+ 2) :+ lΓ :+ c) refl
              (+ length Γ)
              (snd (snd (m (val , env))))
    in refl , refl , refl , p
