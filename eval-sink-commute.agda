module eval-sink-commute where

open import Agda.Builtin.Sigma
open import Agda.Builtin.Maybe
open import Agda.Builtin.Unit

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (length; []; _∷_)
open import Data.Integer hiding (suc)
import Data.Nat as ℕ
open ℕ using (ℕ)
open import Data.Product using (_×_)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import setup
open import spec


forall-fin : {n : ℕ} -> (Fin n -> Set) -> Set
forall-fin {ℕ.zero} f = ⊤
forall-fin {ℕ.suc n} f = f zero × forall-fin {n} (f ∘ suc)

forall-fin-trivial : {n : ℕ} {f : Fin n -> Set} -> ((x : Fin n) -> f x) -> forall-fin f
forall-fin-trivial {ℕ.zero} g = tt
forall-fin-trivial {ℕ.suc n} g = g zero , forall-fin-trivial (\x -> g (suc x))

make-index : {Γ : Env tag} (idx : Fin (length Γ)) -> Idx Γ (Γ !! idx)
make-index {Γ = σ ∷ Γ} zero = Z
make-index {Γ = σ ∷ Γ} (suc i) = S (make-index i)

sinks-to : {Γ Γ' : Env tag}
        -> (w : Weakening Γ Γ')
        -> (env : Val tag Γ) (env2 : Val tag Γ')
        -> Set
sinks-to w env env2 =
  forall-fin (\i -> let idx = make-index i
                        idx' = weaken-var w idx
                    in valprj env idx ≡ valprj env2 idx')

sinks-to-idx : {Γ Γ' : Env tag}
            -> (w : Weakening Γ Γ')
            -> (env : Val tag Γ) (env2 : Val tag Γ')
            -> sinks-to w env env2
            -> {τ : Typ tag} -> (idx : Idx Γ τ) -> valprj env idx ≡ valprj env2 (weaken-var w idx)
sinks-to-idx w env env2 (p , _) Z = p
sinks-to-idx WEnd (push _ env) (push _ env2) (_ , p) (S i) = sinks-to-idx WEnd env env2 p i
sinks-to-idx (WCopy w) (push _ env) (push _ env2) (_ , p) (S i) = sinks-to-idx w env env2 p i
sinks-to-idx (WSkip w) env (push _ env2) p (S i) = sinks-to-idx w env env2 p (S i)

wend-is-id : {Γ : Env tag}
          -> (env : Val tag Γ) (env2 : Val tag Γ)
          -> sinks-to WEnd env env2
          -> env ≡ env2
wend-is-id empty empty _ = refl
wend-is-id (push x env) (push y env2) (refl , p) rewrite wend-is-id env env2 p = refl

inj-weaken-commute : {Γ Γ' Γclo : Env Du}
                  -> (f : {σ : Typ Du} -> Idx Γclo σ -> Idx Γ σ)
                  -> (w : Weakening Γ Γ')
                  -> (env : Val Du Γ) (env2 : Val Du Γ')
                  -> sinks-to w env env2
                  -> buildValFromInj f env ≡ buildValFromInj (weaken-var w ∘ f) env2
inj-weaken-commute {Γclo = []} f w env env2 _ = refl
inj-weaken-commute {Γclo = τ ∷ Γclo} f w env env2 p
  rewrite sinks-to-idx w env env2 p (f Z)
  rewrite inj-weaken-commute (f ∘ S) w env env2 p =
    refl

eval-sink-commute : {Γ Γ' : Env tag} {τ : Typ tag}
                 -> (env : Val tag Γ) (env2 : Val tag Γ')
                 -> (w : Weakening Γ Γ')
                 -> sinks-to w env env2
                 -> (e : Term tag Γ τ)
                 -> eval env e ≡ eval env2 (sink w e)
eval-sink-commute env env2 w (p , _) (var Z) = cong (_, _) p
eval-sink-commute env env2 WEnd p (var (S i)) rewrite wend-is-id env env2 p = refl
eval-sink-commute (push x env) (push y env2) (WCopy w) (_ , p) (var (S i)) =
  eval-sink-commute env env2 w p (var i)
eval-sink-commute env (push y env2) (WSkip w) p (var (S i)) =
  eval-sink-commute env env2 w p (var (S i))

eval-sink-commute env env2 w p (let' e1 e2)
  rewrite eval-sink-commute env env2 w p e1
  rewrite let x , _ = eval env2 (sink w e1)
          in eval-sink-commute (push x env) (push x env2) (WCopy w) (refl , p) e2 =
    refl
eval-sink-commute env env2 w p (lam Γclo inj e)
  rewrite inj-weaken-commute inj w env env2 p =
    refl
eval-sink-commute env env2 w p (app e1 e2)
  rewrite eval-sink-commute env env2 w p e1
  rewrite eval-sink-commute env env2 w p e2 =
    refl
eval-sink-commute env env2 w p (prim op e)
  rewrite eval-sink-commute env env2 w p e =
    refl
eval-sink-commute env env2 w p unit = refl
eval-sink-commute env env2 w p (pair e1 e2)
  rewrite eval-sink-commute env env2 w p e1
  rewrite eval-sink-commute env env2 w p e2 =
    refl
eval-sink-commute env env2 w p (fst' e)
  rewrite eval-sink-commute env env2 w p e =
    refl
eval-sink-commute env env2 w p (snd' e)
  rewrite eval-sink-commute env env2 w p e =
    refl
eval-sink-commute env env2 w p (inl e)
  rewrite eval-sink-commute env env2 w p e =
    refl
eval-sink-commute env env2 w p (inr e)
  rewrite eval-sink-commute env env2 w p e =
    refl
eval-sink-commute env env2 w p (pureevm e)
  rewrite eval-sink-commute env env2 w p e =
    refl
eval-sink-commute env env2 w p (bindevm e1 e2)
  rewrite eval-sink-commute env env2 w p e1
  rewrite eval-sink-commute env env2 w p e2 =
    refl
eval-sink-commute env env2 w p (runevm e1 e2)
  rewrite eval-sink-commute env env2 w p e1
  rewrite eval-sink-commute env env2 w p e2 =
    refl
eval-sink-commute env env2 w p (addevm i e)
  rewrite eval-sink-commute env env2 w p e =
    refl
eval-sink-commute env env2 w p (scopeevm e1 e2)
  rewrite eval-sink-commute env env2 w p e1
  rewrite eval-sink-commute env env2 w p e2 =
    refl
eval-sink-commute env env2 w p lunit = refl
eval-sink-commute env env2 w p (lpair e1 e2)
  rewrite eval-sink-commute env env2 w p e1
  rewrite eval-sink-commute env env2 w p e2 =
    refl
eval-sink-commute env env2 w p (lfst' e)
  rewrite eval-sink-commute env env2 w p e
  with fst (eval env2 (sink w e))
... | nothing = refl
... | just (x , y) rewrite eval-sink-commute env env2 w p e = refl
eval-sink-commute env env2 w p (lsnd' e)
  rewrite eval-sink-commute env env2 w p e
  with fst (eval env2 (sink w e))
... | nothing = refl
... | just (x , y) rewrite eval-sink-commute env env2 w p e = refl
eval-sink-commute env env2 w p lpairzero = refl
eval-sink-commute env env2 w p (linl e)
  rewrite eval-sink-commute env env2 w p e =
    refl
eval-sink-commute env env2 w p (linr e)
  rewrite eval-sink-commute env env2 w p e =
    refl
eval-sink-commute env env2 w p (case' e1 e2 e3)
  rewrite eval-sink-commute env env2 w p e1
  with fst (eval env2 (sink w e1))
... | inj₁ x
        rewrite eval-sink-commute env env2 w p e1
        rewrite eval-sink-commute (push x env) (push x env2) (WCopy w) (refl , p) e2 =
          refl
... | inj₂ x
        rewrite eval-sink-commute env env2 w p e1
        rewrite eval-sink-commute (push x env) (push x env2) (WCopy w) (refl , p) e3 =
          refl
eval-sink-commute env env2 w p (lcastl e)
  rewrite eval-sink-commute env env2 w p e
  with fst (eval env2 (sink w e))
... | nothing rewrite eval-sink-commute env env2 w p e = refl
... | just (inj₁ x) rewrite eval-sink-commute env env2 w p e = refl
... | just (inj₂ y) rewrite eval-sink-commute env env2 w p e = refl
eval-sink-commute env env2 w p (lcastr e)
  rewrite eval-sink-commute env env2 w p e
  with fst (eval env2 (sink w e))
... | nothing rewrite eval-sink-commute env env2 w p e = refl
... | just (inj₁ x) rewrite eval-sink-commute env env2 w p e = refl
... | just (inj₂ y) rewrite eval-sink-commute env env2 w p e = refl
eval-sink-commute env env2 w p lsumzero = refl
