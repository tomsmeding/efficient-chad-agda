module chad-preserves-primal where

open import Agda.Builtin.Sigma

open import Function.Base using (_∘_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality

open import setup
open import spec
open import eval-sink-commute


chad-preserves-primal : {Γ : Env Pr} {τ : Typ Pr}
                     -> (env : Val Pr Γ) (e : Term Pr Γ τ)
                     -> fst (fst (eval (primalVal env) (chad e))) ≡ primal τ (fst (eval env e))
chad-preserves-primal (push x env) (var Z) = refl
chad-preserves-primal (push _ env) (var (S i)) = chad-preserves-primal env (var i)
chad-preserves-primal env (let' {σ = σ} {τ = τ} e1 e2)
  rewrite chad-preserves-primal env e1 =
  let x , _ = eval env e1
      out1 , _ = eval (primalVal env) (chad e1)
      y , _ = eval (push x env) e2
      e2res = eval (push (primal σ x) (push out1 (primalVal env)))
                   (sink (WCopy (WSkip WEnd)) (chad e2))
      rec = chad-preserves-primal (push x env) e2
      answer : e2res ≡ eval (push (primal σ x) (primalVal env)) (chad e2)
      answer = sym (eval-sink-commute (push (primal σ x) (primalVal env))
                                      (push (primal σ x) (push out1 (primalVal env)))
                                      (WCopy (WSkip WEnd))
                                      (refl , forall-fin-trivial (\i -> refl))
                                      (chad e2))
  in trans (cong (fst ∘ fst) answer) rec
chad-preserves-primal env (prim op e)
  rewrite chad-preserves-primal env e
  rewrite eval-d1prim op (fst (eval env e)) =
    refl
chad-preserves-primal env unit = refl
chad-preserves-primal env (pair e1 e2)
  rewrite chad-preserves-primal env e1
  rewrite chad-preserves-primal env e2 =
    refl
chad-preserves-primal env (fst' e) rewrite chad-preserves-primal env e = refl
chad-preserves-primal env (snd' e) rewrite chad-preserves-primal env e = refl
chad-preserves-primal env (inl e) rewrite chad-preserves-primal env e = refl
chad-preserves-primal env (inr e) rewrite chad-preserves-primal env e = refl
chad-preserves-primal env (case' {σ = σ} {τ = τ} e1 e2 e3)
  rewrite chad-preserves-primal env e1
  with fst (eval env e1)
... | inj₁ x =
        let rec = chad-preserves-primal (push x env) e2
            out1 , _ = eval (primalVal env) (chad e1)
            e2res = eval (push (primal σ x) (push out1 (primalVal env)))
                         (sink (WCopy (WSkip WEnd)) (chad e2))
            answer : e2res ≡ eval (push (primal σ x) (primalVal env)) (chad e2)
            answer = sym (eval-sink-commute (push (primal σ x) (primalVal env))
                                            (push (primal σ x) (push out1 (primalVal env)))
                                            (WCopy (WSkip WEnd))
                                            (refl , forall-fin-trivial (\i -> refl))
                                            (chad e2))
        in trans (cong (fst ∘ fst) answer) rec
... | inj₂ y =
        let rec = chad-preserves-primal (push y env) e3
            out1 , _ = eval (primalVal env) (chad e1)
            e3res = eval (push (primal τ y) (push out1 (primalVal env)))
                         (sink (WCopy (WSkip WEnd)) (chad e3))
            answer : e3res ≡ eval (push (primal τ y) (primalVal env)) (chad e3)
            answer = sym (eval-sink-commute (push (primal τ y) (primalVal env))
                                            (push (primal τ y) (push out1 (primalVal env)))
                                            (WCopy (WSkip WEnd))
                                            (refl , forall-fin-trivial (\i -> refl))
                                            (chad e3))
        in trans (cong (fst ∘ fst) answer) rec
