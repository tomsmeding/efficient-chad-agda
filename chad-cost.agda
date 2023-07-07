open import Agda.Builtin.IO
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Float
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Primitive

open import Data.List
open import Data.List.Properties using (length-map)
open import Data.Nat
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _≤_ to _≤ℕ_)
open import Data.Integer
open import Data.Integer.Properties
  using (≤-trans; +-identityˡ; drop‿+≤+; +-monoʳ-≤; +-mono-≤; m≤n⇒m-n≤0; m-n≤0⇒m≤n; ≤ᵇ⇒≤; ≤-reflexive)
open import Data.Integer.Solver
  using (module +-*-Solver)
open +-*-Solver using (solve; _:-_; :-_; con; _:=_)
open import Data.Product using (_×_)
open import Data.Sum using (inj₁; inj₂)

import Data.Fin as F
import Data.Vec as V
open import Function.Base using (id)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (trans; subst; cong; sym)

open import spec
open import setup
open import eval-sink-commute
open import chad-preserves-primal
open import lemmas
import spec.LACM as LACM
open LACM using (LACM)


th1 : TH1-STATEMENT

th1 {Γ} env ctg denvin unit =
  let p1 , p2 = LACM.run-pure tt denvin
      p1' = cong (φ' (map D2τ' Γ)) p1
      p3 = cong +_ (length-map D2τ' Γ)
      tt , denvout , cmonad = LACM.run (LACM.pure tt) denvin
      φe1 = φ' (map D2τ' Γ) denvin
      φeout = φ' (map D2τ' Γ) denvout
      envlen' = + length (map D2τ' Γ)
      envlen = + length Γ
  in {- LEMMA -} lemma-unit cmonad φe1 φeout p1' envlen' p2 envlen p3

th1 {Γ} {σ :* τ} env ctg@nothing denvin (pair e1 e2) =
  let (primal , bp) , crun = eval (primalVal env) (chad (pair e1 e2))
      out1 , crun1 = eval (primalVal env) (chad e1)
      out2 , crun2 = eval (primalVal env) (chad e2)
      subenv1 : Val Du (((D1τ σ :* (D2τ σ :-> D2Γ Γ)) :* (D1τ τ :* (D2τ τ :-> D2Γ Γ))) ∷ [])
      subenv1 = push (out1 , out2) empty
      subenv2 : Val Du (D2τ (σ :* τ) ∷ ((D1τ σ :* (D2τ σ :-> D2Γ Γ)) :* (D1τ τ :* (D2τ τ :-> D2Γ Γ))) ∷ [])
      subenv2 = push nothing subenv1
      primal1 , bp1 = out1
      primal2 , bp2 = out2
      mf , ccall = bp ctg
      ctg1 , czero1 = zerov (D2τ' σ)
      ctg2 , czero2 = zerov (D2τ' τ)
      mf1 , ccall1 = bp1 ctg1
      mf2 , ccall2 = bp2 ctg2
      tt , denvout , cmonad = LACM.run mf denvin
      tt , denv2 , cmonad1 = LACM.run mf1 denvin
      tt , denv3 , cmonad2 = LACM.run mf2 denv2
      φd1 = φ (D2τ' σ) ctg1
      φd2 = φ (D2τ' τ) ctg2
      φe1 = φ' (map D2τ' Γ) denvin
      φe2 = φ' (map D2τ' Γ) denv2
      φe3 = φ' (map D2τ' Γ) denv3
      φeout = φ' (map D2τ' Γ) denvout
      _ , evc1 = eval env e1
      _ , evc2 = eval env e2
      pzero1 : czero1 ≤ + 2
      pzero1 = zero-small-cost-v σ
      pzero2 : czero2 ≤ + 2
      pzero2 = zero-small-cost-v τ
      pφd1 : φd1 ≡ + 1
      pφd1 = zero-small-φ-v σ
      pφd2 : φd2 ≡ + 1
      pφd2 = zero-small-φ-v τ
      runbindres : (denvout ≡ denv3)
                   × (cmonad ≡ cmonad1 + + 1 + cmonad2 - + length Γ)
      runbindres = run-bind2 mf1 (\x -> mf2 , + 1) denvin
      prunbind1 , prunbind2 = runbindres
      pφdenvout : φeout ≡ φe3
      pφdenvout = cong (φ' (map D2τ' Γ)) prunbind1
      k1 = th1 env ctg1 denvin e1
      k2 = th1 env ctg2 denv2 e2
      envlen = + length Γ
  in {- LEMMA -} lemma-pair-nothing crun1 crun2 czero1 czero2 ccall1 ccall2 cmonad cmonad1 cmonad2 φd1 φd2 φe1 φe2 φe3 φeout evc1 evc2 pzero1 pzero2 pφd1 pφd2 pφdenvout envlen prunbind2 k1 k2

th1 {Γ} {σ :* τ} env ctg@(just ctg') denvin (pair e1 e2) =
  let (primal , bp) , crun = eval (primalVal env) (chad (pair e1 e2))
      out1 , crun1 = eval (primalVal env) (chad e1)
      out2 , crun2 = eval (primalVal env) (chad e2)
      primal1 , bp1 = out1
      primal2 , bp2 = out2
      mf , ccall = bp ctg
      ctg1 , ctg2 = ctg'
      mf1 , ccall1 = bp1 ctg1
      mf2 , ccall2 = bp2 ctg2
      tt ,  denvout , cmonad = LACM.run mf denvin
      tt , denv2 , cmonad1 = LACM.run mf1 denvin
      tt , denv3 , cmonad2 = LACM.run mf2 denv2
      φd = φ (D2τ' σ :*! D2τ' τ) ctg
      φd1 = φ (D2τ' σ) ctg1
      φd2 = φ (D2τ' τ) ctg2
      φe1 = φ' (map D2τ' Γ) denvin
      φe2 = φ' (map D2τ' Γ) denv2
      φe3 = φ' (map D2τ' Γ) denv3
      φeout = φ' (map D2τ' Γ) denvout
      _ , evc1 = eval env e1
      _ , evc2 = eval env e2
      runbindres : (denvout ≡ denv3)
                   × (cmonad ≡ cmonad1 + + 1 + cmonad2 - + length Γ)
      runbindres = run-bind2 mf1 (\x -> mf2 , + 1) denvin
      prunbind1 , prunbind2 = runbindres
      pφdenvout : φeout ≡ φe3
      pφdenvout = cong (φ' (map D2τ' Γ)) prunbind1
      k1 : crun1 + ccall1 + cmonad1 - φd1 - φe1 + φe2 - + length Γ ≤ + 31 * cost env e1
      k1 = th1 env ctg1 denvin e1
      k2 : crun2 + ccall2 + cmonad2 - φd2 - φe2 + φe3 - + length Γ ≤ + 31 * cost env e2
      k2 = th1 env ctg2 denv2 e2
      envlen = + length Γ
  in {- LEMMA -} lemma-pair-just crun1 crun2 ccall1 ccall2 cmonad cmonad1 cmonad2 φd1 φd2 φe1 φe2 φe3 φeout evc1 evc2 pφdenvout envlen prunbind2 k1 k2

th1 {Γ} {τ} env ctg denvin (var idx) =
  let lconvIdx = convIdx D2τ'
      (primal , bp) , crun = eval (primalVal env) (chad (var idx))
      mf , ccall = bp ctg
      tt ,  denvout , cmonad = LACM.run mf denvin
      φd = φ (D2τ' τ) ctg
      φe1 = φ' (map D2τ' Γ) denvin
      φe2 = φ' (map D2τ' Γ) (addLEτ (lconvIdx idx) ctg denvin)
      φeout = φ' (map D2τ' Γ) denvout
      prunadd1 , prunadd2 = LACM.run-add (lconvIdx idx) ctg denvin
      p1 = cong (φ' (map D2τ' Γ)) prunadd1
      envlen = + length Γ
      cplus = snd (plusv (D2τ' τ) ctg (denvin Eτ!! lconvIdx idx))
      envlen' = + length (map D2τ' Γ)
      plenmap : envlen ≡ envlen'
      plenmap = sym (cong +_ (length-map D2τ' Γ))
      pφaddlet = φ-of-addLEτ (lconvIdx idx) ctg denvin
      pplus = plusv-amortises ctg (denvin Eτ!! lconvIdx idx)
      paddlet : φ (D2τ' τ) (addLEτ (lconvIdx idx) ctg denvin Eτ!! lconvIdx idx)
              ≡ φ (D2τ' τ) (fst (plusv (D2τ' τ) ctg (denvin Eτ!! lconvIdx idx)))
      paddlet = cong (φ (D2τ' τ)) (lemma-addLEτ-plusv (lconvIdx idx) ctg denvin)
  in {- LEMMA -} lemma-var cmonad φd φe1 φe2 φeout p1 envlen cplus envlen' prunadd2 plenmap (φ (D2τ' τ) (denvin Eτ!! convIdx D2τ' idx)) (φ (D2τ' τ) (addLEτ (convIdx D2τ' idx) ctg denvin Eτ!! convIdx D2τ' idx)) pφaddlet (φ (D2τ' τ) (fst (plusv (D2τ' τ) ctg (denvin Eτ!! convIdx D2τ' idx)))) pplus paddlet

th1 {Γ} {τ} env ctg denvin (let' {σ = σ} e1 e2) =
  let origx1 , evc1 = eval env e1
      _ , evc2 = eval (push origx1 env) e2
      (primal , bp) , crun = eval (primalVal env) (chad (let' e1 e2))
      out1 , crun1 = eval (primalVal env) (chad e1)
      primal1 , bp1 = out1
      preservation : primal1 ≡ spec.primal σ origx1
      preservation = chad-preserves-primal env e1
      env2 : Val Du ((D1τ σ :* (D2τ σ :-> D2Γ Γ)) ∷ D1Γ Γ)
      env2 = push out1 (primalVal env)
      eval-e2-A : Rep (D1τ τ :* (D2τ τ :-> D2Γ (σ ∷ Γ))) × ℤ
      eval-e2-A = eval (push primal1 env2) (sink (WCopy (WSkip WEnd)) (chad e2))
      eval-e2-B : Rep (D1τ τ :* (D2τ τ :-> D2Γ (σ ∷ Γ))) × ℤ
      eval-e2-B = eval (primalVal (push origx1 env)) (chad e2)
      eval-e2-equal : eval-e2-A ≡ eval-e2-B
      eval-e2-equal =
        trans
          (cong (\hole -> eval (push hole env2) (sink (WCopy (WSkip WEnd)) (chad e2)))
                (chad-preserves-primal env e1))
          (sym (eval-sink-commute
                  (push (spec.primal σ origx1) (primalVal env))
                  (push (spec.primal σ origx1) (push out1 (primalVal env)))
                  (WCopy (WSkip WEnd))
                  (refl , forall-fin-trivial (\x -> refl))
                  (chad e2)))
      out2 , crun2 = eval-e2-A
      out2' , crun2' = eval-e2-B
      equals-crun2 : crun2 ≡ crun2'
      equals-crun2 = cong snd eval-e2-equal
      env3 : Val Du ((D1τ τ :* (D2τ τ :-> D2Γ (σ ∷ Γ))) ∷ (D1τ σ :* (D2τ σ :-> D2Γ Γ)) ∷ D1Γ Γ)
      env3 = push out2 env2
      env4 : Val Du (D2τ τ ∷ (D1τ τ :* (D2τ τ :-> D2Γ (σ ∷ Γ))) ∷ (D1τ σ :* (D2τ σ :-> D2Γ Γ)) ∷ [])
      env4 = push ctg (push out2 (push out1 empty))
      zerores , czero = eval env4 (zerot σ)
      primal2 , bp2 = out2
      primal2' , bp2' = out2'
      mf , ccall = bp ctg
      mf2 , ccall2 = bp2 ctg
      tt , denvout , cmonad = LACM.run mf denvin
      p-mf-equality : mf ≡ LACM.bind (LACM.scope zerores mf2) (λ x → fst (bp1 (fst x)) , + 5 + snd (bp1 (fst x)))
      p-mf-equality = refl
      (dx , tt) , denv2 , cmonad2 = LACM.run (LACM.scope zerores mf2) denvin
      mf1 , cbp1 = bp1 dx
      mf2' , cbp2 = bp2' ctg
      equals-mf2 : mf2 ≡ mf2'
      equals-mf2 = cong (\x -> fst (snd (fst x) ctg)) eval-e2-equal
      equals-ccall2 : ccall2 ≡ cbp2
      equals-ccall2 = cong (\x -> snd (snd (fst x) ctg)) eval-e2-equal
      tt , denv3 , cmonad1 = LACM.run mf1 denv2
      tt , (dx' , denv2') , cmonad2' = LACM.run mf2' (zerores , denvin)
      _ , equal-dx , equal-denv2 , equal-cmonad2 = run-scope2 mf2 mf2' equals-mf2 zerores denvin
      envlen = + length Γ
      runbindres : (denvout ≡ denv3) × (cmonad ≡ cmonad2 + (+ 5 + cbp1) + cmonad1 + - envlen)
      runbindres = run-bind2 (LACM.scope zerores mf2) (λ x → fst (bp1 (fst x)) , + 5 + snd (bp1 (fst x))) denvin
      prunbind1 , prunbind2 = runbindres
      φd = φ (D2τ' τ) ctg
      φe1 = φ' (map D2τ' Γ) denvin
      φeout = φ' (map D2τ' Γ) denvout
      φzerores = φ (D2τ' σ) zerores
      φdx = φ (D2τ' σ) dx
      φdx' = φ (D2τ' σ) dx'
      equal-φdx : φdx ≡ φdx'
      equal-φdx = cong (φ (D2τ' σ)) equal-dx
      φdenv2 = φ' (map D2τ' Γ) denv2
      φdenv2' = φ' (map D2τ' Γ) denv2'
      equal-φdenv2 : φdenv2 ≡ φdenv2'
      equal-φdenv2 = cong (φ' (map D2τ' Γ)) equal-denv2
      φdenv3 = φ' (map D2τ' Γ) denv3
      prunbind1φ : φeout ≡ φdenv3
      prunbind1φ = cong (φ' (map D2τ' Γ)) prunbind1
      pczerosmall : czero ≤ + 2
      pczerosmall = zero-small-cost env4 σ
      pφzeroressmall : φzerores ≡ + 1
      pφzeroressmall = zero-small-φ env4 σ
      k2 = th1 (push origx1 env) ctg (zerores , denvin) e2
      k1 = th1 env dx denv2 e1
  in {- LEMMA -} lemma-let evc1 evc2 crun1 crun2 crun2' equals-crun2 czero ccall2 cmonad cmonad2 cbp1 cbp2 equals-ccall2 cmonad1 cmonad2' equal-cmonad2 envlen prunbind2 φd φe1 φeout φzerores φdx φdx' equal-φdx φdenv2 φdenv2' equal-φdenv2 φdenv3 prunbind1φ pczerosmall pφzeroressmall k2 k1

th1 {Γ} env ctg denvin (prim {σ = σ} {τ = τ} op e) =
  let out , crun = eval (primalVal env) (chad (prim op e))
      primal , bp = out
      out1 , crun1 = eval (primalVal env) (chad e)
      primal1 , bp1 = out1
      subenv1 : Val Du (D2τ τ ∷ D1τ σ ∷ D2τ τ ∷ (D1τ σ :* (D2τ σ :-> D2Γ Γ)) ∷ [])
      subenv1 = push ctg (push primal1 (push ctg (push out1 empty)))
      subenv2 : Val Du ((D1τ σ :* (D2τ σ :-> D2Γ Γ)) ∷ D1Γ Γ)
      subenv2 = push out1 (primalVal env)
      dx , cdprim = eval subenv1 (sink (WCopy (WCopy WCut)) (dprim' op))
      mf1 , ccall1 = bp1 dx
      tt , denv2 , cmonad1 = LACM.run mf1 denvin
      φdx = φ (D2τ' σ) dx
      φd = φ (D2τ' τ) ctg
      φe1 = φ' (map D2τ' Γ) denvin
      φe2 = φ' (map D2τ' Γ) denv2
      _ , evc1 = eval env e
      dprim-in-small-env = eval (push ctg (push primal1 empty)) (dprim' op)
      lem1 : snd dprim-in-small-env - φd + φ (D2τ' σ) (fst (dprim-in-small-env)) ≤ + 14
      lem1 = dprim-cheap op primal1 ctg
      lem2 : dprim-in-small-env ≡ (dx , cdprim)
      lem2 = eval-sink-commute (push ctg (push primal1 empty)) subenv1 (WCopy (WCopy WCut)) (refl , refl , tt) (dprim' op)
      lem3 : cdprim - φd + φdx ≤ + 14
      lem3 = subst (\hole -> snd hole - φd + φ (D2τ' σ) (fst hole) ≤ + 14) lem2 lem1
      envlen = + length Γ
      k1 = th1 env dx denvin e
  in {- LEMMA -} lemma-prim crun1 cdprim ccall1 cmonad1 φdx φd φe1 φe2 evc1 lem3 envlen k1

th1 {Γ} env ctg denvin (fst' {σ = σ} {τ = τ} e) =
  let out1 , crun1 = eval (primalVal env) (chad e)
      primal1 , bp1 = out1
      subenv1 : Val Du (D2τ σ ∷ (D1τ (σ :* τ) :* (D2τ (σ :* τ) :-> D2Γ Γ)) ∷ [])
      subenv1 = push ctg (push out1 empty)
      zerores , czero = eval subenv1 (zerot τ)
      ctg1 = just (ctg , zerores)
      mf1 , ccall1 = bp1 ctg1
      tt , denv2 , cmonad1 = LACM.run mf1 denvin
      φd = φ (D2τ' σ) ctg
      φe1 = φ' (map D2τ' Γ) denvin
      φe2 = φ' (map D2τ' Γ) denv2
      φd1 = φ (D2τ' τ) zerores
      _ , evc1 = eval env e
      pzero : czero ≤ + 2
      pzero = zero-small-cost subenv1 τ
      pφd1 : φd1 ≡ + 1
      pφd1 = zero-small-φ subenv1 τ
      k1 = th1 env ctg1 denvin e
      envlen = + length Γ
  in {- LEMMA -} lemma-fst crun1 czero ccall1 cmonad1 φd φe1 φe2 φd1 evc1 pzero pφd1 envlen k1

th1 {Γ} env ctg denvin (snd' {σ = σ} {τ = τ} e) =
  let out1 , crun1 = eval (primalVal env) (chad e)
      primal1 , bp1 = out1
      subenv1 : Val Du (D2τ τ ∷ (D1τ (σ :* τ) :* (D2τ (σ :* τ) :-> D2Γ Γ)) ∷ [])
      subenv1 = push ctg (push out1 empty)
      zerores , czero = eval subenv1 (zerot σ)
      ctg1 = just (zerores , ctg)
      mf1 , ccall1 = bp1 ctg1
      tt , denv2 , cmonad1 = LACM.run mf1 denvin
      φd = φ (D2τ' τ) ctg
      φe1 = φ' (map D2τ' Γ) denvin
      φe2 = φ' (map D2τ' Γ) denv2
      φd1 = φ (D2τ' σ) zerores
      _ , evc1 = eval env e
      pzero : czero ≤ + 2
      pzero = zero-small-cost subenv1 σ
      pφd1 : φd1 ≡ + 1
      pφd1 = zero-small-φ subenv1 σ
      k1 = th1 env ctg1 denvin e
      envlen = + length Γ
  in {- LEMMA -} lemma-snd crun1 czero ccall1 cmonad1 φd φe1 φe2 φd1 evc1 pzero pφd1 envlen k1

th1 {Γ} env ctg@nothing denvin (inl {σ = σ} {τ = τ} e) =
  let out1 , crun1 = eval (primalVal env) (chad e)
      primal1 , bp1 = out1
      zerores , czero = zerov (D2τ' σ)
      mf1 , ccall1 = bp1 zerores
      tt , denv2 , cmonad1 = LACM.run mf1 denvin
      φe1 = φ' (map D2τ' Γ) denvin
      φe2 = φ' (map D2τ' Γ) denv2
      φd1 = φ (D2τ' σ) zerores
      _ , evc1 = eval env e
      pzero = zero-small-φ-v σ
      pφd1 = zero-small-cost-v σ
      k1 = th1 env zerores denvin e
      envlen = + length Γ
  in {- LEMMA -} lemma-inl-nothing crun1 czero ccall1 cmonad1 φe1 φe2 φd1 evc1 pzero pφd1 envlen k1

th1 {Γ} env ctg@(just (inj₁ ctg1)) denvin (inl {σ = σ} {τ = τ} e) =
  let out1 , crun1 = eval (primalVal env) (chad e)
      primal1 , bp1 = out1
      mf1 , ccall1 = bp1 ctg1
      tt , denv2 , cmonad1 = LACM.run mf1 denvin
      φe1 = φ' (map D2τ' Γ) denvin
      φe2 = φ' (map D2τ' Γ) denv2
      φd1 = φ (D2τ' σ) ctg1
      _ , evc1 = eval env e
      k1 = th1 env ctg1 denvin e
      envlen = + length Γ
  in {- LEMMA -} lemma-inl-inj1 crun1 ccall1 cmonad1 φe1 φe2 φd1 evc1 envlen k1

th1 {Γ} env ctg@(just (inj₂ ctg2)) denvin (inl {σ = σ} {τ = τ} e) =
  let out1 , crun1 = eval (primalVal env) (chad e)
      primal1 , bp1 = out1
      zerores , czero = zerov (D2τ' σ)
      mf1 , ccall1 = bp1 zerores
      tt , denv2 , cmonad1 = LACM.run mf1 denvin
      φe1 = φ' (map D2τ' Γ) denvin
      φe2 = φ' (map D2τ' Γ) denv2
      φd1 = φ (D2τ' σ) zerores
      φd2 = φ (D2τ' τ) ctg2
      _ , evc1 = eval env e
      pzero = zero-small-φ-v σ
      pφd1 = zero-small-cost-v σ
      pφd2 = φ-positive (D2τ' τ) ctg2
      sym-φd2 : - φd2 ≤ - φd2
      sym-φd2 = ≤-reflexive refl
      k1 = th1 env zerores denvin e
      envlen = + length Γ
  in {- LEMMA -} lemma-inl-inj2 crun1 czero ccall1 cmonad1 φe1 φe2 φd1 φd2 evc1 pzero pφd1 pφd2 sym-φd2 envlen k1

th1 {Γ} env ctg@nothing denvin (inr {σ = σ} {τ = τ} e) =
  let out1 , crun1 = eval (primalVal env) (chad e)
      primal1 , bp1 = out1
      zerores , czero = zerov (D2τ' τ)
      mf1 , ccall1 = bp1 zerores
      tt , denv2 , cmonad1 = LACM.run mf1 denvin
      φe1 = φ' (map D2τ' Γ) denvin
      φe2 = φ' (map D2τ' Γ) denv2
      φd1 = φ (D2τ' τ) zerores
      _ , evc1 = eval env e
      pzero = zero-small-φ-v τ
      pφd1 = zero-small-cost-v τ
      k1 = th1 env zerores denvin e
      envlen = + length Γ
  in {- LEMMA -} lemma-inl-nothing crun1 czero ccall1 cmonad1 φe1 φe2 φd1 evc1 pzero pφd1 envlen k1

th1 {Γ} env ctg@(just (inj₂ ctg1)) denvin (inr {σ = σ} {τ = τ} e) =
  let out1 , crun1 = eval (primalVal env) (chad e)
      primal1 , bp1 = out1
      mf1 , ccall1 = bp1 ctg1
      tt , denv2 , cmonad1 = LACM.run mf1 denvin
      φe1 = φ' (map D2τ' Γ) denvin
      φe2 = φ' (map D2τ' Γ) denv2
      φd1 = φ (D2τ' τ) ctg1
      _ , evc1 = eval env e
      k1 = th1 env ctg1 denvin e
      envlen = + length Γ
  in {- LEMMA -} lemma-inl-inj1 crun1 ccall1 cmonad1 φe1 φe2 φd1 evc1 envlen k1

th1 {Γ} env ctg@(just (inj₁ ctg2)) denvin (inr {σ = σ} {τ = τ} e) =
  let out1 , crun1 = eval (primalVal env) (chad e)
      primal1 , bp1 = out1
      zerores , czero = zerov (D2τ' τ)
      mf1 , ccall1 = bp1 zerores
      tt , denv2 , cmonad1 = LACM.run mf1 denvin
      φe1 = φ' (map D2τ' Γ) denvin
      φe2 = φ' (map D2τ' Γ) denv2
      φd1 = φ (D2τ' τ) zerores
      φd2 = φ (D2τ' σ) ctg2
      _ , evc1 = eval env e
      pzero = zero-small-φ-v τ
      pφd1 = zero-small-cost-v τ
      pφd2 = φ-positive (D2τ' σ) ctg2
      sym-φd2 : - φd2 ≤ - φd2
      sym-φd2 = ≤-reflexive refl
      k1 = th1 env zerores denvin e
      envlen = + length Γ
  in {- LEMMA -} lemma-inl-inj2 crun1 czero ccall1 cmonad1 φe1 φe2 φd1 φd2 evc1 pzero pφd1 pφd2 sym-φd2 envlen k1

th1 {Γ} env ctg denvin (case' {σ = σ} {τ = τ} {ρ = ρ} e1 e2 e3)
  rewrite chad-preserves-primal env e1
  with eval env e1 in eq
... | inj₁ x , evc1 rewrite eq =  -- why do we need to rewrite twice?
  let out1 , crun1 = eval (primalVal env) (chad e1)
      primal1 , bp1 = out1
      primal1' = primal σ x
      subenv1 : Val Du (D1τ σ ∷ (D1τ (σ :+ τ) :* (D2τ (σ :+ τ) :-> D2Γ Γ)) ∷ D1Γ Γ)
      subenv1 = push primal1' (push out1 (primalVal env))
      chade2res = eval subenv1 (sink (WCopy (WSkip WEnd)) (chad e2))
      out2 , crun2 = chade2res
      primal2 , bp2 = out2
      subenv2 : Val Du (D2τ ρ ∷ (D1τ ρ :* (D2τ ρ :-> D2Γ (σ ∷ Γ))) ∷ (D1τ (σ :+ τ) :* (D2τ (σ :+ τ) :-> D2Γ Γ)) ∷ [])
      subenv2 = push ctg (push out2 (push out1 empty))
      zerores , czero = eval subenv2 (zerot σ)
      mf2 , ccall2 = bp2 ctg
      (dx , tt) , denv2-B , cmonad2-B = LACM.run (LACM.scope zerores mf2) denvin
      mf1 , ccall1 = bp1 (just (inj₁ dx))
      tt , denvout-B , cmonad1-B = LACM.run mf1 denv2-B
      tt , denv2-A , cmonad-A = LACM.run (LACM.bind (LACM.scope zerores mf2) (λ dx' → fst (bp1 (just (inj₁ (fst dx')))) , + 6 + snd (bp1 (just (inj₁ (fst dx')))))) denvin
      _ , evc2 = eval (push x env) e2
      envlen = + length Γ
      φd = φ (D2τ' ρ) ctg
      φdx = φ (D2τ' σ) dx
      φenvin = φ' (map D2τ' Γ) denvin
      φdenv2-A = φ' (map D2τ' Γ) denv2-A
      φdenv2-B = φ' (map D2τ' Γ) denv2-B
      φdenvout-B = φ' (map D2τ' Γ) denvout-B
      φzero = φ (D2τ' σ) zerores

      chade2res-X = eval (push primal1' (primalVal env)) (chad e2)
      out2-X , crun2-X = chade2res-X
      primal2-X , bp2-X = out2-X
      mf2-X , ccall2-X = bp2-X ctg
      tt , (dx-X , denv2-X) , cmonad2-X = LACM.run mf2-X (zerores , denvin)
      φdx-X = φ (D2τ' σ) dx-X
      φdenv2-X = φ' (map D2τ' Γ) denv2-X

      pX : chade2res ≡ chade2res-X
      pX = sym (eval-sink-commute (push primal1' (primalVal env)) subenv1 (WCopy (WSkip WEnd)) (refl , forall-fin-trivial (\_ -> refl)) (chad e2))

      eq-crun2 : crun2 ≡ crun2-X
      eq-crun2 = cong snd pX
      eq-ccall2 : ccall2 ≡ ccall2-X
      eq-ccall2 = cong (\res -> snd (snd (fst res) ctg)) pX
      eq-mf2 : mf2 ≡ mf2-X
      eq-mf2 = cong (\res -> fst (snd (fst res) ctg)) pX

      pScope : (tt ≡ tt) × (dx ≡ dx-X) × (denv2-B ≡ denv2-X) × (cmonad2-B ≡ cmonad2-X)
      pScope = run-scope2 mf2 mf2-X eq-mf2 zerores denvin

      eq-cmonad2 : cmonad2-B ≡ cmonad2-X
      eq-cmonad2 = snd (snd (snd pScope))
      eq-dx : dx ≡ dx-X
      eq-dx = fst (snd pScope)
      eq-φdx : φdx ≡ φdx-X
      eq-φdx = cong (φ (D2τ' σ)) eq-dx
      eq-φdenv2 : φdenv2-B ≡ φdenv2-X
      eq-φdenv2 = cong (φ' (map D2τ' Γ)) (fst (snd (snd pScope)))

      runbindres : (denv2-A ≡ denvout-B) × (cmonad-A ≡ cmonad2-B + (+ 6 + ccall1) + cmonad1-B - envlen)
      runbindres = run-bind2 (LACM.scope zerores mf2) (λ dx' → fst (bp1 (just (inj₁ (fst dx')))) , + 6 + snd (bp1 (just (inj₁ (fst dx'))))) denvin
      runbindres1 : denv2-A ≡ denvout-B
      runbindres1 = fst runbindres
      runbindres2 : cmonad-A ≡ cmonad2-B + (+ 6 + ccall1) + cmonad1-B - envlen
      runbindres2 = snd runbindres

      eq-φdenv2out : φdenv2-A ≡ φdenvout-B
      eq-φdenv2out = cong (φ' (map D2τ' Γ)) runbindres1

      pczero : czero ≤ + 2
      pczero = zero-small-cost subenv2 σ
      pφzero : φzero ≡ + 1
      pφzero = zero-small-φ subenv2 σ

      k1 : crun1 + ccall1 + cmonad1-B + - (+ 1 + φdx) + - φdenv2-B + φdenvout-B + - envlen ≤ + 31 * evc1
      k1 = subst (\hole -> crun1 + ccall1 + cmonad1-B + - (+ 1 + φdx) + - φdenv2-B + φdenvout-B + - envlen ≤ + 31 * snd hole) eq (th1 env (just (inj₁ dx)) denv2-B e1)
      k2 = th1 (push x env) ctg (zerores , denvin) e2
      answer : 
        + 1 + crun1 + (+ 3 + (one + crun2 + + 6)) + (one + (one + czero + (+ 4 + ccall2)) + + 2)
          + cmonad-A - φd - φenvin + φdenv2-A - envlen
          ≤ + 31 * (one + evc1 + evc2)
      answer =
        {- LEMMA -} lemma-case-1 evc1 crun1 crun2 czero ccall2 cmonad2-B ccall1 cmonad1-B cmonad-A evc2 envlen φd φdx φenvin φdenv2-A φdenv2-B φdenvout-B φzero crun2-X ccall2-X cmonad2-X φdx-X φdenv2-X eq-crun2 eq-ccall2 eq-cmonad2 eq-φdx eq-φdenv2 runbindres2 eq-φdenv2out pczero pφzero k1 k2
  in answer
... | inj₂ y , evc1 rewrite eq =
  let out1 , crun1 = eval (primalVal env) (chad e1)
      primal1 , bp1 = out1
      primal1' = primal τ y
      subenv1 : Val Du (D1τ τ ∷ (D1τ (σ :+ τ) :* (D2τ (σ :+ τ) :-> D2Γ Γ)) ∷ D1Γ Γ)
      subenv1 = push primal1' (push out1 (primalVal env))
      chade3res = eval subenv1 (sink (WCopy (WSkip WEnd)) (chad e3))
      out3 , crun3 = chade3res
      primal3 , bp3 = out3
      subenv2 : Val Du (D2τ ρ ∷ (D1τ ρ :* (D2τ ρ :-> D2Γ (τ ∷ Γ))) ∷ (D1τ (σ :+ τ) :* (D2τ (σ :+ τ) :-> D2Γ Γ)) ∷ [])
      subenv2 = push ctg (push out3 (push out1 empty))
      zerores , czero = eval subenv2 (zerot τ)
      mf3 , ccall3 = bp3 ctg
      (dy , tt) , denv3-B , cmonad3-B = LACM.run (LACM.scope zerores mf3) denvin
      mf1 , ccall1 = bp1 (just (inj₂ dy))
      tt , denvout-B , cmonad1-B = LACM.run mf1 denv3-B
      tt , denv3-A , cmonad-A = LACM.run (LACM.bind (LACM.scope zerores mf3) (λ dy' → fst (bp1 (just (inj₂ (fst dy')))) , + 6 + snd (bp1 (just (inj₂ (fst dy')))))) denvin
      _ , evc3 = eval (push y env) e3
      envlen = + length Γ
      φd = φ (D2τ' ρ) ctg
      φdy = φ (D2τ' τ) dy
      φenvin = φ' (map D2τ' Γ) denvin
      φdenv3-A = φ' (map D2τ' Γ) denv3-A
      φdenv3-B = φ' (map D2τ' Γ) denv3-B
      φdenvout-B = φ' (map D2τ' Γ) denvout-B
      φzero = φ (D2τ' τ) zerores

      chade3res-X = eval (push primal1' (primalVal env)) (chad e3)
      out3-X , crun3-X = chade3res-X
      primal3-X , bp3-X = out3-X
      mf3-X , ccall3-X = bp3-X ctg
      tt , (dy-X , denv3-X) , cmonad3-X = LACM.run mf3-X (zerores , denvin)
      φdy-X = φ (D2τ' τ) dy-X
      φdenv3-X = φ' (map D2τ' Γ) denv3-X

      pX : chade3res ≡ chade3res-X
      pX = sym (eval-sink-commute (push primal1' (primalVal env)) subenv1 (WCopy (WSkip WEnd)) (refl , forall-fin-trivial (\_ -> refl)) (chad e3))

      eq-crun3 : crun3 ≡ crun3-X
      eq-crun3 = cong snd pX
      eq-ccall3 : ccall3 ≡ ccall3-X
      eq-ccall3 = cong (\res -> snd (snd (fst res) ctg)) pX
      eq-mf3 : mf3 ≡ mf3-X
      eq-mf3 = cong (\res -> fst (snd (fst res) ctg)) pX

      pScope : (tt ≡ tt) × (dy ≡ dy-X) × (denv3-B ≡ denv3-X) × (cmonad3-B ≡ cmonad3-X)
      pScope = run-scope2 mf3 mf3-X eq-mf3 zerores denvin

      eq-cmonad3 : cmonad3-B ≡ cmonad3-X
      eq-cmonad3 = snd (snd (snd pScope))
      eq-dy : dy ≡ dy-X
      eq-dy = fst (snd pScope)
      eq-φdy : φdy ≡ φdy-X
      eq-φdy = cong (φ (D2τ' τ)) eq-dy
      eq-φdenv3 : φdenv3-B ≡ φdenv3-X
      eq-φdenv3 = cong (φ' (map D2τ' Γ)) (fst (snd (snd pScope)))

      runbindres : (denv3-A ≡ denvout-B) × (cmonad-A ≡ cmonad3-B + (+ 6 + ccall1) + cmonad1-B - envlen)
      runbindres = run-bind2 (LACM.scope zerores mf3) (λ dy' → fst (bp1 (just (inj₂ (fst dy')))) , + 6 + snd (bp1 (just (inj₂ (fst dy'))))) denvin
      runbindres1 : denv3-A ≡ denvout-B
      runbindres1 = fst runbindres
      runbindres2 : cmonad-A ≡ cmonad3-B + (+ 6 + ccall1) + cmonad1-B - envlen
      runbindres2 = snd runbindres

      eq-φdenv3out : φdenv3-A ≡ φdenvout-B
      eq-φdenv3out = cong (φ' (map D2τ' Γ)) runbindres1

      pczero : czero ≤ + 2
      pczero = zero-small-cost subenv2 τ
      pφzero : φzero ≡ + 1
      pφzero = zero-small-φ subenv2 τ

      k1 : crun1 + ccall1 + cmonad1-B + - (+ 1 + φdy) + - φdenv3-B + φdenvout-B + - envlen ≤ + 31 * evc1
      k1 = subst (\hole -> crun1 + ccall1 + cmonad1-B + - (+ 1 + φdy) + - φdenv3-B + φdenvout-B + - envlen ≤ + 31 * snd hole) eq (th1 env (just (inj₂ dy)) denv3-B e1)
      k2 = th1 (push y env) ctg (zerores , denvin) e3
      answer : 
        + 1 + crun1 + (+ 3 + (one + crun3 + + 6)) + (one + (one + czero + (+ 4 + ccall3)) + + 2)
          + cmonad-A - φd - φenvin + φdenv3-A - envlen
          ≤ + 31 * (one + evc1 + evc3)
      answer =
        {- LEMMA -} lemma-case-1 evc1 crun1 crun3 czero ccall3 cmonad3-B ccall1 cmonad1-B cmonad-A evc3 envlen φd φdy φenvin φdenv3-A φdenv3-B φdenvout-B φzero crun3-X ccall3-X cmonad3-X φdy-X φdenv3-X eq-crun3 eq-ccall3 eq-cmonad3 eq-φdy eq-φdenv3 runbindres2 eq-φdenv3out pczero pφzero k1 k2
  in answer

φ-less-size : (τ : Typ Pr) -> (x : LinRep (D2τ' τ)) -> φ (D2τ' τ) x ≤ + size (D2τ' τ) x
φ-less-size Un tt = ≤ᵇ⇒≤ tt
φ-less-size Inte tt = ≤ᵇ⇒≤ tt
φ-less-size R _ = ≤ᵇ⇒≤ tt
φ-less-size (σ :* τ) nothing = +≤+ (s≤s z≤n)
φ-less-size (σ :* τ) (just (x , y)) =
  let k1 = φ-less-size σ x
      k2 = φ-less-size τ y
      φx = φ (D2τ' σ) x
      φy = φ (D2τ' τ) y
      sσ = + size (D2τ' σ) x
      sτ = + size (D2τ' τ) y
  in lemma-φ-less-size φx φy sσ k1 sτ k2
φ-less-size (σ :+ τ) nothing = +≤+ (s≤s z≤n)
φ-less-size (σ :+ τ) (just (inj₁ x)) = +-mono-≤ (+≤+ (s≤s z≤n)) (φ-less-size σ x)
φ-less-size (σ :+ τ) (just (inj₂ y)) = +-mono-≤ (+≤+ (s≤s z≤n)) (φ-less-size τ y)

φ-zero-bound : (τ : LTyp) -> (x : LinRep τ) -> φ τ (fst (zerov τ)) ≤ φ τ x
φ-zero-bound LUn .tt = +≤+ (s≤s z≤n)
φ-zero-bound LR _ = +≤+ (s≤s z≤n)
φ-zero-bound (σ :*! τ) nothing = +≤+ (s≤s z≤n)
φ-zero-bound (σ :*! τ) (just (x , y)) =
  +-mono-≤ (+-mono-≤ (+≤+ (s≤s z≤n)) (φ-positive σ x)) (φ-positive τ y)
φ-zero-bound (σ :+! τ) nothing = +≤+ (s≤s z≤n)
φ-zero-bound (σ :+! τ) (just (inj₁ x)) = +-mono-≤ (+≤+ (s≤s z≤n)) (φ-positive σ x)
φ-zero-bound (σ :+! τ) (just (inj₂ y)) = +-mono-≤ (+≤+ (s≤s z≤n)) (φ-positive τ y)

φ-zerot-bound : {Γ : Env Du} {env : Val Du Γ} -> (τ : Typ Pr) -> (x : LinRep (D2τ' τ)) -> φ (D2τ' τ) (fst (eval env (zerot τ))) ≤ φ (D2τ' τ) x
φ-zerot-bound Un .tt = +≤+ (s≤s z≤n)
φ-zerot-bound Inte .tt = +≤+ (s≤s z≤n)
φ-zerot-bound R _ = +≤+ (s≤s z≤n)
φ-zerot-bound (σ :* τ) nothing = +≤+ (s≤s z≤n)
φ-zerot-bound (σ :* τ) (just (x , y)) =
  +-mono-≤ (+-mono-≤ (+≤+ (s≤s z≤n)) (φ-positive (D2τ' σ) x)) (φ-positive (D2τ' τ) y)
φ-zerot-bound (σ :+ τ) nothing = +≤+ (s≤s z≤n)
φ-zerot-bound (σ :+ τ) (just (inj₁ x)) = +-mono-≤ (+≤+ (s≤s z≤n)) (φ-positive (D2τ' σ) x)
φ-zerot-bound (σ :+ τ) (just (inj₂ y)) = +-mono-≤ (+≤+ (s≤s z≤n)) (φ-positive (D2τ' τ) y)

φ-zero-env-bound : {Γ' : Env Du} {env : Val Du Γ'}
                -> (Γ : Env Pr) -> (tup : LEtup (map D2τ' Γ))
                -> φ' (map D2τ' Γ) (LEtup-to-LEτ (map D2τ' Γ) (fst (eval env (zero-env-term Γ))))
                   ≤ φ' (map D2τ' Γ) tup
φ-zero-env-bound [] .tt = +≤+ z≤n
φ-zero-env-bound (τ ∷ Γ) (x , tup) = +-mono-≤ (φ-zerot-bound τ x) (φ-zero-env-bound Γ tup)

th2 : TH2-STATEMENT
th2 {Γ} {τ} env ctg t =
  let -- definitions
      φd = φ (D2τ' τ) ctg
      envlen = + length Γ

      env1 : Val Du (D2τ τ ∷ D1Γ Γ)
      env1 = push ctg (primalVal env)
      zeroenv , czeroenv = eval env1 (zero-env-term Γ)
      denvin = LEtup-to-LEτ (map D2τ' Γ) zeroenv
      φdenvin = φ' (map D2τ' Γ) denvin

      -- world 1: sunk
      evalres1 = eval env1 (sink (WSkip WEnd) (chad t))
      (primal1 , bp1) , crun1 = evalres1
      mf1 , ccall1 = bp1 ctg
      tt , denvout1 , cmonad1 = LACM.run mf1 denvin

      -- world 2: non-sunk
      evalres2 = eval (primalVal env) (chad t)
      (primal2 , bp2) , crun2 = evalres2
      mf2 , ccall2 = bp2 ctg
      tt , denvout2 , cmonad2 = LACM.run mf2 denvin
      φdenvout2 = φ' (map D2τ' Γ) denvout2

      -- linking the worlds
      eq-evalres : evalres1 ≡ evalres2
      eq-evalres = sym (eval-sink-commute (primalVal env) env1 (WSkip WEnd) (forall-fin-trivial (\i -> refl)) (chad t))
      eq-crun : crun1 ≡ crun2
      eq-crun = cong snd eq-evalres
      eq-ccall : ccall1 ≡ ccall2
      eq-ccall = cong (\evalres -> snd (snd (fst evalres) ctg)) eq-evalres
      eq-cmonad : cmonad1 ≡ cmonad2
      eq-cmonad = cong (\evalres -> snd (snd (LACM.run (fst (snd (fst evalres) ctg)) denvin))) eq-evalres

      bound-φd : φd ≤ + size (D2τ' τ) ctg
      bound-φd = φ-less-size τ ctg
      bound-φenv : φdenvin ≤ φdenvout2
      bound-φenv = φ-zero-env-bound Γ denvout2
      bound-czeroenv : czeroenv ≤ + 1 + + 3 * envlen
      bound-czeroenv = zero-env-small-cost env1 Γ

      sym-φdenvout2 : - φdenvout2 ≤ - φdenvout2
      sym-φdenvout2 = ≤-reflexive refl
      sym-result : + 4 + envlen ≤ + 4 + envlen
      sym-result = ≤-reflexive refl

      primal-cost = cost env t
      codom-size = + size (D2τ' τ) ctg

      k1 : crun2 + ccall2 + cmonad2 - φd - φdenvin + φdenvout2 - envlen ≤ + 31 * primal-cost
      k1 = th1 env ctg denvin t

      answer : + 1 + (+ 1 + (+ 1 + crun1) + + 1 + ccall1) + czeroenv + cmonad1
               ≤ + 5 + + 31 * primal-cost + codom-size + + 4 * envlen
      answer = {- LEMMA -} lemma-th2 φd envlen czeroenv φdenvin crun1 ccall1 cmonad1 crun2 ccall2 cmonad2 φdenvout2 eq-crun eq-ccall eq-cmonad bound-φenv bound-czeroenv sym-φdenvout2 sym-result primal-cost codom-size bound-φd k1
  in answer
