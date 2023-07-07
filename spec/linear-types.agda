module spec.linear-types where

open import Agda.Builtin.Float using (Float; primFloatPlus)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)

open import Data.List using (List; []; _∷_)
open import Data.Integer using (ℤ; _+_; +_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)


-- The linear (i.e. monoidal) types. These types have a monoid structure, and
-- have a potential function (φ) defined on them.
data LTyp : Set where
  LUn LR : LTyp
  _:*!_ : LTyp -> LTyp -> LTyp
  _:+!_ : LTyp -> LTyp -> LTyp

-- A linear typing environment is a list of linear types.
LEnv : Set
LEnv = List LTyp

-- The representation (semantics) of the linear types; the representation of
-- normal types follows in `spec.agda`.
LinRep : LTyp -> Set
LinRep LUn = ⊤
LinRep LR = Float
LinRep (σ :*! τ) = Maybe (LinRep σ × LinRep τ)
LinRep (σ :+! τ) = Maybe (LinRep σ ⊎ LinRep τ)

-- Linear environment tuple: a tuple of all the types in a linear environment.
-- This is used to pass a linear environment as a _value_ into, and out of,
-- the monadic computation in the target program.
LEtup : LEnv -> Set
LEtup [] = ⊤
LEtup (τ ∷ Γ) = LinRep τ × LEtup Γ

-- An index into a typing environment
data Idx {n} {typ : Set n} : List typ -> typ -> Set n where
  Z : {e : List typ} {τ : typ} -> Idx (τ ∷ e) τ
  S : {e : List typ} {τ τ' : typ} -> Idx e τ -> Idx (τ' ∷ e) τ

one : ℤ
one = + 1

-- The zero part of the monoid structure of the linear types. Aside from
-- returning the value, this also returns an integer recording the number of
-- evaluation steps taken during the operation. This integer is used for
-- complexity analysis.
-- Because zerov and plusv are not implemented in terms of evaluation of terms,
-- we simply use an approximation here that is proportional to the actual
-- number of steps. In practice this means that we can take c_φ = 1.
zerov : (τ : LTyp) -> LinRep τ × ℤ
zerov LUn = tt , one
zerov LR = 0.0 , one
zerov (σ :*! τ) = nothing , one
zerov (σ :+! τ) = nothing , one

-- The addition part of the monoid structure of the linear types. Similarly,
-- the number of evaluation steps is returned.
--
-- For sum types, we return zero on adding incompatible values instead of
-- throwing an error. This prevents D2τ (σ :+ τ) from being a monoid, but of
-- course, if a proper implementation that would throw errors does not in fact
-- error on a given input program, the implementation here would not introduce
-- values that violate the monoid laws either.
--
-- In particular, because the dependently-typed variant of CHAD is correct (see
-- Nunes, Vákár. "CHAD for expressive total languages." MSCS 2023 (to appear)
-- (also arXiv:2110.00446)), there is an external proof that those error cases
-- would be impossible, and thus that the cases that violate the monoid laws
-- here are also impossible.
--
-- We put up with this infelicity because it allows us to avoid having to model
-- partiality in our language, which is no fundamental issue but introduces a
-- large amount of administration everywhere that makes the proof harder to
-- read and to write.
plusv : (τ : LTyp) -> LinRep τ -> LinRep τ -> LinRep τ × ℤ
plusv LUn tt tt = tt , one
plusv LR x y = primFloatPlus x y , one
plusv (σ :*! τ) nothing y = y , one
plusv (σ :*! τ) x nothing = x , one
plusv (σ :*! τ) (just (x , y)) (just (x' , y')) =
  let xr , cx = plusv σ x x'
      yr , cy = plusv τ y y'
  in just (xr , yr) , one + cx + cy
plusv (σ :+! τ) x nothing = x , one
plusv (σ :+! τ) nothing y = y , one
plusv (σ :+! τ) (just (inj₁ x)) (just (inj₁ y)) =
  let z , cz = plusv σ x y
  in just (inj₁ z) , one + cz
plusv (σ :+! τ) (just (inj₂ x)) (just (inj₂ y)) =
  let z , cz = plusv τ x y
  in just (inj₂ z) , one + cz
plusv (σ :+! τ) _ _ = nothing , one  -- NOTE: a proper implementation would error here.

-- Add the value 'val' into the position 'idx' in the environment tuple.
addLEτ : {Γ : LEnv} {τ : LTyp} -> (idx : Idx Γ τ) -> (val : LinRep τ) -> LEtup Γ -> LEtup Γ
addLEτ Z val (x , env) = fst (plusv _ val x) , env
addLEτ (S i) val (x , env) = x , addLEτ i val env

-- Project a value out of an environment tuple.
_Eτ!!_ : {Γ : LEnv} {τ : LTyp} -> LEtup Γ -> Idx Γ τ -> LinRep τ
(x , env) Eτ!! Z = x
(x , env) Eτ!! (S i) = env Eτ!! i
