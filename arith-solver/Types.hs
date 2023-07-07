{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
module Types where


data Dict c a where
  Dict :: c a => Dict c a
