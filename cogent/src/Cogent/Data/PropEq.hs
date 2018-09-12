
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

module Cogent.Data.PropEq where

data (:=:) :: k -> k -> * where
    Refl :: a :=: a

sym :: a :=: b -> b :=: a
sym Refl = Refl
