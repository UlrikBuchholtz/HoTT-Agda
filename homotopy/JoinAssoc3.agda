{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.JoinFunc

-- Associativity of the join (work in progress)

module homotopy.JoinAssoc3 where

 import homotopy.JoinAssoc as Assoc

 module JoinAssoc3 {i} (A : Type i) (B : Type i) (C : Type i) where
  
  module A31 = Assoc A B C
  postulate
--    from : ((A * B) * C) → (A * (B * C))
--    to : (A * (B * C)) → ((A * B) * C)
    to-from : (z : (A * (B * C))) → (A31.to (A31.from z)) == z
  
  from = A31.from
  to = A31.to

  idc : C → C
  idc c = c
  ida : A → A
  ida a = a

--  import homotopy.JoinComm as JoinComm
--  open JoinComm

--  from' : ((A * B) * C) → (A * (B * C))
--  from' z =  {! swap $  swap ** ida [ to $ swap $ swap ** idc [ z ] ] !}

 module _  {i} {A : Type i} {B : Type i} {C : Type i} where
  
  import homotopy.JoinComm as JoinComm
  open JoinComm

  module JA31 = JoinAssoc3 A B C
  module JA32 = JoinAssoc3 C B A
  module JA33 = JoinAssoc3 B A C
  idc : C → C
  idc c = c
  ida : A → A
  ida a = a

  -- need A * (B * C)
  from-to : (z : ((A * B) * C)) -> (JA31.from (JA31.to z)) == z
  from-to z with  JA31.to z -- idc ** swap [ {! swap $ swap ** idc [ z ]!} ] --JA32.to $ swap $ swap ** idc [ z ] ]
  ... | p = {!JA31.to-from p!} -- JA31.from-to p
