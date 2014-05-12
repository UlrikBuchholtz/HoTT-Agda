{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.JoinFunc

-- Associativity of the join (work in progress)

module homotopy.JoinAssoc3 where

 module JoinAssoc3 {i} (A : Type i) (B : Type i) (C : Type i) where
  
  postulate
    from : ((A * B) * C) → (A * (B * C))
    to : (A * (B * C)) → ((A * B) * C)
    from-to : (z : (A * (B * C))) → (from (to z)) == z

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

  module JA31 = JoinAssoc3  A B C
  module JA32 = JoinAssoc3 C B A
  module JA33 = JoinAssoc3 B A C
  idc : C → C
  idc c = c
  ida : A → A
  ida a = a

  -- need A * (B * C)
  to-from : (z : ((A * B) * C)) -> (JA31.to (JA31.from z)) == z
  to-from z with  swap $  swap ** ida [ JA32.to $ swap $ swap ** idc [ z ] ]
  ... | p = {!JA31.from-to p!} -- JA31.from-to p
