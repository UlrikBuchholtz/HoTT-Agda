{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.S1SuspensionS0 where

{- To -}

module To = S¹Rec (north Bool) (merid _ false ∙ ! (merid _ true))

to : S¹ → Suspension Bool
to = To.f

{- From -}

from-merid : Bool → base == base
from-merid true = loop
from-merid false = idp

module From = SuspensionRec Bool base base from-merid

from : Suspension Bool → S¹
from = From.f

{- ToFrom and FromTo -}

--postulate  -- TODO, easy and boring
--  to-from : (x : Suspension Bool) → to (from x) == x
--  from-to : (x : S¹) → from (to x) == x


--module SuspensionElim {j} {P : Suspension → Type j} (n : P north) (s : P south)
--  (p : (x : A) → n == s [ P ↓ merid x ])
--  = PushoutElim (λ _ → n) (λ _ → s) p

--module Ind = SuspensionElim (λ (x : Suspension Bool) → to (from x) == x) ? ?

--((ap to (ap from (merid _ false)))  ∙ (merid _ false)) ((ap to (ap from (merid _ true)))  ∙ (merid _ true))

--to-from : (x : Suspension Bool) → to (from x) == x
--to-from x = {! (ap to (ap from (merid _ false)))  ∙ (merid _ false)!}


-- _=⟨_⟩_ : ∀ {i} {A : Type i} (x : A) {y z : A} → x == y → y == z → x == z

{-
from-to : (x : S¹) → from (to x) == x
from-to = {! S¹-elim idp  (↓-∘=idf-in from to 
        (ap from (ap to loop)                      =⟨ ∙-unit-r loop ⟩ 
        loop ∙ idp                                 =⟨ ∙-unit-r loop ⟩ 
        loop ∎))
!}
-}
--to-from  : (x : Suspension Bool) → to (from x) == x
--to-from = Suspension-elim Bool idp idp 

module Bla {i}  {A : Type i} where 
  ∙idp∙ : {x y z : A} (p : x == y) (q : y == z) → p ∙ idp ∙ q == p ∙ q
  ∙idp∙ idp idp = idp
  p∙!q∙q : {x y z : A} (p : x == y) (q : z == y) → p ∙ ( ! q ∙ q)  == p
  p∙!q∙q idp idp = idp
  !-∙∙ :  {x y z w : A} (p : x == y) (q : y == z) (r : x == w) →  ! (p ∙ q) ∙ r == (! q ∙ ! p ) ∙ r
  !-∙∙ idp idp idp = idp
  ∙-unit-l :  {x y : A} (p : x == y) → idp ∙ p == p
  ∙-unit-l idp = idp 


to-from-merid' :  ( ! (ap to (ap from (merid Bool true)))) ∙ idp ∙ merid Bool true ==  (merid Bool true)
to-from-merid'  = ! (ap to (ap from (merid Bool true))) ∙ idp ∙ merid Bool true              =⟨ Bla.∙idp∙ ( ! (ap to (ap from (merid Bool true))))  (merid Bool true)  ⟩
                       ! (ap to (ap from (merid Bool true))) ∙ merid Bool true               =⟨ idp ⟩
                       ! (ap to idp) ∙ merid Bool true                                       =⟨ idp ⟩
                       ! idp ∙ merid Bool true                                               =⟨ idp ⟩
                       idp ∙ merid Bool true                                               =⟨  Bla.∙-unit-l _ ⟩
                       (merid Bool true ∎)
{-
                       ! (ap to idp) ∙ merid Bool true                                       =⟨ idp ⟩
                       ! (merid Bool false ∙ ! (merid Bool true)) ∙ merid Bool true          =⟨ Bla.!-∙∙ (merid Bool false)  (! (merid Bool true)) (merid Bool true)   ⟩
                       (! (! (merid Bool true)) ∙ ! (merid Bool false)) ∙ merid Bool true    =⟨ ∙-assoc (! (! (merid Bool true)))  (! (merid Bool false))  (merid Bool true) ⟩
                       ! (! (merid Bool true)) ∙ (! (merid Bool false) ∙ merid Bool true)    =⟨ {!!} ⟩
                       ! (! (merid Bool true))                                               =⟨ !-!  (merid Bool true) ⟩ 
                       (merid Bool true ∎)
-}

--  ap to (ap from (merid true)) ?
--to-from-merid' false = ?
  
--to-from-merid : (a : Bool) → idp == idp [ (λ z → to (from z) == z) ↓ merid _ a ]
--to-from-merid a = ↓-∘=idf-in from to ? -- (from-to-merid' a)
{-
from-to x =  S¹-elim idp (↓-∘=idf-in to from 
      (ap from (ap to loop)                      =⟨ To.loop-β |in-ctx ap from ⟩ --  =⟨ From.glue-β |in-ctx ap to ⟩
      ?
      ap to (ppt tt true ∙ ppt tt false)         =⟨ ap-∙ to (ppt tt true) (ppt tt false) ⟩
      ap to (ppt tt true) ∙ ap to (ppt tt false) =⟨ To.pp-β (tt , true) |in-ctx (λ u → u ∙ ap to (ppt tt false)) ⟩
      loop ∙ ap to (ppt tt false)                =⟨ To.pp-β (tt , false) |in-ctx (λ u → loop ∙ u) ⟩
      loop ∙ idp                                 =⟨ ∙-unit-r loop ⟩ 
      loop ∎)) -}



--e : S¹ ≃ Suspension Bool
--e = equiv to from to-from from-to
