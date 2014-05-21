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

-- postulate  -- TODO, easy and boring
--to-from : (x : Suspension Bool) → to (from x) == x
--from-to : (x : S¹) → from (to x) == x

module Bla {i}  {A : Type i} where
  ∙idp∙ : {x y z : A} (p : x == y) (q : y == z) → p ∙ idp ∙ q == p ∙ q
  ∙idp∙ idp idp = idp
  p∙!q∙q : {x y z : A} (p : x == y) (q : z == y) → p ∙ ( ! q ∙ q)  == p
  p∙!q∙q idp idp = idp
  !-∙∙ :  {x y z w : A} (p : x == y) (q : y == z) (r : x == w) →  ! (p ∙ q) ∙ r == (! q ∙ ! p ) ∙ r
  !-∙∙ idp idp idp = idp
  ∙-unit-l :  {x y : A} (p : x == y) → idp ∙ p == p
  ∙-unit-l idp = idp
  ∙-coh-l : {x y z : A} {p p' : x == y} → p == p' → (q : y == z) → p ∙ q == p' ∙ q
  ∙-coh-l idp idp = idp
  !-coh : {x y : A} {p p' : x == y} → p == p' → ! p == ! p'
  !-coh idp = idp
  !!-unit : {x y : A} (p : x == y) → ! (! p) == p
  !!-unit idp = idp

ap-coh : ∀ {i j} {A : Type i} {B : Type j} {x y : A} → (f : A → B) → {p p' : x == y} → p == p' → ap f p == ap f p'
ap-coh f idp = idp

to-from-merid' :  ( ! (ap to (ap from (merid Bool true)))) ∙ idp ∙ merid Bool false ==  (merid Bool true)
to-from-merid' =  ! (ap to (ap from (merid Bool true))) ∙ idp ∙ merid Bool false              =⟨ Bla.∙idp∙ ( ! (ap to (ap from (merid Bool true))))  (merid Bool false)  ⟩
                       ! (ap to (ap from (merid Bool true))) ∙ merid Bool false               =⟨ Bla.∙-coh-l (Bla.!-coh (ap-coh to (From.glue-β true))) (merid Bool false) ⟩
                       ! (ap to loop) ∙ merid Bool false                                      =⟨ Bla.∙-coh-l (Bla.!-coh (To.loop-β)) (merid Bool false) ⟩
                       (! (merid Bool false ∙ ! (merid Bool true))) ∙ merid Bool false        =⟨ Bla.!-∙∙ (merid Bool false) (! (merid Bool true)) (merid Bool false) ⟩
                       ((! (! (merid Bool true))) ∙ ! (merid Bool false)) ∙ merid Bool false  =⟨ Bla.∙-coh-l (Bla.∙-coh-l (Bla.!!-unit (merid Bool true)) (! (merid Bool false))) (merid Bool false) ⟩
                       (merid Bool true ∙ ! (merid Bool false)) ∙ merid Bool false  =⟨ ∙-assoc (merid Bool true) (! (merid Bool false)) (merid Bool false)  ⟩
                       merid Bool true ∙ (! (merid Bool false) ∙ merid Bool false)  =⟨ Bla.p∙!q∙q (merid Bool true) (merid Bool false) ⟩
                       (merid Bool true ∎)
{-                                                                                                                                                                                               
                       ! (ap to idp) ∙ merid Bool true                                       =⟨ idp ⟩                                                                                            
                       ! (merid Bool false ∙ ! (merid Bool true)) ∙ merid Bool true          =⟨ Bla.!-∙∙ (merid Bool false)  (! (merid Bool true)) (merid Bool true)   ⟩                         
                       (! (! (merid Bool true)) ∙ ! (merid Bool false)) ∙ merid Bool true    =⟨ ∙-assoc (! (! (merid Bool true)))  (! (merid Bool false))  (merid Bool true) ⟩                   
                       ! (! (merid Bool true)) ∙ (! (merid Bool false) ∙ merid Bool true)    =⟨ {!!} ⟩                                                                                           
                       ! (! (merid Bool true))                                               =⟨ !-!  (merid Bool true) ⟩                                                                         
                       (merid Bool true ∎)                                                                                                                                                       
-}


--e : S¹ ≃ Suspension Bool
--e = equiv to from to-from from-to
