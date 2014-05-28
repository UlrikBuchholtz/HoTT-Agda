{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.S1SuspensionS0 where

{- To -}

module To = S¹Rec (north Bool) (merid _ true ∙ ! (merid _ false))

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


module _ {i}  {A : Type i} where
  ∙idp∙ : {x y z : A} (p : x == y) (q : y == z) → p ∙ idp ∙ q == p ∙ q
  ∙idp∙ idp idp = idp
  p∙!q∙q : {x y z : A} (p : x == y) (q : z == y) → p ∙ ( ! q ∙ q)  == p
  p∙!q∙q idp idp = idp
  !-∙∙ :  {x y z w : A} (p : x == y) (q : y == z) (r : x == w) →  ! (p ∙ q) ∙ r == (! q ∙ ! p ) ∙ r
  !-∙∙ idp idp idp = idp
  !-coh : {x y : A} {p p' : x == y} → p == p' → ! p == ! p'
  !-coh idp = idp
  add-idp-r : {x y : A} → (p : x == y) → p == p ∙ idp
  add-idp-r idp = idp

ap-coh : ∀ {i j} {A : Type i} {B : Type j} {x y : A} → (f : A → B) → {p p' : x == y} → p == p' → ap f p == ap f p'
ap-coh f idp = idp
_∋_ : ∀ {i} (A : Type i) → A → A
A ∋ x = x

mt : north Bool == south Bool
mt = merid Bool true

mf : north Bool == south Bool
mf = merid Bool false

to-from-merid-t' :  ( ! (ap to (ap from mt))) ∙ idp ∙ mt ==  mf
to-from-merid-t' =  ! (ap to (ap from mt)) ∙ idp ∙ mt         =⟨ ∙idp∙ ( ! (ap to (ap from mt)))  mt  ⟩
                    ! (ap to (ap from mt)) ∙ mt               =⟨ (!-coh (ap-coh to (From.glue-β true))) ∙ᵣ mt ⟩
                    ! (ap to loop) ∙ mt                       =⟨ (!-coh (To.loop-β)) ∙ᵣ mt ⟩
                    (! (mt ∙ ! mf)) ∙ mt                      =⟨ !-∙∙ mt (! mf) mt ⟩
                    ((! (! mf)) ∙ ! mt) ∙ mt                  =⟨ ((!-! mf) ∙ᵣ (! mt)) ∙ᵣ mt ⟩
                    (mf ∙ ! mt) ∙ mt                          =⟨ ∙-assoc mf (! mt) mt  ⟩
                    mf ∙ (! mt ∙ mt)                          =⟨ p∙!q∙q mf mt ⟩
                    mf ∎

to-from-merid-f' :  ( ! (ap to (ap from mf))) ∙ idp ∙ mf ==  mf
to-from-merid-f' =  ! (ap to (ap from mf)) ∙ idp ∙ mf        =⟨ ∙idp∙ ( ! (ap to (ap from mf))) mf ⟩ 
                    ! (ap to (ap from mf)) ∙ mf              =⟨ (!-coh (ap-coh to (From.glue-β false))) ∙ᵣ mf ⟩ 
                    mf ∎

-- to-from-merid' : (b : Bool) → ( ! (ap to (ap from (merid Bool b)))) ∙ idp ∙ mf ==  (merid Bool b)
-- to-from-merid' false = to-from-merid-f' 
-- to-from-merid' true = to-from-merid-t' 

to-from : (x : Suspension Bool) → to (from x) == x
to-from = ToFrom.f
  where
    Q : Suspension Bool → Set lzero
    Q x = to (from x) == x
    
    n : to (from (north Bool)) == north Bool
    n = idp
    
    s : to (from (south Bool)) == south Bool
    s = mf

    lemma : {x y : Suspension Bool} → (q : x == y) → (α : to (from x) == x) → transport Q q α == (! (ap to (ap from q))) ∙ α ∙ q
    lemma idp α = add-idp-r α
    
    p : (b : Bool) → n == s [ Q ↓ merid Bool b ]
    p true = from-transp Q mt ((lemma mt n) ∙ to-from-merid-t')
    p false = from-transp Q mf ((lemma mf n) ∙ to-from-merid-f')
    
    module ToFrom = SuspensionElim Bool {P = Q} n s p


from-to-loop' : (! (ap from (ap to loop))) ∙ idp ∙ loop == idp
from-to-loop' = ! (ap from (ap to loop)) ∙ idp ∙ loop         =⟨ ∙idp∙ (! (ap from (ap to loop)))  loop  ⟩
                ! (ap from (ap to loop)) ∙ loop               =⟨ (!-coh (ap-coh from To.loop-β)) ∙ᵣ loop ⟩
                ! (ap from (mt ∙ ! mf)) ∙ loop                =⟨ (!-coh (ap-∙ from mt (! mf))) ∙ᵣ loop  ⟩
                (! ((ap from mt) ∙ (ap from (! mf)))) ∙ loop  =⟨ (!-coh ( (From.glue-β true) ∙ᵣ (ap from (! mf)))) ∙ᵣ loop  ⟩
                ! (loop ∙ (ap from (! mf))) ∙ loop            =⟨ !-coh (loop ∙ₗ ap-! from mf) ∙ᵣ loop ⟩
                ! (loop ∙ ! (ap from mf)) ∙ loop              =⟨ !-coh (loop ∙ₗ (!-coh (From.glue-β false))) ∙ᵣ loop ⟩
                ! (loop ∙ ! idp) ∙ loop                       =⟨ !-∙∙ loop (! idp) loop ⟩
                (! loop) ∙ loop                               =⟨ !-inv-l loop ⟩
                idp ∎


from-to : (x : S¹) → from (to x) == x
from-to = FromTo.f
  where
    Q : S¹ → Type lzero
    Q x = from (to x) == x

    b : Q base
    b = idp

    lemma : {x y : S¹} → (q : x == y) → (α : from (to x) == x) → transport Q q α == (! (ap from (ap to q))) ∙ α ∙ q
    lemma idp α = add-idp-r α
    
    l : b == b [ Q ↓ loop ]
    l = from-transp Q loop ((lemma loop b) ∙ from-to-loop')
    
    module FromTo = S¹Elim {P = Q} b l

e : S¹ ≃ Suspension Bool
e = equiv to from to-from from-to
