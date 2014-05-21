{-# OPTIONS --without-K #-}

open import HoTT

-- Associativity of the join (work in progress)

module homotopy.JoinAssoc {i j k} (A : Type i) (B : Type j) (C : Type k) where

  {- First map -}

  to : (A * B) * C → A * (B * C)
  to = To.f  module ToM where

    to-left-glue : (ab : A × B) → left (fst ab) == right (left (snd ab)) :> A * (B * C)
    to-left-glue (a , b) = glue (a , left b)

    {-
      (to∘inl)(inl(a))       :≡ inl(a)
      (to∘inl)(inr(b))       :≡ inr(inl(b))
      ap (to∘inl) (glue(a,b)) := glue(a,inl(b))
    -}
    module ToLeft = PushoutRec left (right ∘ left) to-left-glue

    to-left : A * B → A * (B * C)
    to-left = ToLeft.f

    to-glue-left : (c : C) (a : A) → to-left (left a) == right (right c)
    to-glue-left c a = glue (a , right c)

    to-glue-right : (c : C) (b : B) → to-left (right b) == right (right c)
    to-glue-right c b = ap right (glue (b , c))

    to-glue-glue : (c : C) (ab : A × B) → to-glue-left c (fst ab) == to-glue-right c (snd ab) [ (λ x → to-left x == right (right c)) ↓ glue ab ]
    to-glue-glue c (a , b) = ↓-swap to-left right _ idp
      (ToLeft.glue-β (a , b) ◃ apd (λ x → glue (a , x)) (glue (b , c)))

    module ToGlue (c : C) = PushoutElim (to-glue-left c) (to-glue-right c) (to-glue-glue c)

    to-glue : (ab-c : (A * B) × C) → to-left (fst ab-c) == right (right (snd ab-c))
    to-glue (ab , c) = M.f ab where module M = ToGlue c

    {- 
      to(inr(c))             :≡ inr(inr(c))
      ap to (glue(inl(a),c)) := glue(a,inr(c))
      ap to (glue(inr(b),c)) := ap inr (glue(b,c))
    -}
    module To = PushoutRec {d = *-span (A * B) C} to-left (right ∘ right) to-glue

  {- Second map -}

  from : A * (B * C) → (A * B) * C
  from = From.f  module MM where

    from-right-glue : (bc : B × C) → left (right (fst bc)) == right (snd bc)
    from-right-glue (b , c) = glue (right b , c)

    {-
      (from∘inr)(inl(b))        :≡ inl(inr(b))
      (from∘inr)(inr(c))        :≡ inr(c)
      ap (from∘inr) (glue(b,c)) := glue(lnr(b),c)
    -}
    module FromRight = PushoutRec (left ∘ right) right from-right-glue

    from-right : B * C → (A * B) * C
    from-right = FromRight.f

    from-glue-left : (a : A) (b : B) → left (left a) == from-right (left b)
    from-glue-left a b = ap left (glue (a , b))

    from-glue-right : (a : A) (c : C) → left (left a) == from-right (right c)
    from-glue-right a c = glue (left a , c)

    from-glue-glue : (a : A) (bc : B × C) → from-glue-left a (fst bc) == from-glue-right a (snd bc) [ (λ x → left (left a) == from-right x) ↓ glue bc ]
    from-glue-glue a (b , c) = ↓-swap! left from-right _ idp
      (apd (λ x → glue (x , c)) (glue (a , b)) ▹! (FromRight.glue-β (b , c)))

    module FromGlue (a : A) = PushoutElim (from-glue-left a) (from-glue-right a) (from-glue-glue a)

    from-glue : (a-bc : A × (B * C)) → left (left (fst a-bc)) == from-right (snd a-bc)
    from-glue (a , bc) = M.f bc where module M = FromGlue a

    {- 
      (from∘inl)(a)           :≡ inl(inl(a))
      ap from (glue(a,inr(c)) := glue(inl(a),c)
      ap from (glue(a,inl(b)) := ap inl (glue(a,b))
    -}
    module From = PushoutRec {d = *-span A (B * C)} (left ∘ left) from-right from-glue

  open MM public

  {- First composite -}
  
  to-from-right-glue' : (b : B) (c : C) → ap (to ∘ from-right) (glue (b , c)) =-= ap right (glue (b , c))
  to-from-right-glue' b c =
    ap (λ z → to (from-right z)) (glue (b , c))     =⟪ ap-∘ to from-right (glue (b , c)) ⟫
    ap to (ap from-right (glue (b , c)))            =⟪ FromRight.glue-β (b , c) |in-ctx ap to ⟫
    ap to (glue ((right b , c) :> (A * B) × C))     =⟪ ToM.To.glue-β (right b , c) ⟫
    ap right (glue (b , c)) ∎∎

  to-from-right-glue : (bc : B × C) → idp == idp [ (λ x → to (from (right x)) == right x) ↓ glue bc ]
  to-from-right-glue (b , c) = ↓-='-in (! (↯ to-from-right-glue' b c))

  module ToFromRight = PushoutElim (λ _ → idp) (λ _ → idp) to-from-right-glue

  to-from-right : (bc : B * C) → to (from (right bc)) == right bc
  to-from-right = ToFromRight.f

  to-from-glue-left' : (a : A) (b : B) → ap to (ap from (glue (a , left b))) =-= glue (a , left b)
  to-from-glue-left' a b =
    ap to (ap from (glue (a , left b)))   =⟪ From.glue-β (a , left b) |in-ctx ap to ⟫
    ap to (ap left (glue (a , b)))        =⟪ ∘-ap to left (glue (a , b)) ⟫
    ap ToM.to-left (glue (a , b))             =⟪ ToM.ToLeft.glue-β (a , b) ⟫
    glue (a , left b) ∎∎

  to-from-glue-left : (a : A) (b : B) → idp == to-from-right (left b) [ (λ x → to (from x) == x) ↓ glue (a , left b) ]
  to-from-glue-left a b = ↓-∘=idf-in to from (↯ to-from-glue-left' a b)

  to-from-glue-right' : (a : A) (c : C) → ap to (ap from (glue (a , right c))) =-= glue (a , right c)
  to-from-glue-right' a c =
    ap to (ap from (glue (a , right c)))   =⟪ From.glue-β (a , right c) |in-ctx ap to ⟫
    ap to (glue (left a , c))              =⟪ ToM.To.glue-β (left a , c) ⟫
    glue (a , right c) ∎∎

  to-from-glue-right : (a : A) (c : C) → idp == to-from-right (right c) [ (λ x → to (from x) == x) ↓ glue (a , right c) ]
  to-from-glue-right a c = ↓-∘=idf-in to from (↯ to-from-glue-right' a c)



{-


  to-from-left-glue' : (a : A) → ap (to ∘ from-left) a =-= ap right (a)
  to-from-left-glue' a =
    ap (λ z → to (from-right z)) (glue (b , c))     =⟪ ap-∘ to from-right (glue (b , c)) ⟫
    ap to (ap from-right (glue (b , c)))            =⟪ FromRight.glue-β (b , c) |in-ctx ap to ⟫
    ap to (glue ((right b , c) :> (A * B) × C))     =⟪ ToM.To.glue-β (right b , c) ⟫
    ap right (glue (b , c)) ∎∎

  to-from-left-glue : (a : A) → idp == idp [ (λ x → to (from (left x)) == left x) ↓ glue a ]
  to-from-left-glue (a) = ↓-='-in (! (↯ to-from-right-glue' b c))

  module ToFromLeft = PushoutElim (λ _ → idp) (λ _ → idp) to-from-left-glue
-}

  postulate  -- Not proved yet. Some of it is being worked on at JoinAssoc2
    *-assoc : ((A * B) * C) ≃ (A * (B * C))
