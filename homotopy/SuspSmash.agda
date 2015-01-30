{-# OPTIONS --without-K #-}

open import HoTT
open import lib.cubical.elims.CofWedge
open import lib.cubical.elims.SuspSmash

{- Σ(X∧Y) ≃ X * Y -}

module homotopy.SuspSmash {i j} (X : Ptd i) (Y : Ptd j) where

private

  {- path lemmas -}
  private
    reduce-x : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : z == y)
      → p ∙ ! q ∙ q ∙ ! p ∙ p == p
    reduce-x idp idp = idp

    reduce-y : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : x == z)
      → p ∙ ! p ∙ q ∙ ! q ∙ p == p
    reduce-y idp idp = idp

  module Into = SuspensionRec (Smash X Y)
    {C = fst (X ⊙* Y)}
    (left (snd X))
    (right (snd Y))
    (cof-wedge-path-rec
      (glue (snd X , snd Y))
      (λ {(x , y) →
        glue (snd X , snd Y) ∙ ! (glue (x , snd Y))
        ∙ glue (x , y)
        ∙ ! (glue (snd X , y)) ∙ glue (snd X , snd Y)})
      (λ x → ! (reduce-x (glue (snd X , snd Y)) (glue (x , snd Y))))
      (λ y → ! (reduce-y (glue (snd X , snd Y)) (glue (snd X , y)))))

  into = Into.f

  module Out = PushoutRec {d = ⊙span-out (*-⊙span X Y)}
    {D = Suspension (Smash X Y)}
    (λ _ → north _)
    (λ _ → south _)
    (λ {(x , y) → merid _ (cfcod _ (x , y))})

  out = Out.f

  into-out : (j : fst (X ⊙* Y)) → into (out j) == j
  into-out = Pushout-elim
    (λ x → glue (snd X , snd Y) ∙ ! (glue (x , snd Y)))
    (λ y → ! (glue (snd X , snd Y)) ∙ glue (snd X , y))
    (↓-∘=idf-from-square into out ∘ λ {(x , y) →
      (ap (ap into) (Out.glue-β (x , y))
       ∙ Into.glue-β (cfcod _ (x ,  y)))
      ∙v⊡ lemma (glue (snd X , snd Y)) (glue (x , snd Y))
                (glue (snd X , y)) (glue (x , y))})
    where
    lemma : ∀ {i} {A : Type i} {x y z w : A}
      (p : x == y) (q : z == y) (r : x == w) (s : z == w)
      → Square (p ∙ ! q) (p ∙ ! q ∙ s ∙ ! r ∙ p) s (! p ∙ r)
    lemma idp idp idp s =
      vert-degen-square (∙-unit-r s)

  out-into : (σ : Suspension (Smash X Y)) → out (into σ) == σ
  out-into = susp-smash-path-elim (out ∘ into) (idf _)
    idp
    idp
    (λ {(x , y) → vert-degen-square $
      ap-∘ out into (merid _ (cfcod _ (x , y)))
      ∙ ap (ap out) (Into.glue-β (cfcod _ (x , y)))
      ∙ lemma₁ out (Out.glue-β (snd X , snd Y))
                   (Out.glue-β (x , snd Y))
                   (Out.glue-β (x , y))
                   (Out.glue-β (snd X , y))
                   (Out.glue-β (snd X , snd Y))
      ∙ lemma₂ {p = merid _ (cfcod _ (snd X , snd Y))}
               {q = merid _ (cfcod _ (x , snd Y))}
               {r = merid _ (cfcod _ (x , y))}
               {s = merid _ (cfcod _ (snd X , y))}
               {t = merid _ (cfcod _ (snd X , snd Y))}
          (ap (merid _) (! (cfglue _ (winl (snd X))) ∙ cfglue _ (winl x)))
          (ap (merid _) (! (cfglue _ (winr y)) ∙ cfglue _ (winr (snd Y))))
      ∙ ! (ap-idf (merid _ (cfcod _ (x , y))))})
    where
    lemma₁ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
      {x y z u v w : A}
      {p : x == y} {q : z == y} {r : z == u} {s : v == u} {t : v == w}
      {p' : f x == f y} {q' : f z == f y} {r' : f z == f u}
      {s' : f v == f u} {t' : f v == f w}
      (α : ap f p == p') (β : ap f q == q') (γ : ap f r == r')
      (δ : ap f s == s') (ε : ap f t == t')
      → ap f (p ∙ ! q ∙ r ∙ ! s ∙ t) == p' ∙ ! q' ∙ r' ∙ ! s' ∙ t'
    lemma₁ f {p = idp} {q = idp} {r = idp} {s = idp} {t = idp}
          idp idp idp idp idp
      = idp

    lemma₂ : ∀ {i} {A : Type i} {x y z u : A}
      {p q : x == y} {r : x == z} {s t : u == z}
      (α : p == q) (β : s == t)
      → p ∙ ! q  ∙ r ∙ ! s ∙ t == r
    lemma₂ {p = idp} {r = idp} {s = idp} idp idp = idp


module SuspSmash where

  eq : Suspension (Smash X Y) ≃ fst (X ⊙* Y)
  eq = equiv into out into-out out-into

  path : Suspension (Smash X Y) == fst (X ⊙* Y)
  path = ua eq

  ⊙path : ⊙Susp (⊙Smash X Y) == X ⊙* Y
  ⊙path = ⊙ua eq idp
