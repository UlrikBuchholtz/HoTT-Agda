{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.FunctionOver

{- The cofiber space of [winl : X → X ∨ Y] is equivalent to [Y],
 - and the cofiber space of [winr : Y → X ∨ Y] is equivalent to [X]. -}

module cohomology.WedgeCofiber where

module WedgeCofiber {i} (X Y : Ptd i) where

  module CofWinl where

    module Into = CofiberRec winl (snd Y) (projr X Y) (λ _ → idp)

    into = Into.f

    out : fst Y → Cofiber (winl {X = X} {Y = Y})
    out = cfcod _ ∘ winr

    out-into : (κ : Cofiber (winl {X = X} {Y = Y})) → out (into κ) == κ
    out-into = Cofiber-elim winl
      (! (cfglue _ (snd X) ∙ ap (cfcod _) wglue))
      (Wedge-elim
        (λ x → ! (cfglue _ (snd X) ∙ ap (cfcod _) wglue) ∙ cfglue _ x)
        (λ y → idp)
        (↓-='-from-square $
          (lemma (cfglue _ (snd X)) (ap (cfcod _) wglue)
           ∙h⊡ (ap-∘ out (projr X Y) wglue ∙ ap (ap out) (Projr.glue-β X Y))
                ∙v⊡ bl-square (ap (cfcod _) wglue))))
      (λ x → ↓-∘=idf-from-square out into $
        ! (∙-unit-r _) ∙h⊡
          ap (ap out) (Into.glue-β x) ∙v⊡
           hid-square {p = (! (cfglue winl (snd X) ∙ ap (cfcod winl) wglue))}
           ⊡v connection {q = cfglue _ x})
      where
      lemma : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z)
        → ! (p ∙ q) ∙ p == ! q
      lemma idp idp = idp

    ⊙path : ⊙Cof (⊙winl {X = X} {Y = Y}) == Y
    ⊙path = ⊙ua (⊙ify-eq (equiv into out (λ _ → idp) out-into) idp)

    cfcod-over : ⊙cfcod ⊙winl == ⊙projr X Y
                 [ (λ U → fst (X ⊙∨ Y ⊙→ U)) ↓ ⊙path ]
    cfcod-over = codomain-over-⊙equiv (⊙cfcod ⊙winl) _
                 ▹ pair= idp (∙-unit-r _ ∙ ap-! into (cfglue _ (snd X))
                              ∙ ap ! (Into.glue-β (snd X)))

  module CofWinr where

    module Into = CofiberRec winr (snd X) (projl X Y) (λ _ → idp)

    into = Into.f

    out : fst X → Cofiber (winr {X = X} {Y = Y})
    out = cfcod _ ∘ winl

    out-into : ∀ κ → out (into κ) == κ
    out-into = Cofiber-elim winr
      (ap (cfcod _) wglue ∙ ! (cfglue _ (snd Y)))
      (Wedge-elim
        (λ x → idp)
        (λ y → (ap (cfcod _) wglue ∙ ! (cfglue _ (snd Y))) ∙ cfglue _ y)
        (↓-='-from-square $
          (ap-∘ out (projl X Y) wglue ∙ ap (ap out) (Projl.glue-β X Y)) ∙v⊡
             connection
           ⊡h∙ ! (lemma (ap (cfcod winr) wglue) (cfglue _ (snd Y)))))
      (λ y → ↓-∘=idf-from-square out into $
        ! (∙-unit-r _) ∙h⊡
          ap (ap out) (Into.glue-β y) ∙v⊡
            hid-square {p = (ap (cfcod winr) wglue ∙ ! (cfglue _ (snd Y)))}
            ⊡v connection {q = cfglue _ y})
      where
      lemma : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : z == y)
        → (p ∙ ! q) ∙ q == p
      lemma idp idp = idp

    ⊙path : ⊙Cof ⊙winr == X
    ⊙path = ⊙ua (⊙ify-eq (equiv into out (λ _ → idp) out-into) idp)

    cfcod-over : ⊙cfcod ⊙winr == ⊙projl X Y
                 [ (λ U → fst (X ⊙∨ Y ⊙→ U)) ↓ ⊙path ]
    cfcod-over = codomain-over-⊙equiv (⊙cfcod ⊙winr) _
                 ▹ pair= idp lemma
      where
      lemma : ap into (ap (cfcod _) (! (! wglue)) ∙ ! (cfglue _ (snd Y))) ∙ idp
           == idp
      lemma =
        ap into (ap (cfcod _) (! (! wglue)) ∙ ! (cfglue _ (snd Y))) ∙ idp
          =⟨ ∙-unit-r _ ⟩
        ap into (ap (cfcod _) (! (! wglue)) ∙ ! (cfglue _ (snd Y)))
          =⟨ !-! wglue
             |in-ctx (λ w → ap into (ap (cfcod _) w ∙ ! (cfglue _ (snd Y)))) ⟩
        ap into (ap (cfcod _) wglue ∙ ! (cfglue _ (snd Y)))
          =⟨ ap-∙ into (ap (cfcod _) wglue) (! (cfglue _ (snd Y))) ⟩
        ap into (ap (cfcod _) wglue) ∙ ap into (! (cfglue _ (snd Y)))
          =⟨ ∘-ap into (cfcod _) wglue
             |in-ctx (λ w → w ∙ ap into (! (cfglue _ (snd Y)))) ⟩
        ap (projl X Y) wglue ∙ ap into (! (cfglue _ (snd Y)))
          =⟨ Projl.glue-β X Y
             |in-ctx (λ w → w ∙ ap into (! (cfglue _ (snd Y)))) ⟩
        ap into (! (cfglue _ (snd Y)))
          =⟨ ap-! into (cfglue _ (snd Y)) ⟩
        ! (ap into (cfglue _ (snd Y)))
          =⟨ ap ! (Into.glue-β (snd Y)) ⟩
        idp ∎
