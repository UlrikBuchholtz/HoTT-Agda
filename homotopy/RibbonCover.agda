{-# OPTIONS --without-K #-}

{-
  Ribbon is an explicit covering space construction.

  This construction is given by Daniel Grayson, Favonia
  and Guillaume Brunerie together.
-}

open import HoTT

-- A is the pointed base space.
-- El is intended to be a (group-)set,
module homotopy.RibbonCover {i : ULevel} where

  -- The HIT ribbon---reconstructed covering space

  private
    π1 = fundamental-group

  module _ (A∙ : Ptd i) {j} (gs : Gset (fundamental-group A∙) j) (a₂ : fst A∙) where
    private
      A = fst A∙
      a₁ = snd A∙
      El = Gset.El gs
      El-level = Gset.El-level gs
      infix 80 _⊙_
      _⊙_ = Gset.act gs

    RibbonSet : Type (lmax i j)
    RibbonSet = El × (a₁ =₀ a₂)

    data RibbonRel : RibbonSet → RibbonSet → Type (lmax i j) where
      ribbon-rel : ∀ el loop (p : a₁ =₀ a₂)
        → RibbonRel (el ⊙ loop , p) (el , loop ∙₀ p)

    Ribbon : Type (lmax i j)
    Ribbon = SetQuotient RibbonRel

  module _ {A∙ : Ptd i} {j} {gs : Gset (fundamental-group A∙) j} {a₂ : fst A∙} where
    private
      A = fst A∙
      a = snd A∙
      El = Gset.El gs
      El-level = Gset.El-level gs
      infix 80 _⊙_
      _⊙_ = Gset.act gs

    -- A point in the fiber [a₂].
    {-
      [e] is a point in the [fiber a], and
      [p] is a path to transport [y] to fiber [a₂].
    -}
    trace : El → a =₀ a₂ → Ribbon A∙ gs a₂
    trace el p = q[ el , p ]

    {-
      A loop based at [a] can used as a group action
      or for concatination.  Both should be equivalent.
    -}
    paste : ∀ el loop (p : a =₀ a₂) → trace (el ⊙ loop) p == trace el (loop ∙₀ p)
    paste el loop p = quot-rel (ribbon-rel el loop p)

    {-
      Make each fiber a set and cancel all higher structures
      due to [paste].
    -}
    Ribbon-level : is-set (Ribbon A∙ gs a₂)
    Ribbon-level = SetQuotient-level

    Ribbon-is-set = Ribbon-level

    -- Elimination rules.
    module RibbonElim {j} {P : Ribbon A∙ gs a₂ → Type j}
      (P-level : ∀ r → is-set (P r))
      (trace* : ∀ el p → P (trace el p))
      (paste* : ∀ el loop p
                → trace* (el ⊙ loop) p == trace* el (loop ∙₀ p)
                  [ P ↓ paste el loop p ]) where

      private
        q[_]* : (α : RibbonSet A∙ gs a₂) → P q[ α ]
        q[ el , p ]* = trace* el p

        rel* : ∀ {α₁ α₂} (r : RibbonRel A∙ gs a₂ α₁ α₂) → q[ α₁ ]* == q[ α₂ ]* [ P ↓ quot-rel r ]
        rel* (ribbon-rel el loop p) = paste* el loop p

        module M = SetQuotElim P-level q[_]* rel*

      f : Π (Ribbon A∙ gs a₂) P
      f = M.f

    open RibbonElim public using () renaming (f to Ribbon-elim)

    module RibbonRec {j} {P : Type j}
      (P-level : is-set P)
      (trace* : ∀ el p → P)
      (paste* : ∀ el loop p
                → trace* (el ⊙ loop) p == trace* el (loop ∙₀ p)) where

      private
        module M = RibbonElim (λ _ → P-level) trace*
          (λ el loop p → ↓-cst-in (paste* el loop p))

      f : Ribbon A∙ gs a₂ → P
      f = M.f

    open RibbonRec public using () renaming (f to Ribbon-rec)

  -- This data structure gives a cover.
  Ribbon-cover : ∀ (A∙ : Ptd i) {j} (gs : Gset (π1 A∙) j)
    → Cover (fst A∙) (lmax i j)
  Ribbon-cover A∙ gs = record
    { Fiber = Ribbon A∙ gs
    ; Fiber-level = λ a → Ribbon-level
    }

  trans-trace : ∀ {A : Type i} {a₁} {j}
    {gs : Gset (π1 (A , a₁)) j}
    {a₂} (q : a₁ == a₂) y p
    → transport (Ribbon (A , a₁) gs) q (trace y p) == trace y (p ∙₀ [ q ])
  trans-trace idp y p = ap (trace y) $ ! $ ∙₀-unit-r p
