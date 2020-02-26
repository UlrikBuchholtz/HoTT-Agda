{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Coproduct
open import lib.types.Empty
open import lib.types.Pi

module lib.Relation2 where

module _ {i} {P : Type i} where

  instance
    Dec-level : ∀ {n} → {{nP : has-level (S n) P}} → has-level (S n) (Dec P)
    Dec-level {n} = has-level-in Dec-level-aux where

      Dec-level-aux : has-level-aux (S n) (Dec P)
      Dec-level-aux (inl p₁) (inl p₂) = equiv-preserves-level (inl=inl-equiv p₁ p₂ ⁻¹) {{has-level-apply-instance}}
      Dec-level-aux (inl p) (inr ¬p) = ⊥-rec $ ¬p p
      Dec-level-aux (inr ¬p) (inl p) = ⊥-rec $ ¬p p
      Dec-level-aux (inr ¬p₁) (inr ¬p₂) = equiv-preserves-level (inr=inr-equiv ¬p₁ ¬p₂ ⁻¹)
        {{has-level-apply (prop-has-level-S ⟨⟩) ¬p₁ ¬p₂}}
