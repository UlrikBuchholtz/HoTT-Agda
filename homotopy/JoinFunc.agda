{-# OPTIONS --without-K #-}

open import HoTT


module homotopy.JoinFunc where


 module F {i j k l}  {A : Type i} {B : Type j} {C : Type k} {D : Type l} (f : A → C) (g : B → D) where

   fg-glue : (ab : A × B) → left (f (fst ab)) == right (g (snd ab)) :> (C * D)
   fg-glue (a , b) = glue (f a , g b)

   to : A * B → C * D
   to = To.f  module M where

     module To = PushoutRec (left ∘ f) (right ∘ g) fg-glue

   open M public

 module _  {i j k l} {A : Type i} {B : Type j} {C : Type k} {D : Type l} where
  _**_[_] : (A → C) → (B → D) → A * B → C * D
  f ** g [ ab ] = M.to ab where
                module M = F f g
