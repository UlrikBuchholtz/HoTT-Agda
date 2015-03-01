{-# OPTIONS --without-K #-}

open import HoTT

module lib.Quaternions where

data Sign : Type₀ where
  plus : Sign
  minus : Sign

opposite : Sign → Sign
opposite plus = minus
opposite minus = plus

_·_ : Sign → Sign → Sign
plus · x = x
minus · x = opposite x

·unitr : (x : Sign) → x · plus == x
·unitr plus = idp
·unitr minus = idp

·assoc : (x y z : Sign) → (x · y) · z == x · (y · z)
·assoc plus y z = idp
·assoc minus plus z = idp
·assoc minus minus plus = idp
·assoc minus minus minus = idp

·cohl : {x y : Sign} → x == y → (z : Sign) → x · z == y · z
·cohl idp z = idp

·cohr : (x : Sign) → {y z : Sign} → y == z → x · y == x · z
·cohr x idp = idp

·comm : (x y : Sign) → x · y == y · x
·comm plus plus = idp
·comm plus minus = idp
·comm minus plus = idp
·comm minus minus = idp

data Dir : Type₀ where
  i : Dir
  j : Dir
  k : Dir

shift : Dir → Dir
shift i = j
shift j = k
shift k = i

data QU : Type₀ where
  one : QU
  dir : Dir → QU
  
Q : Type₀
Q = Σ Sign λ _ → QU

multWithSign : Dir → Dir → Q
multWithSign i i = minus , one
multWithSign i j = plus , dir k
multWithSign i k = minus , dir j
multWithSign j i = minus , dir k
multWithSign j j = minus , one
multWithSign j k = plus , dir i
multWithSign k i = plus , dir j
multWithSign k j = minus , dir i
multWithSign k k = minus , one

_⊙_ : Q → Q → Q
(s , one) ⊙ (t , u) = s · t , u
(s , dir d) ⊙ (t , one) = s · t , dir d
(s , dir d) ⊙ (t , dir e) with multWithSign d e
... | (x , u) = (s · t) · x , u

inv : Q → Q
inv (x , one) = x , one
inv (x , dir d) = opposite x , dir d

unitl : (a : Q) → (plus , one) ⊙ a == a
unitl (x , u) = idp

unitr : (a : Q) → a ⊙ (plus , one) == a
unitr (x , one) = pair×= (·unitr x) idp
unitr (x , dir d) = pair×= (·unitr x) idp

assoc : (a b c : Q) → (a ⊙ b) ⊙ c == a ⊙ (b ⊙ c)
assoc (x , one) (y , one) (z , w) = pair×= (·assoc x y z) idp
assoc (x , one) (y , dir d) (z , one) = pair×= (·assoc x y z) idp
assoc (x , one) (y , dir d) (z , dir e) with multWithSign d e
... | (w , u) = pair×= lemma idp
  where
    lemma : ((x · y) · z) · w == x · ((y · z) · w)
    lemma = ((x · y) · z) · w     =⟨ ·assoc (x · y) z w ⟩
            (x · y) · (z · w)     =⟨ ·assoc x y (z · w) ⟩
            x · (y · (z · w))     =⟨ ·cohr x (! (·assoc y z w)) ⟩
            x · ((y · z) · w) ∎
assoc (x , dir d) (y , one) (z , one) = pair×= (·assoc x y z) idp
assoc (x , dir d) (y , one) (z , dir f) with multWithSign d f
... | (w , u) = pair×= lemma idp
  where
    lemma : ((x · y) · z) · w == (x · (y · z)) · w
    lemma = ((x · y) · z) · w     =⟨ ·cohl (·assoc x y z) w ⟩
            (x · (y · z)) · w ∎
assoc (x , dir d) (y , dir e) (z , one) with multWithSign d e
assoc (x , dir d) (y , dir e) (z , one) | (w , one) = pair×= lemma idp
  where
    lemma : ((x · y) · w) · z == (x · (y · z)) · w
    lemma = ((x · y) · w) · z     =⟨ ·assoc (x · y) w z ⟩
            (x · y) · (w · z)     =⟨ ·cohr (x · y) (·comm w z) ⟩
            (x · y) · (z · w)     =⟨ ! (·assoc (x · y) z w) ⟩
            ((x · y) · z) · w     =⟨ ·cohl (·assoc x y z) w ⟩
            (x · (y · z)) · w ∎
assoc (x , dir d) (y , dir e) (z , one) | (w , dir g) = pair×= lemma idp
  where
    lemma : ((x · y) · w) · z == (x · (y · z)) · w
    lemma = ((x · y) · w) · z     =⟨ ·assoc (x · y) w z ⟩
            (x · y) · (w · z)     =⟨ ·cohr (x · y) (·comm w z) ⟩
            (x · y) · (z · w)     =⟨ ! (·assoc (x · y) z w) ⟩
            ((x · y) · z) · w     =⟨ ·cohl (·assoc x y z) w ⟩
            (x · (y · z)) · w ∎
assoc (x , dir d) (y , dir e) (z , dir f) with multWithSign d e | multWithSign e f
assoc (x , dir d) (y , dir e) (z , dir f) | a , one | b , v = {!!}
assoc (x₁ , dir d) (y , dir e) (z , dir f) | a , dir x | b , v = {!!}
