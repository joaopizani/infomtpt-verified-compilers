\begin{code}
module Util where

open import Level using ( Level )

open import Data.List using (List; []; _∷_; replicate; [_]) renaming (_++_ to _++ₗ_)
open import Data.Nat using (ℕ; _+_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

apply : {X Y : Set} -> {f g : X -> Y} -> (x : X) -> f ≡ g -> f x ≡ g x
apply x refl = refl

cong₃ : {P Q S R : Set} {a b : P} {x y : Q} {p q : S} -> (f : P → Q → S → R) -> a ≡ b -> x ≡ y -> p ≡ q -> f a x p ≡ f b y q
cong₃ f refl refl refl = refl 

cong' : {e : Level} {X : Set e} {R : Set}
     -> (P Q : X -> R)
     -> (a b : X) 
     -> ((x : X) -> P x ≡ Q x) -> a ≡ b 
     -> P a ≡ Q b
cong' P Q a .a f refl = f a 

_~_ : {α : Set} {a b c : α} → a ≡ b → b ≡ c → a ≡ c
_~_ = trans  -- just an easier-to-use notation for transitivity
infixr 5 _~_

-- Now, having our source and "target" languages,
-- we are ready to define the compiler from one to the other:
rep : {A : Set} → (n : ℕ) → A → List A
rep = replicate  -- just a shorter name, used a lot

lemmaConsAppend : {A : Set} (m n : ℕ) (a : A) (s : List A)
    → a ∷ rep m a ++ₗ a ∷ rep n a ++ₗ s ≡ a ∷ (rep m a ++ₗ a ∷ rep n a) ++ₗ s
lemmaConsAppend zero    n a s = refl
lemmaConsAppend (suc m) n a s = cong (_∷_ a) (lemmaConsAppend m n a s)

lemmaPlusAppend : {A : Set} (m n : ℕ) (a : A) → rep m a ++ₗ rep n a ≡ rep (m + n) a
lemmaPlusAppend zero    n a = refl
lemmaPlusAppend (suc m) n a = cong (_∷_ a) (lemmaPlusAppend m n a)

coerce : {A : Set} → (F : A → Set) → {s₁ s₂ : A} → s₁ ≡ s₂ → F s₁ → F s₂
coerce _ refl b = b
\end{code}
