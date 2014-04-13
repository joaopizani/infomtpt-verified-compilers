module Compiler where

-- In this file we "translate" into Agda the developments of the reference paper
-- "A type-correct, stack-safe, provably correct expression compiler in Epigram".

open import Data.Bool using (true; false)
open import Data.List using (List; _∷_; replicate; _++_)
open import Data.Vec using (Vec) renaming ([] to ε; _∷_ to _◁_)
open import Data.Nat using (ℕ; _+_; suc; zero)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Source
open import Bytecode


-- Now, having our source and "target" languages,
-- we are ready to define the compiler from one to the other:
rep : {A : Set} → (n : ℕ) → A → List A
rep = replicate  -- just a shorter name, used a lot

lemmaConsAppend : {A : Set} (m n : ℕ) (a : A) (s : List A)
    → a ∷ rep m a ++ a ∷ rep n a ++ s ≡ a ∷ (rep m a ++ a ∷ rep n a) ++ s
lemmaConsAppend zero    n a s = refl
lemmaConsAppend (suc m) n a s = cong (_∷_ a) (lemmaConsAppend m n a s)

lemmaPlusAppend : {A : Set} (m n : ℕ) (a : A) → rep m a ++ rep n a ≡ rep (m + n) a
lemmaPlusAppend zero    n a = refl
lemmaPlusAppend (suc m) n a = cong (_∷_ a) (lemmaPlusAppend m n a)

coerce : {s s₁ s₂ : StackType} → s₁ ≡ s₂ → Bytecode s s₁ → Bytecode s s₂
coerce refl b = b

coerceStack : {s₁ s₂ : StackType} → s₁ ≡ s₂ → Stack s₁ → Stack s₂
coerceStack refl s = s

lemmaStack : {st : StackType} {c : Bytecode st _}
             → ∀ eq → ∀ s → exec (coerce eq c) s ≡ exec c (coerceStack eq s)
lemmaStack refl s = refl

_~_ : {α : Set} {a b c : α} → a ≡ b → b ≡ c → a ≡ c
_~_ = trans  -- just an easier-to-use notation for transitivity
infixr 5 _~_

compile : ∀ {σ z s} → Src σ z → Bytecode s (rep z σ ++ s)
compile (vₛ x)                  = PUSH x
compile (e₁ +ₛ e₂)              = compile e₂ ⟫ compile e₁ ⟫ ADD
compile (ifₛ c thenₛ t elseₛ e) = compile c ⟫ IF (compile t) (compile e)
compile {.σ} {.(suc n + suc m)} {s} (_⟫ₛ_ {σ} {m} {n} e₁ e₂)
  = coerce
      (lemmaConsAppend n m σ s
       ~ cong (λ l → σ ∷ l ++ s) (lemmaPlusAppend n (suc m) σ))
      (compile e₁ ⟫ compile e₂)



-- Finally, the statement of correctness for the compiler
prepend : ∀ {t n σ} → (v : Vec ⁅ σ ⁆ n) → Stack t → Stack (rep n σ ++ t)
prepend ε        s = s
prepend (x ◁ xs) s = x ▽ prepend xs s

-- lemmaCoerce : ∀ {c} → ∀ eq → coerce eq c ≡ c
-- lemmaCoerce refl = refl

correct : ∀ {σ z s'} (e : Src σ z) (s : Stack s') → prepend ⟦ e ⟧ s ≡ exec (compile e) s

correct (vₛ v) s = refl

correct (x +ₛ y) s
   rewrite sym (correct y s)
         | sym (correct x (prepend ⟦ y ⟧ s))
   with ⟦ x ⟧ | ⟦ y ⟧
... | x' ◁ ε | y' ◁ ε = refl

correct (ifₛ c thenₛ t elseₛ e) s with (exec (compile c) s) | sym (correct c s)
correct (ifₛ c thenₛ t elseₛ e) s | .(prepend ⟦ c ⟧ s) | refl with ⟦ c ⟧
correct (ifₛ c thenₛ t elseₛ e) s | .(prepend ⟦ c ⟧ s) | refl | true  ◁ ε rewrite correct t s = refl
correct (ifₛ c thenₛ t elseₛ e) s | .(prepend ⟦ c ⟧ s) | refl | false ◁ ε rewrite correct e s = refl

correct {.σ} {.(suc n + suc m)} {s'} (_⟫ₛ_ {σ} {m} {n} e₁ e₂) s = {!!}

--(lemmaConsAppend n m σ s' ~ cong (λ l → σ ∷ l ++ s') (lemmaPlusAppend n (suc m) σ))
