module Compiler where

-- In this file we "translate" into Agda the developments of the reference paper
-- "A type-correct, stack-safe, provably correct expression compiler in Epigram".

open import Data.Bool using (true; false)
open import Data.List using (List; _∷_; replicate; _++_)
open import Data.Vec using (Vec) renaming ([] to ε; _∷_ to _◁_; _++_ to _+++_)
open import Data.Nat using (ℕ; _+_; suc; zero)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Source
open import Bytecode

open import Util

lemmaStack :
 {st st1 st2 : StackType} {c : Bytecode st st1} (eq : st1 ≡ st2) (s : Stack st)
 → exec (coerce (Bytecode st) eq c) s ≡ coerce Stack eq (exec c s)
lemmaStack refl s = refl


compile : ∀ {σ z s} → Src σ z → Bytecode s (replicate z σ ++ s)
compile (vₛ x)                  = PUSH x
compile (e₁ +ₛ e₂)              = compile e₂ ⟫ compile e₁ ⟫ ADD
compile (ifₛ c thenₛ t elseₛ e) = compile c ⟫ IF (compile t) (compile e)
compile {.σ} {.(suc n + suc m)} {s} (_⟫ₛ_ {σ} {m} {n} e₁ e₂)
  = coerce (Bytecode s)
      (lemmaConsAppend n m σ s
       ~ cong (λ l → σ ∷ l ++ s) (lemmaPlusAppend n (suc m) σ))
      (compile e₁ ⟫ compile e₂)




