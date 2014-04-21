\begin{code}
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
{- Compile an 'IF cond THEN t ELSE f' statement followed by an expression 'r' to a tree-like representation
   that duplicates the 'r' statement over both branches. It is supposed to be easier to verify correctness
   of this representation than of the representation that shares 'r'. Unfortunately, due to an oversight, we
   only discovered that this case was missing just before the deadline. At that point, it was too late to modify
   the exisisting correctness proofs for this change in generated code. We leave the completion of the proofs
   as an exercise to the reader.
   
compile {.σ} {.(suc n + suc m)} {s} (_⟫ₛ_ {σ} {m} {n} (ifₛ c thenₛ t elseₛ e) e₂)
  = coerce (Bytecode s)
       (lemmaConsAppend n m σ s ~ cong (λ l → σ ∷ l ++ s) (lemmaPlusAppend n (suc m) σ))
       (compile c ⟫ IF (compile t ⟫ compile e₂) (compile e ⟫ compile e₂))
-}
compile {.σ} {.(suc n + suc m)} {s} (_⟫ₛ_ {σ} {m} {n} e₁ e₂)
  = coerce (Bytecode s)
      (lemmaConsAppend n m σ s
       ~ cong (λ l → σ ∷ l ++ s) (lemmaPlusAppend n (suc m) σ))
      (compile e₁ ⟫ compile e₂)
\end{code}
