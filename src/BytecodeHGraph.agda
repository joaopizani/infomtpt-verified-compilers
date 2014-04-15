module BytecodeHGraph where

open import HGraph
open import Source
open import Bytecode

open import Data.Nat using (ℕ; _+_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Data.List using (List; []; _∷_; replicate; [_]) renaming (_++_ to _++ₗ_)

open import Util

SKIP_G : ∀ {v s} -> HGraph' BytecodeF v s s
SKIP_G = HGraphIn SKIP'

PUSH_G : ∀ {v α s} -> (x : ⁅ α ⁆) → HGraph' BytecodeF v s (α ∷ s)
PUSH_G x = HGraphIn (PUSH' x) 

ADD_G : ∀ {v s} -> HGraph' BytecodeF v (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
ADD_G = HGraphIn ADD'

IF_G : ∀ {v s s'} -> HGraph' BytecodeF v s s' -> HGraph' BytecodeF v s s' -> HGraph' BytecodeF v (𝔹ₛ ∷ s) s'
IF_G t f = HGraphIn (IF' t f)

_⟫G_  : ∀ {v s₀ s₁ s₂} → (HGraph' BytecodeF v s₀ s₁) → (HGraph' BytecodeF v s₁ s₂) → HGraph' BytecodeF v s₀ s₂
_⟫G_ f g = HGraphIn (f ⟫' g)

execG : ∀ {s s'} → HGraph BytecodeF s s' -> Stack s -> Stack s'
execG = foldGraph execAlg




compileG' : ∀ {σ z s} → Src σ z → ∀ {v} → HGraph' BytecodeF v s (replicate z σ ++ₗ s)
compileG' (vₛ x)                  = PUSH_G x
compileG' (e₁ +ₛ e₂)              = (compileG' e₂ ⟫G compileG' e₁) ⟫G ADD_G
compileG' (ifₛ c thenₛ t elseₛ e) = compileG' c ⟫G IF_G (compileG' t) (compileG' e)
compileG' {.σ} {.(suc n + suc m)} {s} (_⟫ₛ_ {σ} {m} {n} e₁ e₂) {v}
    = coerce (HGraph' BytecodeF v s)
      (lemmaConsAppend n m σ s
       ~ cong (λ l → σ ∷ l ++ₗ s) (lemmaPlusAppend n (suc m) σ))
      (compileG' e₁ ⟫G compileG' e₂)

compileG : {s : StackType} → ∀ {z σ} -> Src σ z → HGraph BytecodeF s (replicate z σ ++ₗ s)
compileG src = mkHGraph (compileG' src)
