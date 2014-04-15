module Bytecode where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (_+_)

open import Source

open import HFunctor


-- First, we define "typed stacks", which are stacks indexed by lists of TyExp.
-- Each element of the stack has therefore a corresponding type.
StackType : Set
StackType = List Tyₛ

data Stack : StackType → Set where
    ε    : Stack []
    _▽_  : ∀ {σ s'} → ⁅ σ ⁆ → Stack s' → Stack (σ ∷ s')

infixr 7 _▽_


-- To complete the definition of the abstract machine,
-- we need to list the instructions of the bytecode operating on it, and give its semantics.
data Bytecode : StackType → StackType → Set where
    SKIP : ∀ {s}    → Bytecode s s
    PUSH : ∀ {σ s}  → (x : ⁅ σ ⁆) → Bytecode s (σ ∷ s)
    ADD  : ∀ {s}    → Bytecode (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
    IF   : ∀ {s s′} → (t : Bytecode s s′) → (e : Bytecode s s′) → Bytecode (𝔹ₛ ∷ s) s′
    _⟫_  : ∀ {s₀ s₁ s₂} → (c₁ : Bytecode s₀ s₁) → (c₂ : Bytecode s₁ s₂) → Bytecode s₀ s₂

infixl 4 _⟫_


data BytecodeF (r : StackType -> StackType -> Set) : (StackType -> StackType -> Set) where  
    SKIP' : ∀ {s}    → BytecodeF r s s
    PUSH' : ∀ {α s}  → (x : ⁅ α ⁆) → BytecodeF r s (α ∷ s)
    ADD'  : ∀ {s}    → BytecodeF r (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
    IF'   : ∀ {s s′} → (t : r s s′) → (e : r s s′) → BytecodeF r (𝔹ₛ ∷ s) s′
    _⟫'_  : ∀ {s₀ s₁ s₂} → (c₁ : r s₀ s₁) → (c₂ : r s₁ s₂) → BytecodeF r s₀ s₂

mapBytecodeF : {a b : StackType -> StackType -> Set} -> ( {ixp ixq : StackType} ->           a ixp ixq ->           b ixp ixq) 
                                                     -> ( {ixp ixq : StackType} -> BytecodeF a ixp ixq -> BytecodeF b ixp ixq)
mapBytecodeF f SKIP' = SKIP'
mapBytecodeF f (PUSH' x) = PUSH' x
mapBytecodeF f ADD' = ADD'
mapBytecodeF f (IF' t e) = IF' (f t) (f e)
mapBytecodeF f (_⟫'_ c₁ c₂)= f c₁ ⟫' f c₂


BytecodeFunctor : HFunctor BytecodeF
BytecodeFunctor =
  record {
    hmap = mapBytecodeF
  }

-- Now the operational semantics of the bytecode.
exec : ∀ {s s′} → Bytecode s s′ → Stack s → Stack s′
exec SKIP        s           = s
exec (PUSH v)    s           = v ▽ s
exec ADD         (n ▽ m ▽ s) = (n + m) ▽ s
exec (IF t e)    (true  ▽ s) = exec t s
exec (IF t e)    (false ▽ s) = exec e s
exec (c₁ ⟫ c₂)   s           = exec c₂ (exec c₁ s)

execAlg : ∀ {s s′} → BytecodeF (λ t t' → Stack t → Stack t') s s′ → Stack s → Stack s′
execAlg SKIP'        s           = s
execAlg (PUSH' v)    s           = v ▽ s
execAlg ADD'         (n ▽ m ▽ s) = (n + m) ▽ s
execAlg (IF' t e)    (true  ▽ s) = t s
execAlg (IF' t e)    (false ▽ s) = e s
execAlg (c₁ ⟫' c₂)   s           = c₂ (c₁ s)
