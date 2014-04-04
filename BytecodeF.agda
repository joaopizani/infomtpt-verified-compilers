{-# OPTIONS --no-positivity-check #-}
module BytecodeF where

open import Data.List using (_∷_)

open import Basic using (𝔹ₛ; ℕₛ; StackType; Bytecode; ⁅_⁆')


record HFunctor (Ip : Set) (Iq : Set) (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set)) : Set₁ where
  constructor isHFunctor
  field
    hmap : {a : Ip -> Iq -> Set} -> {b : Ip -> Iq -> Set} 
         -> ( {ixp : Ip} -> {ixq : Iq} ->   a ixp ixq ->   b ixp ixq )
         -> ( {ixp : Ip} -> {ixq : Iq} -> F a ixp ixq -> F b ixp ixq )  

record HFix (Ip : Set) (Iq : Set) (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set) ) (ixp : Ip) (ixq : Iq) : Set where
  constructor HIn
  field
    hout : F (HFix Ip Iq F) ixp ixq
  
    

data BytecodeF (r : StackType -> StackType -> Set) : (StackType -> StackType -> Set) where  
    SKIP' : ∀ {s}    → BytecodeF r s s
    PUSH' : ∀ {α s}  → (x : ⁅ α ⁆') → BytecodeF r s (α ∷ s)
    ADD'  : ∀ {s}    → BytecodeF r (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
    IF'   : ∀ {s s′} → (t : r s s′) → (e : r s s′) → BytecodeF r (𝔹ₛ ∷ s) s′
    _⟫'_  : ∀ {s₀ s₁ s₂} → (c₁ : r s₀ s₁) → (c₂ : r s₁ s₂) → BytecodeF r s₀ s₂

mapBytecodeF : {a b : StackType -> StackType -> Set} -> ( {ixp ixq : StackType} ->           a ixp ixq ->           b ixp ixq) 
                                                     -> ( {ixp ixq : StackType} -> BytecodeF a ixp ixq -> BytecodeF b ixp ixq)
mapBytecodeF = {!!}

BytecodeFisFunctor : HFunctor StackType StackType BytecodeF
BytecodeFisFunctor =
  record {
    hmap = mapBytecodeF
  } 

toFixed : (ixp ixq : StackType) -> Bytecode ixp ixq -> HFix StackType StackType BytecodeF ixp ixq
toFixed = {!!}

fromFixed : (ixp ixq : StackType) -> HFix StackType StackType BytecodeF ixp ixq -> Bytecode ixp ixq
fromFixed = {!!}

fold : {r : StackType -> StackType -> Set}
    -> ( {ixp ixq : StackType} -> BytecodeF r ixp ixq                        -> r ixp ixq) 
    -> ( {ixp ixq : StackType} -> HFix StackType StackType BytecodeF ixp ixq -> r ixp ixq)
fold alg (HIn r) = 
  let hmap = HFunctor.hmap BytecodeFisFunctor
  in alg (hmap (fold alg) r)
