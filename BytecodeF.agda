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
    SKIP : ∀ {s}    → BytecodeF r s s
    PUSH : ∀ {α s}  → (x : ⁅ α ⁆') → BytecodeF r s (α ∷ s)
    ADD  : ∀ {s}    → BytecodeF r (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
    IF   : ∀ {s s′} → (t : r s s′) → (e : r s s′) → BytecodeF r (𝔹ₛ ∷ s) s′
    _⟫_  : ∀ {s₀ s₁ s₂} → (c₁ : r s₀ s₁) → (c₂ : r s₁ s₂) → BytecodeF r s₀ s₂

mapBytecodeF : {a b : StackType -> StackType -> Set} -> ( {ixp ixq : StackType} ->           a ixp ixq ->           b ixp ixq) 
                                                     -> ( {ixp ixq : StackType} -> BytecodeF a ixp ixq -> BytecodeF b ixp ixq)
mapBytecodeF f SKIP = SKIP
mapBytecodeF f (PUSH x) = PUSH x
mapBytecodeF f ADD = ADD
mapBytecodeF f (IF t e) = IF (f t) (f e)
mapBytecodeF f (_⟫_ c₁ c₂)= f c₁ ⟫ f c₂


BytecodeFisFunctor : HFunctor StackType StackType BytecodeF
BytecodeFisFunctor =
  record {
    hmap = mapBytecodeF
  } 

toFixed : {ixp ixq : StackType} -> Bytecode ixp ixq -> HFix StackType StackType BytecodeF ixp ixq
toFixed Basic.SKIP = HIn SKIP
toFixed (Basic.PUSH x) = HIn (PUSH x)
toFixed Basic.ADD = HIn ADD
toFixed (Basic.IF bc₁ bc₂) = HIn (IF (toFixed bc₁) (toFixed bc₂))
toFixed (bc₁ Basic.⟫ bc₂) = HIn (toFixed bc₁ ⟫ toFixed bc₂)  

fromFixed : {ixp ixq : StackType} -> HFix StackType StackType BytecodeF ixp ixq -> Bytecode ixp ixq
fromFixed (HIn SKIP) = Basic.SKIP
fromFixed (HIn (PUSH x)) = Basic.PUSH x
fromFixed (HIn ADD) = Basic.ADD
fromFixed (HIn (IF t e)) = Basic.IF (fromFixed t) (fromFixed e)
fromFixed (HIn (c₁ ⟫ c₂)) = fromFixed c₁ Basic.⟫ fromFixed c₂

fold : {r : StackType -> StackType -> Set}
    -> ( {ixp ixq : StackType} -> BytecodeF r ixp ixq                        -> r ixp ixq) 
    -> ( {ixp ixq : StackType} -> HFix StackType StackType BytecodeF ixp ixq -> r ixp ixq)
fold alg (HIn r) = 
  let hmap = HFunctor.hmap BytecodeFisFunctor
  in alg (hmap (fold alg) r)
