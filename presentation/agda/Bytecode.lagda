\begin{code}

{-# OPTIONS --no-positivity-check #-}
module Bytecode where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; replicate; _++_)
open import Data.Nat using (ℕ; _+_; suc; zero)

open import Source

open import HFunctor

_~_ : {α : Set} {a b c : α} → a ≡ b → b ≡ c → a ≡ c
_~_ = trans  -- just an easier-to-use notation for transitivity
infixr 5 _~_


rep : {A : Set} → (n : ℕ) → A → List A
rep = replicate  -- just a shorter name, used a lot


coerce : {A : Set} → (F : A → Set) → {s₁ s₂ : A} → s₁ ≡ s₂ → F s₁ → F s₂
coerce _ refl b = b

lemmaConsAppend : {A : Set} (m n : ℕ) (a : A) (s : List A)
    → a ∷ rep m a ++ a ∷ rep n a ++ s ≡ a ∷ (rep m a ++ a ∷ rep n a) ++ s
lemmaConsAppend zero    n a s = refl
lemmaConsAppend (suc m) n a s = cong (_∷_ a) (lemmaConsAppend m n a s)

lemmaPlusAppend : {A : Set} (m n : ℕ) (a : A) → rep m a ++ rep n a ≡ rep (m + n) a
lemmaPlusAppend zero    n a = refl
lemmaPlusAppend (suc m) n a = cong (_∷_ a) (lemmaPlusAppend m n a)


-- First, we define "typed stacks", which are stacks indexed by lists of TyExp.
-- Each element of the stack has therefore a corresponding type.
\end{code}

%<*stacktype>
\begin{code}
StackType : Set
StackType = List Tyₛ
\end{code}
%</stacktype>

%<*stack>
\begin{code}
data Stack : StackType → Set where
    ε    : Stack []
    _▽_  : ∀ {t s'} → ⁅ t ⁆ → Stack s' → Stack (t ∷ s')
\end{code}
%</stack>
\begin{code}

infixr 7 _▽_
\end{code}


-- To complete the definition of the abstract machine,
-- we need to list the instructions of the bytecode operating on it, and give its semantics.

%<*bytecode>
\begin{code}
data Bytecode : StackType → StackType → Set where
    SKIP : ∀ {s}    → Bytecode s s
    PUSH : ∀ {t s}  → (x : ⁅ t ⁆) → Bytecode s (t ∷ s)
    ADD  : ∀ {s}    → Bytecode (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
\end{code}
%</bytecode>
\begin{code}
    IF   : ∀ {s s′} → (t : Bytecode s s′) → (e : Bytecode s s′) → Bytecode (𝔹ₛ ∷ s) s′
    _⟫_  : ∀ {s₀ s₁ s₂} → (c₁ : Bytecode s₀ s₁) → (c₂ : Bytecode s₁ s₂) → Bytecode s₀ s₂

infixl 4 _⟫_
\end{code}

%<*Tree>
\begin{code}
data Tree (f : Set -> Set) : Set where
  In : f (Tree f) -> Tree f
\end{code}
%</Tree>

%<*Tree>
\begin{code}
data HTree (f : (StackType -> StackType -> Set) 
              → (StackType -> StackType -> Set) ) 
     (ixp : StackType) (ixq : StackType) : Set where
  HTreeIn : f (HTree f) ixp ixq -> HTree f ixp ixq

\end{code}
%</HTree>

\begin{code}
postulate foldTree : {F : (StackType -> StackType -> Set) -> (StackType -> StackType -> Set)} -> {{ functor : HFunctor F }} -> {r : StackType -> StackType -> Set} -> ( {ixp : StackType} {ixq : StackType} -> F r ixp ixq -> r ixp ixq) -> ( {ixp : StackType} {ixq : StackType} -> HTree F   ixp ixq -> r ixp ixq)
\end{code}


%<*HGraph>
\begin{code}
data HGraph' {Ip Iq : Set} (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set) ) (v : Ip -> Iq -> Set) (ixp : Ip) (ixq : Iq) : Set where
  HGraphIn  : F (HGraph' F v) ixp ixq -> HGraph' F v ixp ixq
  HGraphLet : (HGraph' F v ixp ixq) -> (v ixp ixq -> HGraph' F v ixp ixq) -> HGraph' F v ixp ixq  
  HGraphVar : v ixp ixq -> HGraph' F v ixp ixq
\end{code}
%</HGraph>

\begin{code}
data HGraph {Ip Iq : Set} (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set) ) (ixp : Ip) (ixq : Iq) : Set₁ where
  mkHGraph : ( {v : Ip -> Iq -> Set} -> (HGraph' F v ixp ixq) ) -> HGraph F ixp ixq
\end{code}

\begin{code}

postulate foldGraph : {F : (StackType -> StackType -> Set) -> (StackType -> StackType -> Set)} -> {{ functor : HFunctor F }} -> {r : StackType -> StackType -> Set} -> ( {ixp : StackType} {ixq : StackType} -> F r ixp ixq -> r ixp ixq)-> ( {ixp : StackType} {ixq : StackType} -> HGraph F   ixp ixq -> r ixp ixq)

\end{code}


%<*bytecodeF>
\begin{code}

data BytecodeF (r : StackType -> StackType -> Set) : (StackType -> StackType -> Set) where  
    SKIP' : ∀ {s}    → BytecodeF r s s
    PUSH' : ∀ {α s}  → (x : ⁅ α ⁆) → BytecodeF r s (α ∷ s)
    ADD'  : ∀ {s}    → BytecodeF r (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
\end{code}
%</bytecodeF>

\begin{code}
    IF'   : ∀ {s s′} → (t : r s s′) → (e : r s s′) → BytecodeF r (𝔹ₛ ∷ s) s′
    _⟫'_  : ∀ {s₀ s₁ s₂} → (c₁ : r s₀ s₁) → (c₂ : r s₁ s₂) → BytecodeF r s₀ s₂
SKIP_T : ∀ {s} -> HTree BytecodeF s s
SKIP_T = HTreeIn SKIP'

PUSH_T : ∀ {α s} -> (x : ⁅ α ⁆) → HTree BytecodeF s (α ∷ s)
PUSH_T x = HTreeIn (PUSH' x) 

ADD_T : ∀ {s} -> HTree BytecodeF (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
ADD_T = HTreeIn ADD'

IF_T : ∀ {s s'} -> HTree BytecodeF s s' -> HTree BytecodeF s s' -> HTree BytecodeF (𝔹ₛ ∷ s) s'
IF_T t f = HTreeIn (IF' t f)

_⟫T_  : ∀ {s₀ s₁ s₂} → (HTree BytecodeF s₀ s₁) → (HTree BytecodeF s₁ s₂) → HTree BytecodeF s₀ s₂
_⟫T_ f g = HTreeIn (f ⟫' g)
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
\end{code}

%<*compile>
\begin{code}

compile : ∀ {σ z s} → Src σ z → Bytecode s (replicate z σ ++ s)
compile (vₛ x)                  = PUSH x
compile (e₁ +ₛ e₂)              = compile e₂ ⟫ compile e₁ ⟫ ADD
\end{code}
%</compile>

\begin{code}
compile (ifₛ c thenₛ t elseₛ e) = compile c ⟫ IF (compile t) (compile e)
compile {.σ} {.(suc n + suc m)} {s} (_⟫ₛ_ {σ} {m} {n} e₁ e₂)
  = coerce (Bytecode s)
      (lemmaConsAppend n m σ s
       ~ cong (λ l → σ ∷ l ++ s) (lemmaPlusAppend n (suc m) σ))
      (compile e₁ ⟫ compile e₂)
\end{code}

%<*compileT>
\begin{code}
compileT : ∀ {σ z s} → Src σ z → HTree BytecodeF s (replicate z σ ++ s)
\end{code}
%</compileT>

\begin{code}

compileT (vₛ x)                  = PUSH_T x
compileT (e₁ +ₛ e₂)              = (compileT e₂ ⟫T compileT e₁) ⟫T ADD_T
compileT (ifₛ c thenₛ t elseₛ e) = compileT c ⟫T IF_T (compileT t) (compileT e)
compileT {.σ} {.(suc n + suc m)} {s} (_⟫ₛ_ {σ} {m} {n} e₁ e₂) 
    = coerce (HTree BytecodeF s)
      (lemmaConsAppend n m σ s
       ~ cong (λ l → σ ∷ l ++ s) (lemmaPlusAppend n (suc m) σ))
      (compileT e₁ ⟫T compileT e₂)
\end{code}


\begin{code}


compileG' : ∀ {σ z s} → Src σ z → ∀ {v} → HGraph' BytecodeF v s (replicate z σ ++ s)
compileG' (vₛ x)                  = PUSH_G x
compileG' (e₁ +ₛ e₂)              = (compileG' e₂ ⟫G compileG' e₁) ⟫G ADD_G
compileG' (ifₛ c thenₛ t elseₛ e) = compileG' c ⟫G IF_G (compileG' t) (compileG' e)
compileG' {.σ} {.(suc n + suc m)} {s} (_⟫ₛ_ {σ} {m} {n} e₁ e₂) {v}
    = coerce (HGraph' BytecodeF v s)
      (lemmaConsAppend n m σ s
       ~ cong (λ l → σ ∷ l ++ s) (lemmaPlusAppend n (suc m) σ))
      (compileG' e₁ ⟫G compileG' e₂)
\end{code}

%<*compileG>
\begin{code}
compileG : {s : StackType} → ∀ {z σ} -> Src σ z → HGraph BytecodeF s (replicate z σ ++ s)
\end{code}
%</compileG>

\begin{code}
compileG src = mkHGraph (compileG' src)
\end{code}

%<*execT>
\begin{code}
execT : ∀ {s s'} → HTree BytecodeF s s' -> Stack s -> Stack s'
\end{code}
%</execT>

\begin{code}
execT = foldTree execAlg
\end{code}

%<*execG>
\begin{code}
execG : ∀ {s s'} → HGraph BytecodeF s s' -> Stack s -> Stack s'
\end{code}
%</execG>

\begin{code}
execG = foldGraph execAlg
\end{code}
