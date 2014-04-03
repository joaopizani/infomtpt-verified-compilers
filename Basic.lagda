In this file we "translate" the developments of the reference paper
"A type-correct, stack-safe, provably correct expression compiler in Epigram" into Agda.

There. Fixed it. We only need this for HFix. If we trust this is sound, hopefully we can continue our proof without losing too much credibility. I think this is safer than introducing non-positivity in our stack datatype. TODO: move to seperate file so the rest of our proof isn't contaminated.

\begin{code}
{-# OPTIONS --no-positivity-check #-}
module Basic where

open import Data.Bool using (true; false)
\end{code}

First of all, as our expression language is typed, we need a _language of types_
We denote the types of the _object language_ with the similar symbols of the corresponding types in the _host language_ (Agda),
subscripted with a lower-case "o" (OH):

\begin{code}
data TyExp : Set where
    ℕₒ : TyExp
    𝔹ₒ : TyExp
\end{code}

Together with defining the object language types,
we define a mapping from object language types into Agda types.

\begin{code}
open import Data.Nat using (ℕ)
open import Data.Bool using () renaming (Bool to 𝔹)

⁅_⁆ : TyExp → Set
⁅ ℕₒ ⁆ = ℕ
⁅ 𝔹ₒ ⁆ = 𝔹
\end{code}

Now we can define an inductive family for the expressions of our object language,
indexed by their _object language_ type (TyExp). We also use subscripted notation to avoid confusion with
Agda's standard library symbols.

\begin{code}
data Exp : TyExp → Set where
    V                : ∀ {t} → (v : ⁅ t ⁆) → Exp t
    _+ₒ_             : (e₁ e₂ : Exp ℕₒ) → Exp ℕₒ
    ifₒ_thenₒ_elseₒ_ : ∀ {t} → (c : Exp 𝔹ₒ) → (eₜ eₑ : Exp t) → Exp t

infixl 4 _+ₒ_
\end{code}

The evaluation function defined below is the first (denotational) semantics for our object language.
Evaluation takes a _typed expression in out object language_ to a _correspondingly-typed_ Agda value.
We denote evaluation by using the usual "semantic brackets", "⟦" and "⟧".

\begin{code}
open Data.Nat using (_+_)
open Data.Bool using (if_then_else_)

⟦_⟧ : {t : TyExp} → Exp t → ⁅ t ⁆
⟦ V v ⟧                      = v
⟦ e₁ +ₒ e₂ ⟧                 = ⟦ e₁ ⟧ + ⟦ e₂ ⟧
⟦ ifₒ_thenₒ_elseₒ_ c e₁ e₂ ⟧ = if ⟦ c ⟧ then ⟦ e₁ ⟧ else ⟦ e₂ ⟧ 
\end{code}

Now we move towards the second semantics for our expression language:
compilation to bytecode and execution of bytecode in an abstract machine.

First, we define "typed stacks", which are stacks indexed by lists of TyExp.
Each element of the stack has therefore a corresponding type.

\begin{code}
open import Data.List using ([]; _∷_) renaming (List to [_])

StackType : Set
StackType = [ TyExp ]

data Stack : StackType → Set where
    ε   : Stack []
    _▷_ : ∀ {t ts} → ⁅ t ⁆ → Stack ts → Stack (t ∷ ts)

infixr 4 _▷_

top : ∀ {t ts} → Stack (t ∷ ts) → ⁅ t ⁆
top (v ▷ s) = v
\end{code}

To complete the definition of the abstract machine,
we need to list the instructions of the bytecode operating on it, and give its semantics.

In the listing of the bytecode instructions,
it should be noted that each instruction is a function from _typed stack_ to typed stack.

\begin{code}
data Bytecode : StackType → StackType → Set where
    SKIP : ∀ {s}    → Bytecode s s
    PUSH : ∀ {t s}  → ⁅ t ⁆ → Bytecode s (t ∷ s)
    ADD  : ∀ {s}    → Bytecode (ℕₒ ∷ ℕₒ ∷ s) (ℕₒ ∷ s)
    IF   : ∀ {s s′} → Bytecode s s′ → Bytecode s s′ → Bytecode (𝔹ₒ ∷ s) s′
    _⟫_  : ∀ {s₀ s₁ s₂} → Bytecode s₀ s₁ → Bytecode s₁ s₂ → Bytecode s₀ s₂

infixl 4 _⟫_


exec : ∀ {s s′} → Bytecode s s′ → Stack s → Stack s′
exec SKIP s               = s
exec (PUSH v) s           = v ▷ s
exec ADD (n ▷ m ▷ s)      = n + m ▷ s
exec (IF t e) (true  ▷ s) = exec t s
exec (IF t e) (false ▷ s) = exec e s
exec (c₁ ⟫ c₂) s          = exec c₂ (exec c₁ s)
\end{code}

Now, having our source and "target" languages,
we are ready to define the compiler from one to the other:

\begin{code}
compile : ∀ {t s} → Exp t → Bytecode s (t ∷ s)
compile (V v)                   = PUSH v
compile (e₁ +ₒ e₂)              = compile e₂ ⟫ compile e₁ ⟫ ADD
compile (ifₒ c thenₒ t elseₒ e) = compile c ⟫ IF (compile t) (compile e)
\end{code}

The correctness proof for the simple, tree-based bytecode.

\begin{code}
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

correct : ∀ {t st} → (e : Exp t) → (s : Stack st) → ⟦ e ⟧ ▷ s ≡ exec (compile e) s
correct (V v) s = refl
correct (e₁ +ₒ e₂) s rewrite sym (correct e₂ s) | sym (correct e₁ (⟦ e₂ ⟧ ▷ s)) = refl
correct (ifₒ c thenₒ t elseₒ e) s rewrite sym (correct c s) with ⟦ c ⟧
... | true = correct t s
... | false = correct e s
\end{code}

A functor representation for the bytecode, so that we can proof tree ↔ graph equivalence.

\begin{code}
record HFunctor (Ip : Set) (Iq : Set) (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set)) : Set₁ where
  constructor isHFunctor
  field
    hmap : (a : Ip -> Iq -> Set) -> (b : Ip -> Iq -> Set) 
         -> ( (ixp : Ip) -> (ixq : Iq) ->   a ixp ixq ->   b ixp ixq )
         -> ( (ixp : Ip) -> (ixq : Iq) -> F a ixp ixq -> F b ixp ixq )  

record HFix (Ip : Set) (Iq : Set) (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set) ) (ixp : Ip) (ixq : Iq) : Set where
  constructor HIn
  field
    hout : F (HFix Ip Iq F) ixp ixq
  
    

data BytecodeF (r : StackType -> StackType -> Set) : (StackType -> StackType -> Set) where  
    SKIP' : ∀ {s}    → BytecodeF r s s
    PUSH' : ∀ {t s}  → ⁅ t ⁆ → BytecodeF r s (t ∷ s)
    ADD'  : ∀ {s}    → BytecodeF r (ℕₒ ∷ ℕₒ ∷ s) (ℕₒ ∷ s)
    IF'   : ∀ {s s′} → (t : r s s′) → (e : r s s′) → BytecodeF r (𝔹ₒ ∷ s) s′
    _⟫⟫_  : ∀ {s₀ s₁ s₂} → r s₀ s₁ → r s₁ s₂ → BytecodeF r s₀ s₂

mapBytecodeF : (a b : StackType -> StackType -> Set) -> ( (ixp : StackType) -> (ixq : StackType) ->           a ixp ixq ->           b ixp ixq) 
                                                     -> ( (ixp : StackType) -> (ixq : StackType) -> BytecodeF a ixp ixq -> BytecodeF b ixp ixq)
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

fold : (r : StackType -> StackType -> Set) 
    -> ( (ixp ixq : StackType) -> BytecodeF r ixp ixq                        -> r ixp ixq) 
    -> ( (ixp ixq : StackType) -> HFix StackType StackType BytecodeF ixp ixq -> r ixp ixq)
fold = {!!}
\end{code}
