\begin{code}
{-# OPTIONS --no-positivity-check #-}

module Report where
open import Level using ( Level )
open import Data.Bool using (if_then_else_) renaming (Bool to 𝔹)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List using ( ) renaming ( _++_ to _++ₗ_)
open import Data.Vec using (Vec; [_]; head) renaming (_++_ to _+++_)
open import Data.Nat using (ℕ; _+_; suc; zero)
open import Data.Vec using (Vec) renaming ([] to  ε; _∷_ to _◁_)


open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

\end{code}
%<*apply>
\begin{code}
apply : {X Y : Set} -> {f g : X -> Y} -> (x : X) -> f ≡ g -> f x ≡ g x
\end{code}
%</apply>
\begin{code}
apply x refl = refl
\end{code}

%<*funext>
\begin{code}
postulate funext : {X Y : Set} {f g : X → Y} → ( (x : X) → f x ≡ g x ) → f ≡ g
\end{code}
%</funext>



%<*cong3>
\begin{code}
cong₃ : {P Q S R : Set} {a b : P} {x y : Q} {p q : S} -> (f : P → Q → S → R) -> a ≡ b -> x ≡ y -> p ≡ q -> f a x p ≡ f b y q
\end{code}
%</cong3>
\begin{code}
cong₃ f refl refl refl = refl 

\end{code}
%<*cong'>
\begin{code}
cong' : {e : Level} {X : Set e} {R : Set}
     -> (P Q : X -> R)
     -> (a b : X) 
     -> ((x : X) -> P x ≡ Q x) -> a ≡ b 
     -> P a ≡ Q b
cong' P Q a .a f refl = f a 
\end{code}
%</cong'>
\begin{code}

_~_ : {α : Set} {a b c : α} → a ≡ b → b ≡ c → a ≡ c
_~_ = trans  -- just an easier-to-use notation for transitivity
infixr 5 _~_


-- Now, having our source and "target" languages,
-- we are ready to define the compiler from one to the other:
rep : {A : Set} → (n : ℕ) → A → List A
rep = replicate  -- just a shorter name, used a lot

\end{code}
%<*lemmaConsAppend>
\begin{code}
lemmaConsAppend : {A : Set} (m n : ℕ) (a : A) (s : List A)
    → a ∷ rep m a ++ₗ a ∷ rep n a ++ₗ s ≡ a ∷ (rep m a ++ₗ a ∷ rep n a) ++ₗ s
lemmaConsAppend zero    n a s = refl
lemmaConsAppend (suc m) n a s = cong (_∷_ a) (lemmaConsAppend m n a s)
\end{code}
%</lemmaConsAppend>
\begin{code}

\end{code}
%<*lemmaPlusAppend>
\begin{code}
lemmaPlusAppend : {A : Set} (m n : ℕ) (a : A) → rep m a ++ₗ rep n a ≡ rep (m + n) a
lemmaPlusAppend zero    n a = refl
lemmaPlusAppend (suc m) n a = cong (_∷_ a) (lemmaPlusAppend m n a)
\end{code}
%</lemmaPlusAppend>
\begin{code}

\end{code}
%<*coerce>
\begin{code}
coerce : {A : Set} → (F : A → Set) → {s₁ s₂ : A} → s₁ ≡ s₂ → F s₁ → F s₂
coerce _ refl b = b
\end{code}
%</coerce>

%<*HFunctor>
\begin{code}
record HFunctor {Ip Iq : Set} (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set)) : Set₁ where
  constructor isHFunctor
  field
    hmap : {a : Ip -> Iq -> Set} -> {b : Ip -> Iq -> Set} 
         -> ( {ixp : Ip} -> {ixq : Iq} ->   a ixp ixq ->   b ixp ixq )
         -> ( {ixp : Ip} -> {ixq : Iq} -> F a ixp ixq -> F b ixp ixq )  
\end{code}
%</HFunctor>

%<*Tys>
\begin{code}
data Tyₛ : Set where
    ℕₛ : Tyₛ
    𝔹ₛ : Tyₛ
\end{code}
%</Tys>
\begin{code}

-- Together with defining the object language types,
-- we define a mapping from object language types into Agda types

\end{code}
%<*TyInterpretation>
\begin{code}
⁅_⁆ : (α : Tyₛ) → Set
⁅ ℕₛ ⁆ = ℕ
⁅ 𝔹ₛ ⁆ = 𝔹
\end{code}
%</TyInterpretation>
\begin{code}

-- Now we can define an inductive family for the expressions of our object language,
-- indexed by their src language type (Tyₛ). We also use subscripted notation
-- to avoid confusion with Agda's standard library symbols.

\end{code}
%<*SizeS>
\begin{code}
Sizeₛ : Set
Sizeₛ = ℕ
\end{code}
%</SizeS>
\begin{code}

\end{code}
%<*Src>
\begin{code}
data Src : (σ : Tyₛ) → (z : Sizeₛ) → Set where
    vₛ    : ∀ {σ} → (v : ⁅ σ ⁆) → Src σ 1
    _+ₛ_  : (e₁ e₂ : Src ℕₛ 1) → Src ℕₛ 1
    ifₛ_thenₛ_elseₛ_ : ∀ {σ n} → (c : Src 𝔹ₛ 1)
                        → (eₜ eₑ : Src σ (suc n)) → Src σ (suc n)
    _⟫ₛ_  : ∀ {σ m n} → Src σ (suc m) → Src σ (suc n) → Src σ (suc n + suc m)
\end{code}
%</Src>
\begin{code}

infixl 40 _+ₛ_



-- The evaluation function defined below is a denotational semantics for the src language.
-- Evaluation takes a typed expression in our src language_ to a typed Agda value.
-- We denote evaluation by using the usual "semantic brackets", "⟦" and "⟧".
mutual
\end{code}
%<*eval>
\begin{code}
    ⟦_⟧ : {σ : Tyₛ} {z : Sizeₛ} → (e : Src σ z) → Vec ⁅ σ ⁆ z
    ⟦ vₛ v ⟧                     = [ v ]
    ⟦ e₁ +ₛ e₂ ⟧                 = [ ⟦ e₁ ⟧' + ⟦ e₂ ⟧' ] 
    ⟦ ifₛ_thenₛ_elseₛ_ c e₁ e₂ ⟧ = if ⟦ c ⟧' then ⟦ e₁ ⟧ else ⟦ e₂ ⟧
    ⟦ e₁ ⟫ₛ e₂ ⟧                 = ⟦ e₂ ⟧ +++ ⟦ e₁ ⟧

    ⟦_⟧' : {σ : Tyₛ} {z' : Sizeₛ} → (e : Src σ (suc z')) → ⁅ σ ⁆
    ⟦ e ⟧' = head ⟦ e ⟧
\end{code}
%</eval>

\begin{code}
-- First, we define "typed stacks", which are stacks indexed by lists of TyExp.
-- Each element of the stack has therefore a corresponding type.
\end{code}
%<*StackType>
\begin{code}
StackType : Set
StackType = List Tyₛ
\end{code}
%</StackType>
\begin{code}

\end{code}
%<*Stack>
\begin{code}
data Stack : StackType → Set where
    ε    : Stack []
    _▽_  : ∀ {σ s'} → ⁅ σ ⁆ → Stack s' → Stack (σ ∷ s')
\end{code}
%</Stack>
\begin{code}

infixr 7 _▽_


-- To complete the definition of the abstract machine,
-- we need to list the instructions of the bytecode operating on it, and give its semantics.
\end{code}
%<*Bytecode>
\begin{code}
data Bytecode : StackType → StackType → Set where
    SKIP : ∀ {s}    → Bytecode s s
    PUSH : ∀ {σ s}  → (x : ⁅ σ ⁆) → Bytecode s (σ ∷ s)
    ADD  : ∀ {s}    → Bytecode (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
    IF   : ∀ {s s′} → (t : Bytecode s s′) → (e : Bytecode s s′) → Bytecode (𝔹ₛ ∷ s) s′
    _⟫_  : ∀ {s₀ s₁ s₂} → (c₁ : Bytecode s₀ s₁) → (c₂ : Bytecode s₁ s₂) → Bytecode s₀ s₂
\end{code}
%</Bytecode>
\begin{code}


infixl 4 _⟫_

\end{code}
%<*BytecodeF>
\begin{code}
data BytecodeF (r : StackType -> StackType -> Set) : (StackType -> StackType -> Set) where  
    SKIP' : ∀ {s}    → BytecodeF r s s
    PUSH' : ∀ {α s}  → (x : ⁅ α ⁆) → BytecodeF r s (α ∷ s)
    ADD'  : ∀ {s}    → BytecodeF r (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
    IF'   : ∀ {s s′} → (t : r s s′) → (e : r s s′) → BytecodeF r (𝔹ₛ ∷ s) s′
    _⟫'_  : ∀ {s₀ s₁ s₂} → (c₁ : r s₀ s₁) → (c₂ : r s₁ s₂) → BytecodeF r s₀ s₂
\end{code}
%</BytecodeF>
\begin{code}

mapBytecodeF : {a b : StackType -> StackType -> Set} -> ( {ixp ixq : StackType} ->           a ixp ixq ->           b ixp ixq) 
                                                     -> ( {ixp ixq : StackType} -> BytecodeF a ixp ixq -> BytecodeF b ixp ixq)
mapBytecodeF f SKIP' = SKIP'
mapBytecodeF f (PUSH' x) = PUSH' x
mapBytecodeF f ADD' = ADD'
mapBytecodeF f (IF' t e) = IF' (f t) (f e)
mapBytecodeF f (_⟫'_ c₁ c₂)= f c₁ ⟫' f c₂

\end{code}
%<*BytecodeFunctor>
\begin{code}
BytecodeFunctor : HFunctor BytecodeF
BytecodeFunctor =
  record {
    hmap = mapBytecodeF
  }
\end{code}
%</correctT>
\begin{code}

-- Now the operational semantics of the bytecode.
\end{code}
%<*exec>
\begin{code}
exec : ∀ {s s′} → Bytecode s s′ → Stack s → Stack s′
\end{code}
%</exec>
\begin{code}
exec SKIP        s           = s
exec (PUSH v)    s           = v ▽ s
exec ADD         (n ▽ m ▽ s) = (n + m) ▽ s
exec (IF t e)    (true  ▽ s) = exec t s
exec (IF t e)    (false ▽ s) = exec e s
exec (c₁ ⟫ c₂)   s           = exec c₂ (exec c₁ s)

\end{code}
%<*execAlg>
\begin{code}
execAlg : ∀ {s s′} → BytecodeF (λ t t' → Stack t → Stack t') s s′ → Stack s → Stack s′
\end{code}
%</execAlg>
\begin{code}
execAlg SKIP'        s           = s
execAlg (PUSH' v)    s           = v ▽ s
execAlg ADD'         (n ▽ m ▽ s) = (n + m) ▽ s
execAlg (IF' t e)    (true  ▽ s) = t s
execAlg (IF' t e)    (false ▽ s) = e s
execAlg (c₁ ⟫' c₂)   s           = c₂ (c₁ s)
\end{code}

%<*lemmaStack>
\begin{code}
lemmaStack :
 {st st1 st2 : StackType} {c : Bytecode st st1} (eq : st1 ≡ st2) (s : Stack st)
 → exec (coerce (Bytecode st) eq c) s ≡ coerce Stack eq (exec c s)
lemmaStack refl s = refl
\end{code}
%</lemmaStack>
\begin{code}

\end{code}
%<*compile>
\begin{code}
compile : ∀ {σ z s} → Src σ z → Bytecode s (replicate z σ ++ₗ s)
\end{code}
%</compile>
\begin{code}
compile (vₛ x)                  = PUSH x
compile (e₁ +ₛ e₂)              = compile e₂ ⟫ compile e₁ ⟫ ADD
compile (ifₛ c thenₛ t elseₛ e) = compile c ⟫ IF (compile t) (compile e)
compile {.σ} {.(suc n + suc m)} {s} (_⟫ₛ_ {σ} {m} {n} e₁ e₂)
  = coerce (Bytecode s)
      (lemmaConsAppend n m σ s
       ~ cong (λ l → σ ∷ l ++ₗ s) (lemmaPlusAppend n (suc m) σ))
      (compile e₁ ⟫ compile e₂)

\end{code}
%<*HTree>
\begin{code}
record HTree {Ip Iq : Set} (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set) ) (ixp : Ip) (ixq : Iq) : Set where
  constructor HTreeIn
  field
    treeOut : F (HTree F) ixp ixq
\end{code}
%</HTree>
\begin{code}

\end{code}
%<*foldTree>
\begin{code}
postulate foldTree : {Ip Iq : Set} -> {F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set)} -> {{ functor : HFunctor F }} -> {r : Ip -> Iq -> Set} -> ( {ixp : Ip} {ixq : Iq} -> F r ixp ixq -> r ixp ixq) -> ( {ixp : Ip} {ixq : Iq} -> HTree F   ixp ixq -> r ixp ixq)
\end{code}
%</foldTree>

-- foldTree : 
--         {Ip Iq : Set} 
--      -> {F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set)} -> 
--         {{ functor : HFunctor F }} 
--      -> {r : Ip -> Iq -> Set} 
--      -> ( {ixp : Ip} {ixq : Iq} -> F r ixp ixq -> r ixp ixq) 
--      -> ( {ixp : Ip} {ixq : Iq} -> HTree F   ixp ixq -> r ixp ixq)
-- foldTree {{functor}} alg (HTreeIn r) = alg (hmap (foldTree alg) r) 
--   where open HFunctor functor

\begin{code}
--postulate foldTree : {Ip Iq : Set} -> {F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set)} -> {{ functor : HFunctor F }} -> {r : Ip -> Iq -> Set} -> ( {ixp : Ip} {ixq : Iq} -> F r ixp ixq -> r ixp ixq) -> ( {ixp : Ip} {ixq : Iq} -> HTree F   ixp ixq -> r ixp ixq)

{-
fusion : 
     ∀ {Ip Iq r} 
  -> ∀ {F} -> {{ functor : HFunctor F }}
  -> {ixp : Ip} {ixq : Iq}
  -> (b : ∀ {c} -> ( {ixP : Ip} -> {ixQ : Iq} -> F c ixP ixQ -> c ixP ixQ) -> c ixp ixq)       
  -> (alg : ∀ {ixp ixq} → F r ixp ixq → r ixp ixq)
  -> b alg ≡ foldTree alg {ixp} {ixq} (b HTreeIn)
fusion {_} {_} {_} {{_}} {ixp} {ixq} b alg with alg {ixp} {ixq}
... | alg' = {!!}
-}

\end{code}
%<*fusion>
\begin{code}
postulate fusion : ∀ {Ip Iq r} -> ∀ {F} -> {{ functor : HFunctor F }} -> {ixp : Ip} {ixq : Iq}-> (b : ∀ {c} -> ( {ixP : Ip} -> {ixQ : Iq} -> F c ixP ixQ -> c ixP ixQ) -> c ixp ixq) -> (alg : ∀ {ixp ixq} → F r ixp ixq → r ixp ixq) -> b alg ≡ foldTree alg {ixp} {ixq} (b HTreeIn)
\end{code}
%</fusion>
\begin{code}

\end{code}

\begin{code}

\end{code}
%<*HGraph'>
\begin{code}
data HGraph' {Ip Iq : Set} (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set) ) (v : Ip -> Iq -> Set) (ixp : Ip) (ixq : Iq) : Set where
  HGraphIn  : F (HGraph' F v) ixp ixq -> HGraph' F v ixp ixq
  HGraphLet : (HGraph' F v ixp ixq) -> (v ixp ixq -> HGraph' F v ixp ixq) -> HGraph' F v ixp ixq  
  HGraphVar : v ixp ixq -> HGraph' F v ixp ixq
\end{code}
%</HGraph'>
\begin{code}

\end{code}
%<*foldGraph'>
\begin{code}
{-# NO_TERMINATION_CHECK #-}
foldGraph' :
       {Ip Iq : Set} 
    -> {F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set)} ->
       {{ functor : HFunctor F }}
    -> {V : Ip -> Iq -> Set}      
    -> {r : Ip -> Iq -> Set}
    -> ( {ixp : Ip} {ixq : Iq} -> V ixp ixq -> r ixp ixq )
    -> ( {ixp : Ip} {ixq : Iq} -> r ixp ixq -> (V ixp ixq -> r ixp ixq) -> r ixp ixq)
    -> ( {ixp : Ip} {ixq : Iq} ->         F r ixp ixq -> r ixp ixq) 
    -> ( {ixp : Ip} {ixq : Iq} -> HGraph' F V ixp ixq -> r ixp ixq)
foldGraph' {{functor}} v l alg (HGraphIn r) = alg (hmap (foldGraph' v l alg) r)
  where open HFunctor functor 
\end{code}
%</foldGraph'>
\begin{code}

\end{code}
%<*foldGraph'>
\begin{code}
foldGraph' v l alg (HGraphLet e f) = l (foldGraph' v l alg e) (λ x → foldGraph' v l alg (f x)) 
foldGraph' v l alg (HGraphVar x) = v x
\end{code}
%</foldGraph'>
\begin{code}

\end{code}
%<*HGraph>
\begin{code}
data HGraph {Ip Iq : Set} (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set) ) (ixp : Ip) (ixq : Iq) : Set₁ where
  mkHGraph : ( {v : Ip -> Iq -> Set} -> (HGraph' F v ixp ixq) ) -> HGraph F ixp ixq
\end{code}
%</HGraph>
\begin{code}

\end{code}
%<*foldGraphFull>
\begin{code}
foldGraphFull :
       {Ip Iq : Set} 
    -> ∀ {F} → {{ functor : HFunctor F }} -> 
       {r : Ip -> Iq -> Set}
    -> {V : Ip -> Iq -> Set}
    -> ( {ixp : Ip} {ixq : Iq} -> V ixp ixq                     -> r ixp ixq)
    -> ( {ixp : Ip} {ixq : Iq} -> r ixp ixq -> (V ixp ixq -> r ixp ixq) -> r ixp ixq)
    -> ( {ixp : Ip} {ixq : Iq} ->        F r ixp ixq            -> r ixp ixq) 
    -> ( {ixp : Ip} {ixq : Iq} -> HGraph F   ixp ixq            -> r ixp ixq)
foldGraphFull l v alg (mkHGraph g) = foldGraph' l v alg g
\end{code}
%</foldGraphFull>
\begin{code}

\end{code}
%<*foldGraph>
\begin{code}
foldGraph :
       {Ip Iq : Set} 
    -> {F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set)} -> 
       {{ functor : HFunctor F }}    
    -> {r : Ip -> Iq -> Set}
    -> ( {ixp : Ip} {ixq : Iq} ->        F r ixp ixq -> r ixp ixq) 
    -> ( {ixp : Ip} {ixq : Iq} -> HGraph F   ixp ixq -> r ixp ixq)
foldGraph = foldGraphFull (λ v → v) (λ e f → f e)
\end{code}
%</foldGraph>
\begin{code}

\end{code}
%<*unravel>
\begin{code}
unravel : 
     {Ip Iq : Set} 
  -> ∀ {F} -> {{ functor : HFunctor F }} -> 
     {ipx : Ip} -> {ipq : Iq} 
  -> HGraph F ipx ipq -> HTree F ipx ipq
unravel = foldGraph HTreeIn
\end{code}
%</unravel>
\begin{code}

SKIP_T : ∀ {s} -> HTree BytecodeF s s
SKIP_T = HTreeIn SKIP'

\end{code}
%<*PUSH_T>
\begin{code}
PUSH_T : ∀ {α s} -> (x : ⁅ α ⁆) → HTree BytecodeF s (α ∷ s)
PUSH_T x = HTreeIn (PUSH' x) 
\end{code}
%</PUSH_T>
\begin{code}

ADD_T : ∀ {s} -> HTree BytecodeF (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
ADD_T = HTreeIn ADD'

IF_T : ∀ {s s'} -> HTree BytecodeF s s' -> HTree BytecodeF s s' -> HTree BytecodeF (𝔹ₛ ∷ s) s'
IF_T t f = HTreeIn (IF' t f)

_⟫T_  : ∀ {s₀ s₁ s₂} → (HTree BytecodeF s₀ s₁) → (HTree BytecodeF s₁ s₂) → HTree BytecodeF s₀ s₂
_⟫T_ f g = HTreeIn (f ⟫' g)

\end{code}
%<*foldSKIP>
\begin{code}
postulate foldSKIP : ∀ {r} → {{functor : HFunctor BytecodeF}} → (alg : ∀ {s s'} → BytecodeF r s s' -> r s s') -> ∀ {s} → foldTree {{functor}} alg {s} {s} (HTreeIn SKIP') ≡ alg {s} {s} SKIP'
\end{code}
%</foldSKIP>
\begin{code}

postulate foldPUSH : ∀ {r} → {{functor : HFunctor BytecodeF}} → (alg : ∀ {s s'} → BytecodeF r s s' -> r s s') -> ∀ {α} → {x : ⁅ α ⁆} → ∀ {s} → foldTree {{functor}} alg {s} {α ∷ s} (HTreeIn (PUSH' x)) ≡ alg {s} {α ∷ s} (PUSH' x)

postulate foldADD : ∀ {r} → {{functor : HFunctor BytecodeF}} → (alg : ∀ {s s'} → BytecodeF r s s' -> r s s') -> ∀ {s} → foldTree {{functor}} alg {ℕₛ ∷ ℕₛ ∷ s} {ℕₛ ∷ s} (HTreeIn ADD') ≡ alg {ℕₛ ∷ ℕₛ ∷ s} {ℕₛ ∷ s} ADD'

postulate foldIF : ∀ {r} → {{functor : HFunctor BytecodeF}} → (alg : ∀ {s s'} → BytecodeF r s s' -> r s s') -> ∀ {s s'} → ∀ t e → foldTree {{functor}} alg {𝔹ₛ ∷ s} {s'} (HTreeIn (IF' t e)) ≡ alg {𝔹ₛ ∷ s} {s'} (IF' (foldTree {{functor}} alg t) (foldTree {{functor}} alg e))

postulate fold⟫ : ∀ {r} → {{functor : HFunctor BytecodeF}} → (alg : ∀ {s s'} → BytecodeF r s s' -> r s s') -> ∀ {s₁ s₂ s₃} → (f : HTree BytecodeF s₁ s₂) (g : HTree BytecodeF s₂ s₃) → foldTree {{functor}} alg {s₁} {s₃} (HTreeIn (f ⟫' g)) ≡ alg {s₁} {s₃} (foldTree {{functor}} alg f ⟫' foldTree {{functor}} alg g)

\end{code}
%<*toTree>
\begin{code}
toTree : {ixp ixq : StackType} -> Bytecode ixp ixq -> HTree BytecodeF ixp ixq
\end{code}
%</toTree>
\begin{code}
toTree Bytecode.SKIP = HTreeIn SKIP'
toTree (Bytecode.PUSH x) = HTreeIn (PUSH' x)
toTree Bytecode.ADD = HTreeIn ADD'
toTree (Bytecode.IF bc₁ bc₂) = HTreeIn (IF' (toTree bc₁) (toTree bc₂))
toTree (bc₁ Bytecode.⟫ bc₂) = HTreeIn (toTree bc₁ ⟫' toTree bc₂)  

\end{code}
%<*fromTree>
\begin{code}
fromTree : {ixp ixq : StackType} -> HTree BytecodeF ixp ixq -> Bytecode ixp ixq
\end{code}
%</fromTree>
\begin{code}

fromTree (HTreeIn SKIP') = Bytecode.SKIP
fromTree (HTreeIn (PUSH' x)) = Bytecode.PUSH x
fromTree (HTreeIn ADD') = Bytecode.ADD
fromTree (HTreeIn (IF' t e)) = Bytecode.IF (fromTree t) (fromTree e)
fromTree (HTreeIn (c₁ ⟫' c₂)) = fromTree c₁ Bytecode.⟫ fromTree c₂

\end{code}
%<*isoToTree>
\begin{code}
treeIsoTo : {ixp ixq : StackType} -> (code : Bytecode ixp ixq) -> fromTree (toTree code) ≡ code
\end{code}
%</isoToTree>
\begin{code}
treeIsoTo SKIP = refl
treeIsoTo (PUSH x) = refl
treeIsoTo ADD = refl
treeIsoTo (IF t f) rewrite treeIsoTo t | treeIsoTo f = refl
treeIsoTo (a ⟫ b) rewrite treeIsoTo a | treeIsoTo b = refl

\end{code}
%<*isoFromTree>
\begin{code}
treeIsoFrom : {ixp ixq : StackType} -> (tree : HTree BytecodeF ixp ixq) -> toTree (fromTree tree) ≡ tree
\end{code}
%</isoFromTree>
\begin{code}
treeIsoFrom (HTreeIn SKIP') = refl
treeIsoFrom (HTreeIn (PUSH' x)) = refl
treeIsoFrom (HTreeIn ADD') = refl
treeIsoFrom (HTreeIn (IF' t f)) rewrite treeIsoFrom t | treeIsoFrom f =  refl
treeIsoFrom (HTreeIn (a ⟫' b)) rewrite treeIsoFrom a | treeIsoFrom b = refl

\end{code}
%<*execT>
\begin{code}
execT : ∀ {s s'} → HTree BytecodeF s s' -> Stack s -> Stack s'
execT = foldTree execAlg
\end{code}
%</execT>

%<*execTcorrect>
\begin{code}
execTcorrect : ∀ {s s'} → (tree : HTree BytecodeF s s') -> {t : Stack s} -> execT tree t ≡ exec (fromTree tree) t
\end{code}
%</execTcorrect>
\begin{code}

execTcorrect (HTreeIn SKIP') {t} = apply t (foldSKIP execAlg)
execTcorrect (HTreeIn (PUSH' x)) {t} = apply t (foldPUSH execAlg)
execTcorrect (HTreeIn ADD') {t} with apply t (foldADD execAlg)
execTcorrect (HTreeIn ADD') {n ▽ m ▽ s} | p = p
execTcorrect (HTreeIn (IF' t e)) {w} with apply w (foldIF execAlg t e)
execTcorrect (HTreeIn (IF' t e)) {true ▽ w}  | p = p ~ execTcorrect t
execTcorrect (HTreeIn (IF' t e)) {false ▽ w} | p = p ~ execTcorrect e
execTcorrect (HTreeIn (f ⟫' g)) {w} with apply w (fold⟫ execAlg f g)
execTcorrect (HTreeIn (f ⟫' g)) {w} | p 
  = p ~ cong' (foldTree execAlg g)   (exec (fromTree g)) 
              (foldTree execAlg f w) (exec (fromTree f) w) 
              (λ m → execTcorrect g {m}) 
              (execTcorrect f {w})

\end{code}
%<*compileT>
\begin{code}
compileT : ∀ {σ z s} → Src σ z → HTree BytecodeF s (replicate z σ ++ₗ s)
compileT (vₛ x)                  = PUSH_T x
compileT (e₁ +ₛ e₂)              = (compileT e₂ ⟫T compileT e₁) ⟫T ADD_T
\end{code}
%</compileT>
\begin{code}
compileT (ifₛ c thenₛ t elseₛ e) = compileT c ⟫T IF_T (compileT t) (compileT e)
compileT {.σ} {.(suc n + suc m)} {s} (_⟫ₛ_ {σ} {m} {n} e₁ e₂) 
    = coerce (HTree BytecodeF s)
      (lemmaConsAppend n m σ s
       ~ cong (λ l → σ ∷ l ++ₗ s) (lemmaPlusAppend n (suc m) σ))
      (compileT e₁ ⟫T compileT e₂)

mutual 
  coerceIdCompile : ∀ {m n σ} -> (f : Src σ m) -> (g : Src σ n) -> {s : StackType} -> {b : StackType} -> (p : replicate n σ ++ₗ replicate m σ ++ₗ s ≡ b) -> toTree {s} {b} (coerce (Bytecode s) p (compile f Bytecode.⟫ compile g)) 
                                  ≡ coerce (HTree BytecodeF s) p (compileT f ⟫T compileT g)
  coerceIdCompile {m} {n} {σ} f g {s} .{replicate n σ ++ₗ replicate m σ ++ₗ s} refl = cong₂ (λ x y → HTreeIn (x ⟫' y)) (compileTcorrect f) (compileTcorrect g)

  compileTcorrect : ∀ {σ z s} → (e : Src σ z) -> toTree {s} (compile e) ≡ compileT e
  compileTcorrect (vₛ v) = refl
  compileTcorrect (p +ₛ q) = cong₂ (λ a x → HTreeIn (HTreeIn (a ⟫' x) ⟫' HTreeIn ADD')) (compileTcorrect q) (compileTcorrect p)
  compileTcorrect (ifₛ c thenₛ t elseₛ e) = cong₃ (λ a x p → HTreeIn (a ⟫' HTreeIn (IF' x p))) (compileTcorrect c) (compileTcorrect t) (compileTcorrect e)
  compileTcorrect .{σ} .{suc n + suc m} {s} (_⟫ₛ_ {σ} {m} {n} f g) 
    = coerceIdCompile {suc m} {suc n} {σ} f g {s} {σ ∷ replicate (n + suc m) σ ++ₗ s} (lemmaConsAppend n m σ s ~ cong (λ l → σ ∷ l ++ₗ s) (lemmaPlusAppend n (suc m) σ))
\end{code}


\begin{code}

\end{code}
%<*SKIP_G>
\begin{code}
SKIP_G : ∀ {v s} -> HGraph' BytecodeF v s s
SKIP_G = HGraphIn SKIP'
\end{code}
%</SKIP_G>
\begin{code}

\end{code}
%<*PUSH_G>
\begin{code}
PUSH_G : ∀ {v α s} -> (x : ⁅ α ⁆) → HGraph' BytecodeF v s (α ∷ s)
PUSH_G x = HGraphIn (PUSH' x) 
\end{code}
%</PUSH_G>
\begin{code}

ADD_G : ∀ {v s} -> HGraph' BytecodeF v (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
ADD_G = HGraphIn ADD'

IF_G : ∀ {v s s'} -> HGraph' BytecodeF v s s' -> HGraph' BytecodeF v s s' -> HGraph' BytecodeF v (𝔹ₛ ∷ s) s'
IF_G t f = HGraphIn (IF' t f)

_⟫G_  : ∀ {v s₀ s₁ s₂} → (HGraph' BytecodeF v s₀ s₁) → (HGraph' BytecodeF v s₁ s₂) → HGraph' BytecodeF v s₀ s₂
_⟫G_ f g = HGraphIn (f ⟫' g)

execG : ∀ {s s'} → HGraph BytecodeF s s' -> Stack s -> Stack s'
execG = foldGraph execAlg



\end{code}
%<*compileG'>
\begin{code}
compileG' : ∀ {σ z s} → Src σ z → ∀ {v} → HGraph' BytecodeF v s (replicate z σ ++ₗ s)
\end{code}
%</compileG'>
\begin{code}
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
\end{code}



\begin{code}


-- Finally, the statement of correctness for the compiler
\end{code}
%<*prepend>
\begin{code}
prepend : ∀ {t n σ} → (v : Vec ⁅ σ ⁆ n) → Stack t → Stack (rep n σ ++ₗ t)
prepend ε        s = s
prepend (x ◁ xs) s = x ▽ prepend xs s
\end{code}
%</prepend>
\begin{code}


{-
lemmaPrepend : ∀ {m n σ t} → (v₁ : Vec ⁅ σ ⁆ m) (v₂ : Vec ⁅ σ ⁆ n) (l : Stack t) → prepend (v₁ +++ v₂) l ≡ prepend v₁ (prepend v₂ l)
lemmaPrepend v1 v2 l = {!!}
-}

\end{code}
%<*correct>
\begin{code}
correct : {σ : Tyₛ} {z : Sizeₛ} {s' : StackType} (e : Src σ z) (s : Stack s')
          → prepend ⟦ e ⟧ s ≡ exec (compile e) s
\end{code}
%</correct>
\begin{code}
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

correct {.σ} {.(suc n + suc m)} {s'} (_⟫ₛ_ {σ} {m} {n} e₁ e₂) s
 rewrite lemmaStack
         {c = (compile e₁ ⟫ compile e₂)}
         (lemmaConsAppend n m σ s' ~ cong (λ l → σ ∷ l ++ₗ s') (lemmaPlusAppend n (suc m) σ)) s
  | sym (correct e₁ s)
  | sym (correct e₂ (prepend ⟦ e₁ ⟧ s)) = {!!}


mutual
  coerceIdLemma₁ : ∀ {m n σ} -> (f : Src σ m) -> (g : Src σ n) -> {s : StackType} -> {b : StackType} -> ( p : replicate n σ ++ₗ replicate m σ ++ₗ s ≡ b )
                                   -> coerce (HTree BytecodeF s) p (compileT f ⟫T compileT g)
                                  ≡ foldGraph' (λ v → v) (λ e f → f e) (λ {ixp} {ixq} → {!!}) (coerce (HGraph' BytecodeF (HTree BytecodeF) s) p (compileG' f ⟫G compileG' g))
  coerceIdLemma₁ {m} {n} {σ} f g {s} .{replicate n σ ++ₗ replicate m σ ++ₗ s} refl 
    = cong₂ (λ x y → HTreeIn (x ⟫' y)) (Lemma₁ f) (Lemma₁ g)


  Lemma₁ : {s : StackType} 
       → ∀ {σ z} 
       → ( src : Src σ z) → compileT {σ} {z} {s} src ≡ unravel (compileG {s} src)
  Lemma₁ (vₛ v) = refl
  Lemma₁ (a +ₛ b) = cong₂ (λ x p → HTreeIn (HTreeIn (p ⟫' x) ⟫' HTreeIn ADD' )) (Lemma₁ a) (Lemma₁ b)
  Lemma₁ (ifₛ c thenₛ t elseₛ e) = cong₃ (λ x p a → HTreeIn (x ⟫' HTreeIn (IF' p a))) (Lemma₁ c) (Lemma₁ t) (Lemma₁ e)
  Lemma₁ {s} .{σ} .{suc (n + suc m)} (_⟫ₛ_ {σ} {m} {n} f g) 
    = coerceIdLemma₁ {suc m} {suc n} {σ} f g ( lemmaConsAppend n m σ s 
                                             ~ cong (λ l → σ ∷ l ++ₗ s) (lemmaPlusAppend n (suc m) σ)
                                             )

\end{code}

\begin{code}

-- prepend ⟦ e ⟧  r ≡ exec (compile e) r 
--                  ≡ exec (fromTree . toTree . compile e) r 
--                  ≡ execT (toTree . compile e) r 
--                  ≡ execT (compileT e) r

\end{code}
%<*correctT>
\begin{code}
correctT : ∀ {s σ z} → (e : Src σ z) → execT {s} (compileT e) ≡ prepend ⟦ e ⟧
\end{code}
%</correctT>
\begin{code}
correctT e = funext (λ r → sym 
               ( correct e r 
               ~ cong (λ t → exec t r) (sym (treeIsoTo (compile e))) 
               ~ sym (execTcorrect (toTree (compile e))) 
               ~ cong (λ t → execT t r) (compileTcorrect e)
               ) 
             )
\end{code}

\begin{code}

module Lifting ( IndexType : Set -> Set 
    ) ( post : (σ : Tyₛ) → (z : ℕ) → IndexType Tyₛ → IndexType Tyₛ
  ) { F : (IndexType Tyₛ -> IndexType Tyₛ -> Set) -> IndexType Tyₛ -> IndexType Tyₛ -> Set
  }{{ functor : HFunctor F
  }}( target : IndexType Tyₛ → IndexType Tyₛ → Set
  ) ( execAlg : ∀ {s s′} → F target s s′ → target s s′
  ) ( compileT : ∀ {s σ z} → Src σ z → HTree  F s (post σ z s)
  ) ( compileG : ∀ {s σ z} → Src σ z → HGraph F s (post σ z s)
  ) ( unravelLemma : ∀ {s σ z} 
                   → (src : Src σ z) → compileT {s} src ≡ unravel (compileG {s} src)
  ) ( prepend : ∀ {t n σ} → (v : Vec ⁅ σ ⁆ n) → target t (post σ n t)
  ) ( correctT : ∀ {s σ z} 
               → (e : Src σ z) → foldTree execAlg {s} {post σ z s} (compileT e) ≡ prepend ⟦ e ⟧
  )
 where

  execT' :  ∀ {s s'} → HTree F s s' -> target s s'
  execT' = foldTree execAlg

  execG' :  ∀ {s s'} → HGraph F s s' -> target s s'
  execG' = foldGraph execAlg


  Theorem :
      ∀ {r}
    → ∀ {F} → {{ functor : HFunctor F }}
    → (alg : {s s' : IndexType Tyₛ} → F r s s' → r s s')
    → {s s' : IndexType Tyₛ}
    → (graph : HGraph F s s') → foldGraph alg graph ≡ foldTree alg (unravel graph)
  Theorem alg graph = fusion (λ a → foldGraph a graph) alg


  Lemma : {s s' : IndexType Tyₛ}
        → (graph : HGraph F s s') → execG' graph ≡ execT' (unravel graph)
  Lemma graph = Theorem execAlg graph

  graphCorrectness : ∀ {s σ z}
                   → (e : Src σ z) → execG' {s} (compileG e) ≡ prepend ⟦ e ⟧ 
  graphCorrectness e = 
    let step1 = cong' (λ g → execG' g) 
             (λ g → execT' (unravel g)) 
           (compileG e) (compileG e) 
           (Lemma) refl
        step2 = cong' (λ g → execT' g) 
            (λ g → execT' g)  
            (unravel (compileG e)) (compileT e)
            (λ t → refl) (sym (unravelLemma e))
    in step1 ~ step2 ~ (correctT e)
\end{code}


%<*correctG>
\begin{code}
correctG : ∀ {s σ z}
         → (e : Src σ z) → execG {s} (compileG e) ≡ prepend ⟦ e ⟧
\end{code}
%</correctG>
\begin{code}
correctG =  graphCorrectness 
  where open Lifting List (λ σ n s → replicate n σ ++ₗ s) 
                          (λ s s' → Stack s -> Stack s')
                          execAlg 
                          compileT compileG  Lemma₁ 
                          prepend  correctT


\end{code}
