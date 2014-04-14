{-# OPTIONS --no-positivity-check #-}
module BytecodeF where

open import Level renaming ( suc to zuc )
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_; replicate; [_]) renaming (_++_ to _++ₗ_)
open import Data.Vec using (Vec) renaming ([] to ε; _∷_ to _◁_)
open import Data.Nat using (ℕ; _+_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Source using (𝔹ₛ; ℕₛ; ⁅_⁆; Src; vₛ; _+ₛ_; ifₛ_thenₛ_elseₛ_; _⟫ₛ_; ⟦_⟧)
open import Bytecode using (_▽_; StackType; Stack; Bytecode; exec)
open import Compiler using (correct; compile; lemmaPlusAppend; _~_; lemmaConsAppend; prepend; rep; coerce)


record HFunctor {Ip Iq : Set} (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set)) : Set₁ where
  constructor isHFunctor
  field
    hmap : {a : Ip -> Iq -> Set} -> {b : Ip -> Iq -> Set} 
         -> ( {ixp : Ip} -> {ixq : Iq} ->   a ixp ixq ->   b ixp ixq )
         -> ( {ixp : Ip} -> {ixq : Iq} -> F a ixp ixq -> F b ixp ixq )  

record HTree {Ip Iq : Set} (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set) ) (ixp : Ip) (ixq : Iq) : Set where
  constructor HTreeIn
  field
    treeOut : F (HTree F) ixp ixq

data HGraph' {Ip Iq : Set} (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set) ) (v : Ip -> Iq -> Set) (ixp : Ip) (ixq : Iq) : Set where
  HGraphIn  : F (HGraph' F v) ixp ixq -> HGraph' F v ixp ixq
  HGraphLet : (HGraph' F v ixp ixq) -> (v ixp ixq -> HGraph' F v ixp ixq) -> HGraph' F v ixp ixq  
  HGraphVar : v ixp ixq -> HGraph' F v ixp ixq

data HGraph {Ip Iq : Set} (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set) ) (ixp : Ip) (ixq : Iq) : Set₁ where
  mkHGraph : ( {v : Ip -> Iq -> Set} -> (HGraph' F v ixp ixq) ) -> HGraph F ixp ixq

data BytecodeF (r : StackType -> StackType -> Set) : (StackType -> StackType -> Set) where  
    SKIP : ∀ {s}    → BytecodeF r s s
    PUSH : ∀ {α s}  → (x : ⁅ α ⁆) → BytecodeF r s (α ∷ s)
    ADD  : ∀ {s}    → BytecodeF r (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
    IF   : ∀ {s s′} → (t : r s s′) → (e : r s s′) → BytecodeF r (𝔹ₛ ∷ s) s′
    _⟫_  : ∀ {s₀ s₁ s₂} → (c₁ : r s₀ s₁) → (c₂ : r s₁ s₂) → BytecodeF r s₀ s₂
{-
Ip Iq : Set
Ip = StackType
Iq = StackType

F : (r : Ip -> Iq -> Set) -> (Ip -> Iq -> Set)
F = BytecodeF
-}

SKIP_T : ∀ {s} -> HTree BytecodeF s s
SKIP_T = HTreeIn SKIP

PUSH_T : ∀ {α s} -> (x : ⁅ α ⁆) → HTree BytecodeF s (α ∷ s)
PUSH_T x = HTreeIn (PUSH x) 

ADD_T : ∀ {s} -> HTree BytecodeF (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
ADD_T = HTreeIn ADD

IF_T : ∀ {s s'} -> HTree BytecodeF s s' -> HTree BytecodeF s s' -> HTree BytecodeF (𝔹ₛ ∷ s) s'
IF_T t f = HTreeIn (IF t f)

_⟫T_  : ∀ {s₀ s₁ s₂} → (HTree BytecodeF s₀ s₁) → (HTree BytecodeF s₁ s₂) → HTree BytecodeF s₀ s₂
_⟫T_ f g = HTreeIn (f ⟫ g)

SKIP_G : ∀ {v s} -> HGraph' BytecodeF v s s
SKIP_G = HGraphIn SKIP

PUSH_G : ∀ {v α s} -> (x : ⁅ α ⁆) → HGraph' BytecodeF v s (α ∷ s)
PUSH_G x = HGraphIn (PUSH x) 

ADD_G : ∀ {v s} -> HGraph' BytecodeF v (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
ADD_G = HGraphIn ADD

IF_G : ∀ {v s s'} -> HGraph' BytecodeF v s s' -> HGraph' BytecodeF v s s' -> HGraph' BytecodeF v (𝔹ₛ ∷ s) s'
IF_G t f = HGraphIn (IF t f)

_⟫G_  : ∀ {v s₀ s₁ s₂} → (HGraph' BytecodeF v s₀ s₁) → (HGraph' BytecodeF v s₁ s₂) → HGraph' BytecodeF v s₀ s₂
_⟫G_ f g = HGraphIn (f ⟫ g)



mapBytecodeF : {a b : StackType -> StackType -> Set} -> ( {ixp ixq : StackType} ->           a ixp ixq ->           b ixp ixq) 
                                                     -> ( {ixp ixq : StackType} -> BytecodeF a ixp ixq -> BytecodeF b ixp ixq)
mapBytecodeF f SKIP = SKIP
mapBytecodeF f (PUSH x) = PUSH x
mapBytecodeF f ADD = ADD
mapBytecodeF f (IF t e) = IF (f t) (f e)
mapBytecodeF f (_⟫_ c₁ c₂)= f c₁ ⟫ f c₂


BytecodeFunctor : HFunctor BytecodeF
BytecodeFunctor =
  record {
    hmap = mapBytecodeF
  } 

toTree : {ixp ixq : StackType} -> Bytecode ixp ixq -> HTree BytecodeF ixp ixq
toTree Bytecode.SKIP = HTreeIn SKIP
toTree (Bytecode.PUSH x) = HTreeIn (PUSH x)
toTree Bytecode.ADD = HTreeIn ADD
toTree (Bytecode.IF bc₁ bc₂) = HTreeIn (IF (toTree bc₁) (toTree bc₂))
toTree (bc₁ Bytecode.⟫ bc₂) = HTreeIn (toTree bc₁ ⟫ toTree bc₂)  

fromTree : {ixp ixq : StackType} -> HTree BytecodeF ixp ixq -> Bytecode ixp ixq
fromTree (HTreeIn SKIP) = Bytecode.SKIP
fromTree (HTreeIn (PUSH x)) = Bytecode.PUSH x
fromTree (HTreeIn ADD) = Bytecode.ADD
fromTree (HTreeIn (IF t e)) = Bytecode.IF (fromTree t) (fromTree e)
fromTree (HTreeIn (c₁ ⟫ c₂)) = fromTree c₁ Bytecode.⟫ fromTree c₂

treeIsoTo : {ixp ixq : StackType} -> (code : Bytecode ixp ixq) -> fromTree (toTree code) ≡ code
treeIsoTo Bytecode.SKIP = refl
treeIsoTo (Bytecode.PUSH x) = refl
treeIsoTo Bytecode.ADD = refl
treeIsoTo (Bytecode.IF t f) rewrite treeIsoTo t | treeIsoTo f = refl
treeIsoTo (a Bytecode.⟫ b) rewrite treeIsoTo a | treeIsoTo b = refl

treeIsoFrom : {ixp ixq : StackType} -> (tree : HTree BytecodeF ixp ixq) -> toTree (fromTree tree) ≡ tree
treeIsoFrom (HTreeIn SKIP) = refl
treeIsoFrom (HTreeIn (PUSH x)) = refl
treeIsoFrom (HTreeIn ADD) = refl
treeIsoFrom (HTreeIn (IF t f)) rewrite treeIsoFrom t | treeIsoFrom f =  refl
treeIsoFrom (HTreeIn (a ⟫ b)) rewrite treeIsoFrom a | treeIsoFrom b = refl

{-
{-# NO_TERMINATION_CHECK #-}
foldTree : 
        {Ip Iq : Set} 
     -> {F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set)} -> 
        {{ functor : HFunctor F }} 
     -> {r : Ip -> Iq -> Set} 
     -> ( {ixp : Ip} {ixq : Iq} -> F r ixp ixq -> r ixp ixq) 
     -> ( {ixp : Ip} {ixq : Iq} -> HTree F   ixp ixq -> r ixp ixq)
foldTree {{functor}} alg (HTreeIn r) = alg (hmap (foldTree alg) r) 
  where open HFunctor functor
-}

postulate foldTree : {Ip Iq : Set} -> {F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set)} -> {{ functor : HFunctor F }} -> {r : Ip -> Iq -> Set} -> ( {ixp : Ip} {ixq : Iq} -> F r ixp ixq -> r ixp ixq) -> ( {ixp : Ip} {ixq : Iq} -> HTree F   ixp ixq -> r ixp ixq)
 
-- {-# NO_TERMINATION_CHECK #-}
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

foldGraph' v l alg (HGraphLet e f) = l (foldGraph' v l alg e) (λ x → foldGraph' v l alg (f x)) 
foldGraph' v l alg (HGraphVar x) = v x

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

foldGraph :
       {Ip Iq : Set} 
    -> {F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set)} -> 
       {{ functor : HFunctor F }}    
    -> {r : Ip -> Iq -> Set}
    -> ( {ixp : Ip} {ixq : Iq} ->        F r ixp ixq -> r ixp ixq) 
    -> ( {ixp : Ip} {ixq : Iq} -> HGraph F   ixp ixq -> r ixp ixq)
foldGraph = foldGraphFull (λ v → v) (λ e f → f e)


execAlg : ∀ {s s′} → BytecodeF (λ t t' → Stack t → Stack t') s s′ → Stack s → Stack s′
execAlg SKIP        s           = s
execAlg (PUSH v)    s           = v ▽ s
execAlg ADD         (n ▽ m ▽ s) = (n + m) ▽ s
execAlg (IF t e)    (true  ▽ s) = t s
execAlg (IF t e)    (false ▽ s) = e s
execAlg (c₁ ⟫ c₂)   s           = c₂ (c₁ s)

execT : ∀ {s s'} → HTree BytecodeF s s' -> Stack s -> Stack s'
execT = foldTree execAlg

execTcorrect : ∀ {s s'} → (tree : HTree BytecodeF s s') -> exec (fromTree tree) ≡ execT tree
execTcorrect (HTreeIn SKIP) = {!!}
execTcorrect (HTreeIn (PUSH x)) = {!!}
execTcorrect (HTreeIn ADD) = {!!}
execTcorrect (HTreeIn (IF t e)) = {!!}
execTcorrect (HTreeIn (c₁ ⟫ c₂)) = {!!}


execG : ∀ {s s'} → HGraph BytecodeF s s' -> Stack s -> Stack s'
execG = foldGraph  execAlg

unravel : 
     {Ip Iq : Set} 
  -> ∀ {F} -> {{ functor : HFunctor F }} -> 
     {ipx : Ip} -> {ipq : Iq} 
  -> HGraph F ipx ipq -> HTree F ipx ipq
unravel = foldGraph HTreeIn

compileT : ∀ {σ z s} → Src σ z → HTree BytecodeF s (replicate z σ ++ₗ s)
compileT (vₛ x)                  = PUSH_T x
compileT (e₁ +ₛ e₂)              = (compileT e₂ ⟫T compileT e₁) ⟫T ADD_T
compileT (ifₛ c thenₛ t elseₛ e) = compileT c ⟫T IF_T (compileT t) (compileT e)
compileT {.σ} {.(suc n + suc m)} {s} (_⟫ₛ_ {σ} {m} {n} e₁ e₂) 
    = coerce (HTree BytecodeF s)
      (lemmaConsAppend n m σ s
       ~ cong (λ l → σ ∷ l ++ₗ s) (lemmaPlusAppend n (suc m) σ))
      (compileT e₁ ⟫T compileT e₂)


compileTcorrect : ∀ {σ z s} → (e : Src σ z) -> toTree {s} (compile e) ≡ compileT e
compileTcorrect (vₛ v) = refl
compileTcorrect (src +ₛ src₁) = {!!}
compileTcorrect (ifₛ src thenₛ src₁ elseₛ src₂) = {!!}
compileTcorrect (src ⟫ₛ src₁) = {!!}

compileG' : ∀ {σ z s} → Src σ z → ∀ {v} → HGraph' BytecodeF v s (rep z σ ++ₗ s)
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

Lemma₁ : {s : StackType} 
       → ∀ {σ z} 
       → ( src : Src σ z) → compileT {σ} {z} {s} src ≡ unravel (compileG {s} src)
Lemma₁ (vₛ v) = {!!}
Lemma₁ (src +ₛ src₁) = {!!}
Lemma₁ (ifₛ src thenₛ src₁ elseₛ src₂) = {!!}
Lemma₁ (src ⟫ₛ src₁) = {!!}

data Unit : Set where
  T : Unit

fusion : 
     ∀ {Ip Iq r} → ∀ {F} 
  -> {{ functor : HFunctor F }}
  -> (b : ∀ {c} -> ( {ixp : Ip} -> {ixq : Iq} -> F c ixp ixq -> c ixp ixq) -> {ixp : Ip} -> {ixq : Iq} -> c ixp ixq)       
  -> (alg : ∀ {ixp ixq} → F r ixp ixq → r ixp ixq)
  -> (ixp : Ip) (ixq : Iq)
  -> b alg {ixp} {ixq} ≡ foldTree alg {ixp} {ixq} (b HTreeIn {ixp} {ixq})
fusion = {!!}


Theorem :
    ∀ {Ip Iq} → ∀ {F} → 
    {{ functor : HFunctor F }} → 
    ∀ {r}
  → (alg : ∀ {ixp ixq} → F r ixp ixq → r ixp ixq)
  → {ixp : Ip} {ixq : Iq} 
  → ∀ graph → foldGraph alg {ixp} {ixq} graph ≡ foldTree alg {ixp} {ixq} (unravel graph)
Theorem alg graph =
  let r = fusion {!!} -- (λ a → foldGraph a graph)
  in {!!}

apply : {X Y : Set} -> {f g : X -> Y} -> (x : X) -> f ≡ g -> f x ≡ g x
apply x refl = refl

Lemma₂ : {s s' : StackType} → (r : Stack s) 
       → (graph : HGraph BytecodeF s s')
       →  execG graph r ≡ execT (unravel graph) r
Lemma₂ {s} {s'} r graph = apply r (Theorem execAlg graph)

-- prepend ⟦ e ⟧  r ≡ exec (compile e) r 
--                  ≡ exec (fromTree . toTree . compile e) r 
--                  ≡ execT (toTree . compile e) r 
--                  ≡ execT (compileT e) r

correctT : ∀ {σ z s'} → (e : Src σ z) 
         → ∀ (r : Stack s') → prepend ⟦ e ⟧  r ≡ execT (compileT e) r
correctT e r = correct e r 
             ~ cong (λ t → exec t r) (sym (treeIsoTo (compile e))) 
             ~ apply r (execTcorrect (toTree (compile e))) 
             ~ cong (λ t → execT t r) (compileTcorrect e)

broken_cong : {e : Level} {X : Set e} {R : Set}
     -> (P Q : X -> R)
     -> (a b : X) 
     -> ((x : X) -> P x ≡ Q x) -> a ≡ b 
     -> P a ≡ Q b
broken_cong P Q a .a f refl = f a 


correctG : ∀ {σ z s}
         → (e : Src σ z) → ∀ (r : Stack s) → execG (compileG e) r ≡ prepend ⟦ e ⟧  r
correctG e r = 
  let step1 = broken_cong (λ g → execG g r) 
         (λ g → execT (unravel g) r) 
         (compileG e) (compileG e) 
         (Lemma₂ r) refl
      step2 = broken_cong (λ g → execT g r) 
          (λ g → execT g r)  
          (unravel (compileG e)) (compileT e)
          (λ t → refl) (sym (Lemma₁ e))
  in step1 ~ step2 ~ sym (correctT e r)
