\begin{code}

open import Util
--open import Bytecode
open import HTree
open import HGraph
open import HFunctor
open import Source

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Vec using (Vec) renaming ([] to  ε; _∷_ to _◁_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import Data.List using (List; replicate; _∷_ ) renaming (_++_ to _++ₗ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

module Lifting
  { F : (List Tyₛ -> List Tyₛ -> Set) -> List Tyₛ -> List Tyₛ -> Set
  } 
  {{ functor : HFunctor F
  }}
  ( _++ₗ_ : List Tyₛ -> List Tyₛ -> List Tyₛ
  )
  ( replicate : (n : ℕ) -> Tyₛ -> (List Tyₛ)
  )
  { Stack : List Tyₛ -> Set
  }
  ( execAlg : ∀ {s s′} → F (λ t t' → Stack t → Stack t') s s′ → Stack s → Stack s′
  ) 
  { compileT : ∀ {s σ z} → Src σ z → HTree  F s (replicate z σ ++ₗ s)
  } 
  ( compileG : ∀ {s σ z} → Src σ z → HGraph F s (replicate z σ ++ₗ s)
  ) 
  ( unravelLemma : ∀ {s σ z} 
                 → (src : Src σ z) → compileT {s} src ≡ unravel (compileG {s} src)
  )
  ( prepend : ∀ {t n σ} → (v : Vec ⁅ σ ⁆ n) → Stack t → Stack (replicate n σ ++ₗ t)
  )
  ( correctT : ∀ {s σ z} → (e : Src σ z) 
             → ∀ (r : Stack s) → foldTree execAlg (compileT e) r ≡ prepend ⟦ e ⟧ r
  )
 where

execT :  ∀ {s s'} → HTree F s s' -> Stack s -> Stack s'
execT = foldTree execAlg

execG :  ∀ {s s'} → HGraph F s s' -> Stack s -> Stack s'
execG = foldGraph execAlg


Theorem :
    ∀ {Ip Iq} → ∀ {F} → 
    {{ functor : HFunctor F }} → 
    ∀ {r}
  → (alg : {ixp : Ip} → {ixq : Iq} → F r ixp ixq → r ixp ixq)
  → {ixp : Ip} {ixq : Iq} 
  → ∀ graph → foldGraph alg {ixp} {ixq} graph ≡ foldTree alg {ixp} {ixq} (unravel graph)
Theorem alg {ipx} {ipy} graph = fusion (λ a → foldGraph a graph) alg


Lemma : {s s' : List Tyₛ} → (r : Stack s) 
       → (graph : HGraph F s s')
       →  execG graph r ≡ execT (unravel graph) r
Lemma {s} {s'} r graph = apply r (Theorem execAlg graph)


graphCorrectness : ∀ {σ z s}
         → (e : Src σ z) → ∀ (r : Stack s) → execG (compileG e) r ≡ prepend ⟦ e ⟧  r
graphCorrectness e r = 
  let step1 = cong' (λ g → execG g r) 
         (λ g → execT (unravel g) r) 
         (compileG e) (compileG e) 
         (Lemma r) refl
      step2 = cong' (λ g → execT g r) 
          (λ g → execT g r)  
          (unravel (compileG e)) (compileT e)
          (λ t → refl) (sym (unravelLemma e))
  in step1 ~ step2 ~ (correctT e r)
\end{code}
