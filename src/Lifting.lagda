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
open import Data.List using (List; replicate; _∷_ ) renaming (_++_ to _++ₗ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

module Lifting
    ( IndexType : Set -> Set 
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

execT :  ∀ {s s'} → HTree F s s' -> target s s'
execT = foldTree execAlg

execG :  ∀ {s s'} → HGraph F s s' -> target s s'
execG = foldGraph execAlg


Theorem :
    ∀ {r}
  → ∀ {F} → {{ functor : HFunctor F }}
  → (alg : {s s' : IndexType Tyₛ} → F r s s' → r s s')
  → {s s' : IndexType Tyₛ}
  → (graph : HGraph F s s') → foldGraph alg graph ≡ foldTree alg (unravel graph)
Theorem alg graph = fusion (λ a → foldGraph a graph) alg


Lemma : {s s' : IndexType Tyₛ}
      → (graph : HGraph F s s') → execG graph ≡ execT (unravel graph)
Lemma graph = Theorem execAlg graph

graphCorrectness : ∀ {s σ z}
                 → (e : Src σ z) → execG {s} (compileG e) ≡ prepend ⟦ e ⟧ 
graphCorrectness e = 
  let step1 = cong' (λ g → execG g) 
         (λ g → execT (unravel g)) 
         (compileG e) (compileG e) 
         (Lemma) refl
      step2 = cong' (λ g → execT g) 
          (λ g → execT g)  
          (unravel (compileG e)) (compileT e)
          (λ t → refl) (sym (unravelLemma e))
  in step1 ~ step2 ~ (correctT e)
\end{code}
