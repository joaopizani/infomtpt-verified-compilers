\begin{code}
module Correctness where

open import Source
open import Bytecode
open import Compiler

open import HTree
open import HGraph
open import HFunctor

open import BytecodeHTree
open import BytecodeHGraph

open import Util


open import Data.Bool using (true; false)
open import Data.List using (List; replicate; _∷_ ) renaming (_++_ to _++ₗ_)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Vec using (Vec) renaming ([] to  ε; _∷_ to _◁_; _++_ to _+++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Relation.Binary.HeterogeneousEquality using (_≅_) renaming (cong to hcong; trans to htrans)



-- Finally, the statement of correctness for the compiler
prepend : ∀ {t n σ} → (v : Vec ⁅ σ ⁆ n) → Stack t → Stack (rep n σ ++ₗ t)
prepend ε        s = s
prepend (x ◁ xs) s = x ▽ prepend xs s


lemmaPrepend : ∀ {m n σ t} → (v₁ : Vec ⁅ σ ⁆ m) (v₂ : Vec ⁅ σ ⁆ n) (l : Stack t) → prepend (v₁ +++ v₂) l ≅ prepend v₁ (prepend v₂ l)
lemmaPrepend v1 v2 l = {!!}


_~~_ : {A : Set} {B : Set} {C : Set}
      {x : A} {y : B} {z : C} →
      x ≅ y → y ≅ z → x ≅ z
_~~_ = htrans

fall : {P : Set} {p : P} {q : P} → (p ≅ q) -> (p ≡ q)
fall Relation.Binary.HeterogeneousEquality.refl = refl

correct : {σ : Tyₛ} {z : Sizeₛ} {s' : StackType} (e : Src σ z) (s : Stack s')
          → prepend ⟦ e ⟧ s ≡ exec (compile e) s

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
  | sym (correct e₂ (prepend ⟦ e₁ ⟧ s)) = fall (lemmaPrepend ⟦ e₂ ⟧ ⟦ e₁ ⟧ s ~~ {!!})



mutual
  coerceIdunravelLemma : ∀ {m n σ} -> (f : Src σ m) -> (g : Src σ n) -> {s : StackType} -> {b : StackType} -> ( p : replicate n σ ++ₗ replicate m σ ++ₗ s ≡ b )
                                   -> coerce (HTree BytecodeF s) p (compileT f ⟫T compileT g)
                                  ≡ foldGraph' (λ v → v) (λ e f → f e) (λ {ixp} {ixq} t → HTreeIn {!!}) (coerce (HGraph' BytecodeF (HTree BytecodeF) s) p (compileG' f ⟫G compileG' g))
  coerceIdunravelLemma {m} {n} {σ} f g {s} .{replicate n σ ++ₗ replicate m σ ++ₗ s} refl 
    = cong₂ (λ x y → HTreeIn (x ⟫' y)) (unravelLemma f) (unravelLemma g)


  unravelLemma : ∀ {s σ z} 
       → ( src : Src σ z) → compileT {s} src ≡ unravel (compileG {s} src)
  unravelLemma (vₛ v) = refl
  unravelLemma (a +ₛ b) = cong₂ (λ x p → HTreeIn (HTreeIn (p ⟫' x) ⟫' HTreeIn ADD' )) (unravelLemma a) (unravelLemma b)
  unravelLemma (ifₛ c thenₛ t elseₛ e) = cong₃ (λ x p a → HTreeIn (x ⟫' HTreeIn (IF' p a))) (unravelLemma c) (unravelLemma t) (unravelLemma e)
  unravelLemma {s} .{σ} .{suc (n + suc m)} (_⟫ₛ_ {σ} {m} {n} f g) 
    = coerceIdunravelLemma {suc m} {suc n} {σ} f g ( lemmaConsAppend n m σ s 
                                             ~ cong (λ l → σ ∷ l ++ₗ s) (lemmaPlusAppend n (suc m) σ)
                                             )

correctT : ∀ {s σ z} → (e : Src σ z) → execT {s} (compileT e) ≡ prepend ⟦ e ⟧
correctT e = funext (λ r → sym 
               ( correct e r 
               ~ cong (λ t → exec t r) (sym (treeIsoTo (compile e))) 
               ~ sym (execTcorrect (toTree (compile e))) 
               ~ cong (λ t → execT t r) (compileTcorrect e)
               ) 
             )


correctG : ∀ {s σ z}
            → (e : Src σ z) → execG {s} (compileG e) ≡ prepend ⟦ e ⟧
correctG = graphCorrectness
  where open import Lifting List (λ σ n s → replicate n σ ++ₗ s) 
                            (λ s s' → Stack s -> Stack s')
                            execAlg 
                            compileT compileG  unravelLemma
                            prepend  correctT




\end{code}
