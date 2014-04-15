module BytecodeHTree where

open import Source using ( Src;  vₛ; _+ₛ_; ifₛ_thenₛ_elseₛ_; _⟫ₛ_; ⁅_⁆; 𝔹ₛ; ℕₛ )

open import Bytecode using (_▽_; Stack; StackType; exec; execAlg)
open import Bytecode using (Bytecode;  SKIP ; PUSH ; ADD ; IF ; _⟫_ )
open import Bytecode using (BytecodeF; SKIP'; PUSH'; ADD'; IF'; _⟫'_; BytecodeFunctor)
open import Compiler using (compile)

open import HFunctor using ( HFunctor )
open import HTree using ( HTree; HTreeIn; foldTree )


open import Data.Bool using ( true; false )

open import Data.Nat using (ℕ; _+_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Data.List using (List; []; _∷_; replicate; [_]) renaming (_++_ to _++ₗ_)

open import Util using ( apply; _~_; cong₃; cong'; coerce; lemmaConsAppend; lemmaPlusAppend )



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


postulate foldSKIP : ∀ {r} → {{functor : HFunctor BytecodeF}} → (alg : ∀ {s s'} → BytecodeF r s s' -> r s s') -> ∀ {s} → foldTree {{functor}} alg {s} {s} (HTreeIn SKIP') ≡ alg {s} {s} SKIP'

postulate foldPUSH : ∀ {r} → {{functor : HFunctor BytecodeF}} → (alg : ∀ {s s'} → BytecodeF r s s' -> r s s') -> ∀ {α} → {x : ⁅ α ⁆} → ∀ {s} → foldTree {{functor}} alg {s} {α ∷ s} (HTreeIn (PUSH' x)) ≡ alg {s} {α ∷ s} (PUSH' x)

postulate foldADD : ∀ {r} → {{functor : HFunctor BytecodeF}} → (alg : ∀ {s s'} → BytecodeF r s s' -> r s s') -> ∀ {s} → foldTree {{functor}} alg {ℕₛ ∷ ℕₛ ∷ s} {ℕₛ ∷ s} (HTreeIn ADD') ≡ alg {ℕₛ ∷ ℕₛ ∷ s} {ℕₛ ∷ s} ADD'

postulate foldIF : ∀ {r} → {{functor : HFunctor BytecodeF}} → (alg : ∀ {s s'} → BytecodeF r s s' -> r s s') -> ∀ {s s'} → ∀ t e → foldTree {{functor}} alg {𝔹ₛ ∷ s} {s'} (HTreeIn (IF' t e)) ≡ alg {𝔹ₛ ∷ s} {s'} (IF' (foldTree {{functor}} alg t) (foldTree {{functor}} alg e))

postulate fold⟫ : ∀ {r} → {{functor : HFunctor BytecodeF}} → (alg : ∀ {s s'} → BytecodeF r s s' -> r s s') -> ∀ {s₁ s₂ s₃} → (f : HTree BytecodeF s₁ s₂) (g : HTree BytecodeF s₂ s₃) → foldTree {{functor}} alg {s₁} {s₃} (HTreeIn (f ⟫' g)) ≡ alg {s₁} {s₃} (foldTree {{functor}} alg f ⟫' foldTree {{functor}} alg g)


toTree : {ixp ixq : StackType} -> Bytecode ixp ixq -> HTree BytecodeF ixp ixq
toTree Bytecode.SKIP = HTreeIn SKIP'
toTree (Bytecode.PUSH x) = HTreeIn (PUSH' x)
toTree Bytecode.ADD = HTreeIn ADD'
toTree (Bytecode.IF bc₁ bc₂) = HTreeIn (IF' (toTree bc₁) (toTree bc₂))
toTree (bc₁ Bytecode.⟫ bc₂) = HTreeIn (toTree bc₁ ⟫' toTree bc₂)  

fromTree : {ixp ixq : StackType} -> HTree BytecodeF ixp ixq -> Bytecode ixp ixq
fromTree (HTreeIn SKIP') = Bytecode.SKIP
fromTree (HTreeIn (PUSH' x)) = Bytecode.PUSH x
fromTree (HTreeIn ADD') = Bytecode.ADD
fromTree (HTreeIn (IF' t e)) = Bytecode.IF (fromTree t) (fromTree e)
fromTree (HTreeIn (c₁ ⟫' c₂)) = fromTree c₁ Bytecode.⟫ fromTree c₂

treeIsoTo : {ixp ixq : StackType} -> (code : Bytecode ixp ixq) -> fromTree (toTree code) ≡ code
treeIsoTo SKIP = refl
treeIsoTo (PUSH x) = refl
treeIsoTo ADD = refl
treeIsoTo (IF t f) rewrite treeIsoTo t | treeIsoTo f = refl
treeIsoTo (a ⟫ b) rewrite treeIsoTo a | treeIsoTo b = refl

treeIsoFrom : {ixp ixq : StackType} -> (tree : HTree BytecodeF ixp ixq) -> toTree (fromTree tree) ≡ tree
treeIsoFrom (HTreeIn SKIP') = refl
treeIsoFrom (HTreeIn (PUSH' x)) = refl
treeIsoFrom (HTreeIn ADD') = refl
treeIsoFrom (HTreeIn (IF' t f)) rewrite treeIsoFrom t | treeIsoFrom f =  refl
treeIsoFrom (HTreeIn (a ⟫' b)) rewrite treeIsoFrom a | treeIsoFrom b = refl

execT : ∀ {s s'} → HTree BytecodeF s s' -> Stack s -> Stack s'
execT = foldTree execAlg

execTcorrect : ∀ {s s'} → (tree : HTree BytecodeF s s') -> {t : Stack s} -> execT tree t ≡ exec (fromTree tree) t
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

compileT : ∀ {σ z s} → Src σ z → HTree BytecodeF s (replicate z σ ++ₗ s)
compileT (vₛ x)                  = PUSH_T x
compileT (e₁ +ₛ e₂)              = (compileT e₂ ⟫T compileT e₁) ⟫T ADD_T
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
