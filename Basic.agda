module Basic where

-- In this file we "translate" into Agda the developments of the reference paper
-- "A type-correct, stack-safe, provably correct expression compiler in Epigram".

open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_; replicate; _++_)
open import Data.Vec using (Vec; [_]; head) renaming ([] to ε; _∷_ to _◁_; _++_ to _+++_)
open import Data.Nat using (ℕ; _+_; suc; zero)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)


-- First of all, as our expression language is typed, we need a language of types
-- We denote the types of the Src language with similar symbols of the corresponding types in Agda,
-- subscripted with a lower-case "s"
data Tyₛ : Set where
    ℕₛ : Tyₛ
    𝔹ₛ : Tyₛ

-- Together with defining the object language types,
-- we define a mapping from object language types into Agda types.
⁅_⁆ : (α : Tyₛ) → Set
⁅ ℕₛ ⁆ = ℕ
⁅ 𝔹ₛ ⁆ = 𝔹


-- Now we can define an inductive family for the expressions of our object language,
-- indexed by their src language type (Tyₛ). We also use subscripted notation to avoid confusion with
-- Agda's standard library symbols.
Sizeₛ : Set
Sizeₛ = ℕ

data Src : (σ : Tyₛ) → (z : Sizeₛ) → Set where
    vₛ    : ∀ {σ} → (v : ⁅ σ ⁆) → Src σ 1
    _+ₛ_  : (e₁ e₂ : Src ℕₛ 1) → Src ℕₛ 1
    ifₛ_thenₛ_elseₛ_ : ∀ {σ} → (c : Src 𝔹ₛ 1) → (eₜ eₑ : Src σ 1) → Src σ 1
    _⟫ₛ_  : ∀ {σ m n} → Src σ (suc m) → Src σ (suc n) → Src σ (suc n + suc m)

infixl 40 _+ₛ_

-- The evaluation function defined below is a denotational semantics for the src language.
-- Evaluation takes a typed expression in our src language_ to a correspondingly-typed Agda value.
-- We denote evaluation by using the usual "semantic brackets", "⟦" and "⟧".
⟦_⟧ : {σ : Tyₛ} {z : Sizeₛ} → (e : Src σ z) → Vec ⁅ σ ⁆ z
⟦ vₛ v ⟧                     = [ v ]
⟦ e₁ +ₛ e₂ ⟧                 = [ head ⟦ e₁ ⟧ + head ⟦ e₂ ⟧ ]
⟦ ifₛ_thenₛ_elseₛ_ c e₁ e₂ ⟧ = [ if (head ⟦ c ⟧) then (head ⟦ e₁ ⟧) else (head ⟦ e₂ ⟧) ]
⟦ e₁ ⟫ₛ e₂ ⟧ = ⟦ e₂ ⟧ +++ ⟦ e₁ ⟧

-- Now we move towards the second semantics for our expression language:
-- compilation to bytecode and execution of bytecode in an abstract machine.

-- First, we define "typed stacks", which are stacks indexed by lists of TyExp.
-- Each element of the stack has therefore a corresponding type.
StackType : Set
StackType = List Tyₛ

data Stack : StackType → Set where
    ε    : Stack []
    _▽_  : ∀ {σ s'} → ⁅ σ ⁆ → Stack s' → Stack (σ ∷ s')

infixr 4 _▽_

-- To complete the definition of the abstract machine,
-- we need to list the instructions of the bytecode operating on it, and give its semantics.

-- In the listing of the bytecode instructions,
-- it should be noted that each instruction is a function from typed stack to typed stack.
data Bytecode : StackType → StackType → Set where
    SKIP : ∀ {s}    → Bytecode s s
    PUSH : ∀ {σ s}  → (x : ⁅ σ ⁆) → Bytecode s (σ ∷ s)
    ADD  : ∀ {s}    → Bytecode (ℕₛ ∷ ℕₛ ∷ s) (ℕₛ ∷ s)
    IF   : ∀ {s s′} → (t : Bytecode s s′) → (e : Bytecode s s′) → Bytecode (𝔹ₛ ∷ s) s′
    _⟫_  : ∀ {s₀ s₁ s₂} → (c₁ : Bytecode s₀ s₁) → (c₂ : Bytecode s₁ s₂) → Bytecode s₀ s₂

infixl 4 _⟫_

exec : ∀ {s s′} → Bytecode s s′ → Stack s → Stack s′
exec SKIP        s           = s
exec (PUSH v)    s           = v ▽ s
exec ADD         (n ▽ m ▽ s) = (n + m) ▽ s
exec (IF t e)    (true  ▽ s) = exec t s
exec (IF t e)    (false ▽ s) = exec e s
exec (c₁ ⟫ c₂)   s           = exec c₂ (exec c₁ s)

open import Algebra
import Data.Nat.Properties as NatProps
private
  module NatCS = CommutativeSemiring NatProps.commutativeSemiring
  module STMono = Monoid (Data.List.monoid Tyₛ)
  
lemmaRepOrder : {A : Set} (m n : ℕ) (a : A)
                 → replicate m a ++ replicate n a ≡ replicate (m + n) a
lemmaRepOrder zero n a = refl
lemmaRepOrder (suc m) n a rewrite lemmaRepOrder m n a = refl

lemmaConsAppend : {A : Set} (m n : ℕ) (a : A) (s : List A)
  →   a ∷ (replicate m a ++ a ∷ replicate n a) ++ s
     ≡ a ∷ replicate m a ++ a ∷ replicate n a ++ s
lemmaConsAppend zero n a s = refl
lemmaConsAppend (suc m) n a s rewrite lemmaConsAppend m n a s = refl

lemmaPlusAppend : {A : Set} (m n : ℕ) (a : A)
    → replicate (m + n) a ≡ replicate m a ++ replicate n a
lemmaPlusAppend zero n a = refl
lemmaPlusAppend (suc m) n a rewrite lemmaPlusAppend m n a = refl


-- Now, having our source and "target" languages,
-- we are ready to define the compiler from one to the other:
compile : ∀ {σ z s} → Src σ z → Bytecode s (replicate z σ ++ s)
compile (vₛ x)                  = PUSH x
compile (e₁ +ₛ e₂)              = compile e₂ ⟫ compile e₁ ⟫ ADD
compile (ifₛ c thenₛ t elseₛ e) = compile c ⟫ IF (compile t) (compile e)
compile {.σ} {.(suc n + suc m)} {s} (_⟫ₛ_ {σ} {m} {n} e₁ e₂)
    rewrite lemmaPlusAppend n (suc m) σ
          | lemmaConsAppend n m σ s
    = compile e₁ ⟫ compile e₂


prepend : {t : StackType} {n : Sizeₛ} {σ : Tyₛ}
              (v : Vec ⁅ σ ⁆ n) → Stack t → Stack (replicate n σ ++ t)
prepend ε        s = s
prepend (x ◁ xs) s = x ▽ prepend xs s


correct : ∀ {σ z s'} (e : Src σ z) (s : Stack s') → prepend ⟦ e ⟧ s ≡ exec (compile e) s
correct (vₛ v) s = refl

correct (x +ₛ y) s
    rewrite sym (correct y s)
          | sym (correct x (prepend ⟦ y ⟧ s))
    with ⟦ x ⟧ | ⟦ y ⟧
... | x' ◁ ε | y' ◁ ε = refl

correct (ifₛ c thenₛ t elseₛ e) s with (exec (compile c) s) | sym (correct c s)
correct (ifₛ c thenₛ t elseₛ e) s | .(prepend ⟦ c ⟧ s) | refl with ⟦ c ⟧
correct (ifₛ c thenₛ t elseₛ e) s | .(prepend ⟦ c ⟧ s) | refl | true  ◁ ε with (exec (compile t) s) | sym (correct t s)
correct (ifₛ c thenₛ t elseₛ e) s | .(prepend ⟦ c ⟧ s) | refl | true  ◁ ε | .(prepend ⟦ t ⟧ s) | refl with ⟦ t ⟧
correct (ifₛ c thenₛ t elseₛ e) s | .(prepend ⟦ c ⟧ s) | refl | true  ◁ ε | .(prepend ⟦ t ⟧ s) | refl | t' ◁ ε = refl
correct (ifₛ c thenₛ t elseₛ e) s | .(prepend ⟦ c ⟧ s) | refl | false ◁ ε with (exec (compile e) s) | sym (correct e s)
correct (ifₛ c thenₛ t elseₛ e) s | .(prepend ⟦ c ⟧ s) | refl | false ◁ ε | .(prepend ⟦ e ⟧ s) | refl with ⟦ e ⟧
correct (ifₛ c thenₛ t elseₛ e) s | .(prepend ⟦ c ⟧ s) | refl | false ◁ ε | .(prepend ⟦ e ⟧ s) | refl | e' ◁ ε = refl

correct {.σ} {.(suc n + suc m)} {s'} (_⟫ₛ_ {σ} {m} {n} e₁ e₂) s = {!!}

--compile {.σ} {.(suc n + suc m)} {s} (_⟫ₛ_ {σ} {m} {n} e₁ e₂)
--    rewrite lemmaPlusAppend n (suc m) σ
--          | lemmaConsAppend n m σ s
--    = compile e₁ ⟫ compile e₂

--lemmaPlusAppend : {A : Set} (m n : ℕ) (a : A)
--    → replicate (m + n) a ≡ replicate m a ++ replicate n a

--lemmaConsAppend : {A : Set} (m n : ℕ) (a : A) (s : List A)
--  →   a ∷ (replicate m a ++ a ∷ replicate n a) ++ s
--     ≡ a ∷ replicate m a ++ a ∷ replicate n a ++ s
