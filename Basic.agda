module Basic where

-- In this file we "translate" into Agda the developments of the reference paper
-- "A type-correct, stack-safe, provably correct expression compiler in Epigram".

open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_; replicate; _++_; [_])
open import Data.Vec using (Vec) renaming ([] to ε; _∷_ to _◁_)
open import Data.Nat using (ℕ; _+_; suc)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)


-- First of all, as our expression language is typed, we need a language of types
-- We denote the types of the Src language with similar symbols of the corresponding types in Agda,
-- subscripted with a lower-case "s"
data TyScalarₛ : Set where
    ℕₛ : TyScalarₛ
    𝔹ₛ : TyScalarₛ

data Tyₛ : Set where
    Sₛ   : (α : TyScalarₛ) → Tyₛ
    Vecₛ : (β : TyScalarₛ) → (n : ℕ) → Tyₛ

-- Together with defining the object language types,
-- we define a mapping from object language types into Agda types.
⁅_⁆' : (α : TyScalarₛ) → Set
⁅ ℕₛ ⁆' = ℕ
⁅ 𝔹ₛ ⁆' = 𝔹

⁅_⁆ : (σ : Tyₛ) → Set
⁅ Sₛ σ      ⁆ = ⁅ σ ⁆'
⁅ Vecₛ σ n  ⁆ = Vec ⁅ σ ⁆' n


-- Now we can define an inductive family for the expressions of our object language,
-- indexed by their src language type (Tyₛ). We also use subscripted notation to avoid confusion with
-- Agda's standard library symbols.
data Src : (σ : Tyₛ) → Set where
    vₛ              : ∀ {α} → (v : ⁅ α ⁆') → Src (Sₛ α)
    _+ₛ_            : (e₁ e₂ : Src (Sₛ ℕₛ)) → Src (Sₛ ℕₛ)
    ifₛ_thenₛ_elseₛ_ : ∀ {σ} → (c : Src (Sₛ 𝔹ₛ)) → (eₜ eₑ : Src σ) → Src σ
    εₛ      : ∀ {α} → Src (Vecₛ α 0)
    _◁ₛ_    : ∀ {α n} → (x : Src (Sₛ α)) → (xs : Src (Vecₛ α n)) → Src (Vecₛ α (suc n))

infixl 40 _+ₛ_
infixl 30 _◁ₛ_ 

-- The evaluation function defined below is a denotational semantics for the src language.
-- Evaluation takes a typed expression in our src language_ to a correspondingly-typed Agda value.
-- We denote evaluation by using the usual "semantic brackets", "⟦" and "⟧".
⟦_⟧ : {σ : Tyₛ} → (e : Src σ) → ⁅ σ ⁆
⟦ vₛ v ⟧                     = v
⟦ e₁ +ₛ e₂ ⟧                 = ⟦ e₁ ⟧ + ⟦ e₂ ⟧
⟦ ifₛ_thenₛ_elseₛ_ c e₁ e₂ ⟧ = if ⟦ c ⟧ then ⟦ e₁ ⟧ else ⟦ e₂ ⟧
⟦ εₛ ⟧                       = ε
⟦ x ◁ₛ xs ⟧                  = ⟦ x ⟧ ◁ ⟦ xs ⟧


-- Now we move towards the second semantics for our expression language:
-- compilation to bytecode and execution of bytecode in an abstract machine.

-- First, we define "typed stacks", which are stacks indexed by lists of TyExp.
-- Each element of the stack has therefore a corresponding type.
StackType : Set
StackType = List TyScalarₛ

toStackType : Tyₛ → StackType
toStackType (Sₛ α)     = [ α ]
toStackType (Vecₛ α n) = replicate n α

data Stack : StackType → Set where
    ε    : Stack []
    _▽_  : ∀ {α σ'} → ⁅ α ⁆' → Stack σ' → Stack (α ∷ σ')

infixr 4 _▽_

-- To complete the definition of the abstract machine,
-- we need to list the instructions of the bytecode operating on it, and give its semantics.

-- In the listing of the bytecode instructions,
-- it should be noted that each instruction is a function from typed stack to typed stack.
data Bytecode : StackType → StackType → Set where
    SKIP : ∀ {s}    → Bytecode s s
    PUSH : ∀ {α s}  → (x : ⁅ α ⁆') → Bytecode s (α ∷ s)
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

-- Now, having our source and "target" languages,
-- we are ready to define the compiler from one to the other:
compile : ∀ {σ s} → Src σ → Bytecode s (toStackType σ ++ s)
compile (vₛ x)                  = PUSH x
compile (e₁ +ₛ e₂)              = compile e₂ ⟫ compile e₁ ⟫ ADD
compile (ifₛ c thenₛ t elseₛ e) = compile c ⟫ IF (compile t) (compile e)
compile εₛ                      = SKIP
compile (x ◁ₛ xs)               = compile xs ⟫ compile x


evalPrepend : {t : StackType} {σ : Tyₛ} (v : ⁅ σ ⁆) → Stack t → Stack (toStackType σ ++ t)
evalPrepend {t} {Sₛ α}      v s =  v ▽ s
evalPrepend {t} {Vecₛ β .0} ε s = s
evalPrepend {t} {Vecₛ β (suc m)} (x ◁ xs) s = x ▽ evalPrepend {t} {Vecₛ β m} xs s


correctSc : {α : TyScalarₛ} {s' : StackType} (e : Src (Sₛ α)) (s : Stack s')
                → ⟦ e ⟧ ▽ s ≡ exec (compile e) s
correctSc (vₛ v) s = refl
correctSc (e₁ +ₛ e₂) s
  rewrite sym (correctSc e₂ s)
        | sym (correctSc e₁ (⟦ e₂ ⟧ ▽ s)) = refl
correctSc (ifₛ c thenₛ t elseₛ e) s
  rewrite sym (correctSc c s) with ⟦ c ⟧
... | true  = correctSc t s
... | false = correctSc e s


-- The correctness proof for the simple, tree-based bytecode.
correct : ∀ {σ s'} → (e : Src σ) → (s : Stack s')
          → evalPrepend {s'} {σ} ⟦ e ⟧  s ≡ exec (compile e) s
correct {Sₛ α}           e s = correctSc e s
correct {Vecₛ β n}       (ifₛ c thenₛ t elseₛ e) s
  rewrite sym (correctSc c s) with ⟦ c ⟧
... | true  = correct t s
... | false = correct e s
correct {Vecₛ β .0}      εₛ s = refl
correct {Vecₛ β (suc m)} {s'} (x ◁ₛ xs) s
    rewrite sym (correct xs s)
          | sym (correctSc x (evalPrepend {s'} {Vecₛ β m} ⟦ xs ⟧ s)) = refl
