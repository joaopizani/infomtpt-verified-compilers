\begin{code}
module Source where

open import Data.Bool using (if_then_else_) renaming (Bool to 𝔹)
open import Data.Vec using (Vec; [_]; head) renaming (_++_ to _+++_)
open import Data.Nat using (ℕ; _+_; suc)



-- First of all, as our expression language is typed, we need a language of types
-- We denote the types of the Src language with similar symbols of the
-- corresponding types in Agda, subscripted with a lower-case "s"
\end{code}
%<*tys>
\begin{code}
data Tyₛ : Set where
    ℕₛ : Tyₛ
    𝔹ₛ : Tyₛ
\end{code}
%</tys>

-- Together with defining the object language types,
-- we define a mapping from object language types into Agda types.
⁅_⁆ : (α : Tyₛ) → Set
⁅ ℕₛ ⁆ = ℕ
⁅ 𝔹ₛ ⁆ = 𝔹

-- Now we can define an inductive family for the expressions of our object language,
-- indexed by their src language type (Tyₛ). We also use subscripted notation
-- to avoid confusion with Agda's standard library symbols.
Sizeₛ : Set
Sizeₛ = ℕ

data Src : (σ : Tyₛ) → (z : Sizeₛ) → Set where
    vₛ    : ∀ {σ} → (v : ⁅ σ ⁆) → Src σ 1
    _+ₛ_  : (e₁ e₂ : Src ℕₛ 1) → Src ℕₛ 1
    ifₛ_thenₛ_elseₛ_ : ∀ {σ n} → (c : Src 𝔹ₛ 1)
                        → (eₜ eₑ : Src σ (suc n)) → Src σ (suc n)
    _⟫ₛ_  : ∀ {σ m n} → Src σ (suc m) → Src σ (suc n) → Src σ (suc n + suc m)

infixl 40 _+ₛ_



-- The evaluation function defined below is a denotational semantics for the src language.
-- Evaluation takes a typed expression in our src language_ to a typed Agda value.
-- We denote evaluation by using the usual "semantic brackets", "⟦" and "⟧".
mutual
    ⟦_⟧ : {σ : Tyₛ} {z : Sizeₛ} → (e : Src σ z) → Vec ⁅ σ ⁆ z
    ⟦ vₛ v ⟧                     = [ v ]
    ⟦ e₁ +ₛ e₂ ⟧                 = [ ⟦ e₁ ⟧' + ⟦ e₂ ⟧' ] 
    ⟦ ifₛ_thenₛ_elseₛ_ c e₁ e₂ ⟧ = if ⟦ c ⟧' then ⟦ e₁ ⟧ else ⟦ e₂ ⟧
    ⟦ e₁ ⟫ₛ e₂ ⟧                 = ⟦ e₂ ⟧ +++ ⟦ e₁ ⟧

    ⟦_⟧' : {σ : Tyₛ} {z' : Sizeₛ} → (e : Src σ (suc z')) → ⁅ σ ⁆
    ⟦ e ⟧' = head ⟦ e ⟧
\end{code}
