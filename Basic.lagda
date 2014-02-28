In this file we "translate" the developments of the reference paper
"A type-correct, stack-safe, provably correct expression compiler in Epigram" into Agda.

\begin{code}
module Basic where
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
    V              : ∀ {t} → (v : ⁅ t ⁆) → Exp t
    _+ₒ_            : (e₁ e₂ : Exp ℕₒ) → Exp ℕₒ
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
⟦ V v ⟧                    = v
⟦ e₁ +ₒ e₂ ⟧                = ⟦ e₁ ⟧ + ⟦ e₂ ⟧
⟦ ifₒ_thenₒ_elseₒ_ c e₁ e₂ ⟧ = if ⟦ c ⟧ then ⟦ e₁ ⟧ else ⟦ e₂ ⟧ 
\end{code}
