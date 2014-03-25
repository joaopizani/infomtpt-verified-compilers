module GraphCompiler where

open import Data.Nat using (ℕ; _+_)


data Maybe (α : Set) : Set where
    Nothing : Maybe α
    Just    : α → Maybe α


data SrcCode : Set where
    V     : ℕ → SrcCode
    _+₀_  : SrcCode → SrcCode → SrcCode
    throw : SrcCode
    catch : SrcCode → SrcCode → SrcCode

⟦_⟧ : SrcCode → Maybe ℕ
⟦ V n ⟧   = Just n
⟦ throw ⟧ = Nothing
⟦ catch e h ⟧ with ⟦ e ⟧
⟦ catch e h ⟧ | Nothing = Nothing
⟦ catch e h ⟧ | Just n  = Just n
⟦ e₁ +₀ e₂ ⟧ with ⟦ e₁ ⟧
⟦ e₁ +₀ e₂ ⟧ | Nothing = Nothing
⟦ e₁ +₀ e₂ ⟧ | Just n  with ⟦ e₂ ⟧
⟦ e₁ +₀ e₂ ⟧ | Just n  | Nothing = Nothing
⟦ e₁ +₀ e₂ ⟧ | Just n  | Just m  = Just (n + m)


data Bytecode : Set where  -- CPS
    PUSH   : ℕ → Bytecode → Bytecode
    ADD    : Bytecode → Bytecode
    HALT   : Bytecode
    MARK   : Bytecode → Bytecode → Bytecode
    UNMARK : Bytecode → Bytecode
    THROW  : Bytecode

-- Low-precedence right-associative function application helper, to make Bytecode look nicer
_▷_ : {α β : Set} → (α → β) → α → β
f ▷ x = f x

infixr 1 _▷_

compileCPS : SrcCode → Bytecode → Bytecode
compileCPS (V n)       c = PUSH n ▷ c
compileCPS (e₁ +₀ e₂)  c = compileCPS e₁ ▷ compileCPS e₂ ▷ ADD ▷ c
compileCPS throw       c = THROW
compileCPS (catch e h) c = MARK (compileCPS h c) ▷ compileCPS e (UNMARK c)

compile : SrcCode → Bytecode
compile e = compileCPS e ▷ HALT


open import Data.List using (List; _∷_)

mutual
    Stack : Set
    Stack = List StackItem

    data StackItem : Set where
        VAL : ℕ → StackItem
        HAN : (Stack → Stack) → StackItem

-- TODO: Problem with positivity AGAIN. Also, let's use *typed* stacks and *typed* bytecode?
