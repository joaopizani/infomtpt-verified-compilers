{-# OPTIONS --no-positivity-check #-}


module HTree where

open import HFunctor
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)


record HTree {Ip Iq : Set} (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set) ) (ixp : Ip) (ixq : Iq) : Set where
  constructor HTreeIn
  field
    treeOut : F (HTree F) ixp ixq
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

{-
fusion : 
     ∀ {Ip Iq r} 
  -> ∀ {F} -> {{ functor : HFunctor F }}
  -> {ixp : Ip} {ixq : Iq}
  -> (b : ∀ {c} -> ( {ixP : Ip} -> {ixQ : Iq} -> F c ixP ixQ -> c ixP ixQ) -> c ixp ixq)       
  -> (alg : ∀ {ixp ixq} → F r ixp ixq → r ixp ixq)
  -> b alg ≡ foldTree alg {ixp} {ixq} (b HTreeIn)
fusion {_} {_} {_} {{_}} {ixp} {ixq} b alg with alg {ixp} {ixq}
... | alg' = {!!}
-}

postulate fusion : ∀ {Ip Iq r} -> ∀ {F} -> {{ functor : HFunctor F }} -> {ixp : Ip} {ixq : Iq}-> (b : ∀ {c} -> ( {ixP : Ip} -> {ixQ : Iq} -> F c ixP ixQ -> c ixP ixQ) -> c ixp ixq) -> (alg : ∀ {ixp ixq} → F r ixp ixq → r ixp ixq) -> b alg ≡ foldTree alg {ixp} {ixq} (b HTreeIn)

