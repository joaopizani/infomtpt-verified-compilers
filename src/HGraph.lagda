\begin{code}
{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --allow-unsolved-metas #-}
module HGraph where

open import HFunctor using ( HFunctor )
open import HTree

data HGraph' {Ip Iq : Set} (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set) ) (v : Ip -> Iq -> Set) (ixp : Ip) (ixq : Iq) : Set where
  HGraphIn  : F (HGraph' F v) ixp ixq -> HGraph' F v ixp ixq
  HGraphLet : (HGraph' F v ixp ixq) -> (v ixp ixq -> HGraph' F v ixp ixq) -> HGraph' F v ixp ixq  
  HGraphVar : v ixp ixq -> HGraph' F v ixp ixq

{-# NO_TERMINATION_CHECK #-}
foldGraph' :
       {Ip Iq : Set} 
    -> {F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set)} ->
       {{ functor : HFunctor F }}
    -> {V : Ip -> Iq -> Set}      
    -> {r : Ip -> Iq -> Set}
    -> ( {ixp : Ip} {ixq : Iq} -> V ixp ixq -> r ixp ixq )
    -> ( {ixp : Ip} {ixq : Iq} -> r ixp ixq -> (V ixp ixq -> r ixp ixq) -> r ixp ixq)
    -> ( {ixp : Ip} {ixq : Iq} ->         F r ixp ixq -> r ixp ixq) 
    -> ( {ixp : Ip} {ixq : Iq} -> HGraph' F V ixp ixq -> r ixp ixq)
foldGraph' {{functor}} v l alg (HGraphIn r) = alg (hmap (foldGraph' v l alg) r)
  where open HFunctor.HFunctor functor 

foldGraph' v l alg (HGraphLet e f) = l (foldGraph' v l alg e) (λ x → foldGraph' v l alg (f x)) 
foldGraph' v l alg (HGraphVar x) = v x


data HGraph {Ip Iq : Set} (F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set) ) (ixp : Ip) (ixq : Iq) : Set₁ where
  mkHGraph : ( {v : Ip -> Iq -> Set} -> (HGraph' F v ixp ixq) ) -> HGraph F ixp ixq

foldGraphFull :
       {Ip Iq : Set} 
    -> ∀ {F} → {{ functor : HFunctor F }} -> 
       {r : Ip -> Iq -> Set}
    -> {V : Ip -> Iq -> Set}
    -> ( {ixp : Ip} {ixq : Iq} -> V ixp ixq                     -> r ixp ixq)
    -> ( {ixp : Ip} {ixq : Iq} -> r ixp ixq -> (V ixp ixq -> r ixp ixq) -> r ixp ixq)
    -> ( {ixp : Ip} {ixq : Iq} ->        F r ixp ixq            -> r ixp ixq) 
    -> ( {ixp : Ip} {ixq : Iq} -> HGraph F   ixp ixq            -> r ixp ixq)
foldGraphFull l v alg (mkHGraph g) = foldGraph' l v alg g

foldGraph :
       {Ip Iq : Set} 
    -> {F : (Ip -> Iq -> Set) -> (Ip -> Iq -> Set)} -> 
       {{ functor : HFunctor F }}    
    -> {r : Ip -> Iq -> Set}
    -> ( {ixp : Ip} {ixq : Iq} ->        F r ixp ixq -> r ixp ixq) 
    -> ( {ixp : Ip} {ixq : Iq} -> HGraph F   ixp ixq -> r ixp ixq)
foldGraph = foldGraphFull (λ v → v) (λ e f → f e)

unravel : 
     {Ip Iq : Set} 
  -> ∀ {F} -> {{ functor : HFunctor F }} -> 
     {ipx : Ip} -> {ipq : Iq} 
  -> HGraph F ipx ipq -> HTree F ipx ipq
unravel = foldGraph HTreeIn
\end{code}
