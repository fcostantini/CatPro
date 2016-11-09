module AdjMon where

  open import Library
  open import Categories
  open import Adjunctions
  open import Functors
  open import Monads

  open Cat
  open Fun
 
--y en D, x en C
--a)x -> Ry en C
--b)Lx -> y en D
--right: a -> b
--left: b -> a

  AdjToMon : ∀{a b c d}{ C : Cat {a} {b}}{ D : Cat {c}{d}} → Adj C D → Monad C
  AdjToMon {a}{b}{c}{d}{C}{D} (adjunction L R left right lawa lawb natleft natright) = monad (OMap (R ○ L))
                                                                                             (left (iden D))
                                                                                             {!!}
                                                                                             {!!}
                                                                                             {!!}
                                                                                             {!!}

  