module Monads where

open import Library
open import Functors
open import Naturals
open import Categories

{- Mónadas à la Haskell (Tripletas de Kleisli) -}

record Monad {a}{b}(C : Cat {a}{b}) : Set (a ⊔ b) where
  constructor monad
  open Cat C
  field T      : Obj → Obj
        return : ∀ {X} → Hom X (T X)
        bind   : ∀{X Y} → Hom X (T Y) → Hom (T X) (T Y)
        mlaw1  : ∀{X} → bind (return {X}) ≅ iden {T X}
        mlaw2  : ∀{X Y}{f : Hom X (T Y)} → bind f ∙ return ≅ f
        mlaw3  : ∀{X Y Z}{f : Hom X (T Y)}{g : Hom Y (T Z)} → 
                  bind (bind g ∙ f)  ≅ bind g ∙ bind f


--Categoría Kleisli de una mónada
kleisliC : ∀{a b}{C : Cat {a} {b}} → (M : Monad C) → Cat {a} {b}
kleisliC {a}{b}{C} (monad T return bind mlaw1 mlaw2 mlaw3) = let open Cat C renaming (Obj to ObjC; Hom to HomC; iden to idenC; idr to idrC; idl to idlC; ass to assC) in record
                                                                                 { Obj = ObjC
                                                                                 ; Hom = λ X Y → HomC X (T Y)
                                                                                 ; iden = return
                                                                                 ; _∙_ = λ f g → (bind f) ∙ g --g va de x a ty, bind f va de ty a tz
                                                                                 ; idl = λ {x} {y} {f} → proof bind return ∙ f --iden ∙ f = f
                                                                                                                    ≅⟨ congl mlaw1 ⟩
                                                                                                                    idenC ∙ f
                                                                                                                    ≅⟨ idlC ⟩
                                                                                                                    f ∎
                                                                                 ; idr = mlaw2 --f ∙ iden = f                                     
                                                                                 ; ass = λ {w} {x} {y} {z} {f} {g} {h} → proof bind (bind f ∙ g) ∙ h --(f ∙ g) ∙ h = f ∙ (g ∙ h)
                                                                                                                                                   ≅⟨ congl mlaw3 ⟩
                                                                                                                                                   (bind f ∙ bind g) ∙ h
                                                                                                                                                   ≅⟨ assC ⟩
                                                                                                                                                   bind f ∙ bind g ∙ h ∎
                                                                                 }
