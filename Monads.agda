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
kleisliC {a}{b}{C} (monad T return bind mlaw1 mlaw2 mlaw3) = let open Cat C renaming (_∙_ to _∙C_; Obj to ObjC; Hom to HomC; iden to idenC; idr to idrC; idl to idlC; ass to assC) in record
                                                                                 { Obj = ObjC
                                                                                 ; Hom = λ X Y → HomC X (T Y) --un homomorfismo de X a Y es uno de X a TY en C
                                                                                 ; iden = return -- X en X => X en TX en C
                                                                                 ; _∙_ = λ f g → (bind f) ∙C g --g va de X a TY, f va de Y a TZ => bind f va de TY a TZ
                                                                                 ; idl = λ {x} {y} {f} → proof --iden ∙ f ≅ f o sea (bind return) ∙C f ≅ f
                                                                                                                    bind return ∙C f
                                                                                                                    ≅⟨ cong₂ _∙C_ mlaw1 refl ⟩
                                                                                                                    idenC ∙C f
                                                                                                                    ≅⟨ idlC ⟩
                                                                                                                    f ∎
                                                                                 ; idr = mlaw2 -- f ∙ iden ≅ f  o sea (bind f) ∙C return ≅ f                                  
                                                                                 ; ass = λ {w} {x} {y} {z} {f} {g} {h} → proof --(f ∙ g) ∙ h ≅ f ∙ (g ∙ h) o sea bind (bind f ∙C g) ∙C h ≅ bind f ∙C (bind g ∙C h)
                                                                                                                                                   bind (bind f ∙C g) ∙C h 
                                                                                                                                                   ≅⟨ cong₂ _∙C_ mlaw3 refl ⟩
                                                                                                                                                   (bind f ∙C bind g) ∙C h
                                                                                                                                                   ≅⟨ assC ⟩
                                                                                                                                                   bind f ∙C bind g ∙C h ∎
                                                                                 }
