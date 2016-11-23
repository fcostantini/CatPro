module AdjMon where

  open import Library
  open import Categories
  open import Adjunctions
  open import Functors
  open import Monads

  open Cat
  open Fun
 
  AdjToMon : ∀{a b c d}{ C : Cat {a} {b}}{ D : Cat {c}{d}} → Adj C D → Monad C
  AdjToMon {a}{b}{c}{d}{C}{D} (adjunction L R left right lawa lawb natleft natright) =
            let open Cat C renaming (iden to idenC; _∙_ to _∙C_; idr to idrC; idl to idlC; ass to assC)
                open Cat D renaming (iden to idenD; _∙_ to _∙D_; idr to idrD; idl to idlD; ass to assD)
            in 
           monad (OMap (R ○ L)) --mapeo en C
            (left (idenD)) --X en RLX, idenD es LX en LX
            (λ f → HMap R (right f)) --f de X en RLY, right f de LY en LY
            (proof --bind (return x) ≅ iden Tx o sea R (right (left idD)) ≅ idC
              HMap R (right (left (idenD))) 
              ≅⟨ cong (HMap R) (lawa (idenD)) ⟩ --right (left f) = f
              HMap R (idenD)
              ≅⟨ fid R ⟩
              idenC ∎)
              (λ {x} {y} {f} → proof --bind f ∙ return ≅ f o sea R (right f) ∙C (left idD)
                                 (HMap R (right f)) ∙C (left (idenD))
                                 ≅⟨ sym idrC ⟩ --introduzco idC para poder usar natleft
                                 (HMap R (right f) ∙C left (idenD)) ∙C idenC
                                 ≅⟨ assC ⟩
                                 HMap R (right f) ∙C left idenD ∙C idenC
                                 ≅⟨ natleft idenC (right f) idenD ⟩ --natleft
                                 left (right f ∙D idenD ∙D HMap L idenC)
                                 ≅⟨ cong left (cong₂ _∙D_ refl (cong₂ _∙D_ refl (fid L))) ⟩
                                 left (right f ∙D idenD ∙D idenD) 
                                 ≅⟨ cong left (cong₂ _∙D_ refl idrD) ⟩
                                 left (right f ∙D idenD)
                                 ≅⟨ cong left idrD ⟩ 
                                 left (right f) --left (right f) = f
                                 ≅⟨ lawb f ⟩
                                 f ∎)
              (λ {x} {y} {z} {f} {g} → proof --bind (bind g  ∙ f) ≅ bind g ∙ bind f o sea R (right (R (right g) ∙ f)) ≅ R (right g) ∙ R (right f)
                                          HMap R (right (HMap R (right g) ∙C f))
                                          ≅⟨ cong (HMap R) (cong right (sym idrC)) ⟩ --introduzco idC para poder usar natright
                                          HMap R (right ((HMap R (right g) ∙C f) ∙C idenC))
                                          ≅⟨  cong (HMap R) (cong right assC) ⟩
                                          HMap R (right (HMap R (right g) ∙C f ∙C idenC))
                                          ≅⟨ cong (HMap R) (natright idenC (right g) f) ⟩ --natright
                                          HMap R (right g ∙D right f ∙D HMap L idenC)
                                          ≅⟨ cong (HMap R) (cong₂ _∙D_ refl (cong₂ _∙D_ refl (fid L)) )⟩
                                          HMap R (right g ∙D right f ∙D idenD)
                                          ≅⟨ cong (HMap R) (cong₂ _∙D_ refl idrD ) ⟩
                                          HMap R (right g ∙D right f)
                                          ≅⟨ fcomp R ⟩
                                          HMap R (right g) ∙C HMap R (right f) ∎)

--Functores para adjunción de Kleisli (ref. http://www.cs.nott.ac.uk/~psztxa/monads-more-1.pdf)

kL :  ∀{a b}{ C : Cat {a} {b}}{M : Monad C} → Fun C (kleisliC M)
kL {a}{b}{C}{M = monad T return bind mlaw1 mlaw2 mlaw3} = let open Cat C renaming (iden to idenC; _∙_ to _∙C_; idr to idrC; idl to idlC; ass to assC) in 
                                      functor id
                                                  (λ f → return ∙C f) --f de x en y, necesito x en Ty => return (f x)
                                                 idrC --kL idC ≅ idkC o sea return ∙ id ≅ return
                                                  (λ {x} {y} {z} {f} {g} → proof --kL (f ∙C g) ≅ kL f ∙kC kL g o sea return ∙C f ∙C g ≅ bind (return ∙C f) ∙C return ∙C g 
                                                                                           return ∙C f ∙C g
                                                                                           ≅⟨ sym assC ⟩
                                                                                            (return ∙C f) ∙C g 
                                                                                            ≅⟨ cong₂ _∙C_ (sym mlaw2) refl ⟩ --introduzco bind return
                                                                                            (bind (return ∙C f) ∙C return) ∙C g 
                                                                                            ≅⟨ assC ⟩
                                                                                            bind (return ∙C f) ∙C return ∙C g ∎)

kR :  ∀{a b}{ C : Cat {a} {b}}{M : Monad C} → Fun (kleisliC M) C
kR {a}{b}{C}{M = monad T return bind mlaw1 mlaw2 mlaw3} = let open Cat C renaming (iden to idenC; _∙_ to _∙C_; idr to idrC; idl to idlC; ass to assC) in
                                     functor T -- el mapeo de objetos es la función de la mónada 
                                                 bind --tengo x en ty, necesito tx en ty 
                                                 mlaw1 --bind id = idenC -> bind return = idenC
                                                 mlaw3 -- bind (f ∙kC g) = bind f ∙C bind g -> bind (bind f ∙ g) = bind f ∙C bind g

--Adjunción de Kleisli
MonToAdj : ∀{a b}{ C : Cat {a} {b}} → (M : Monad C) → Adj C (kleisliC M)
MonToAdj {a}{b}{C}(monad T return bind mlaw1 mlaw2 mlaw3) = let open Cat C renaming (iden to idenC; _∙_ to _∙C_; idr to idrC; idl to idlC; ass to assC) in 
                                    adjunction (kL {a} {b} {C} {monad T return bind mlaw1 mlaw2 mlaw3})
                                                     (kR  {a} {b} {C} {monad T return bind mlaw1 mlaw2 mlaw3}) 
                                                     id 
                                                     id 
                                                     (λ f → refl)
                                                     (λ f → refl) 
                                                     (λ f g h → proof 
                                                                     (bind g) ∙C (h ∙C f)
                                                                     ≅⟨ cong₂ _∙C_ refl (cong₂ _∙C_ (sym mlaw2) refl) ⟩ --introduzco bind return
                                                                     (bind g) ∙C ((bind h) ∙C return) ∙C f
                                                                     ≅⟨ cong₂ _∙C_ refl  assC ⟩
                                                                     (bind g) ∙C (bind h) ∙C (return ∙C f) ∎)
                                                     (λ f g h → proof 
                                                                     (bind g) ∙C (h ∙C f)
                                                                     ≅⟨ cong₂ _∙C_ refl (cong₂ _∙C_ (sym mlaw2) refl) ⟩ --introduzco bind return
                                                                     (bind g) ∙C ((bind h) ∙C return) ∙C f
                                                                     ≅⟨ cong₂ _∙C_ refl  assC ⟩
                                                                     (bind g) ∙C (bind h) ∙C (return ∙C f) ∎) 
{-                                                     
MonToMon : ∀{a b}{ C : Cat {a} {b}} → (M : Monad C) → AdjToMon (MonToAdj {a}{b}{C} M) ≅ M
MonToMon {a} {b}{C} (monad T return bind mlaw1 mlaw2 mlaw3) = let open Cat C renaming (iden to idenC; _∙_ to _∙C_; idr to idrC; idl to idlC; ass to assC) in 
                                                proof AdjToMon (MonToAdj (monad T return bind mlaw1 mlaw2 mlaw3))
                                                         ≅⟨ cong AdjToMon refl  ⟩
                                                         AdjToMon (adjunction (kL {a} {b} {C} {monad T return bind mlaw1 mlaw2 mlaw3})
                                                                                            (kR {a} {b} {C} {monad T return bind mlaw1 mlaw2 mlaw3})
                                                                                            id 
                                                                                            id
                                                                                            (λ f → refl)
                                                                                            (λ f → refl)
                                                                                           (λ f g h → proof
                                                                                                           (bind g) ∙C (h ∙C f)
                                                                                                           ≅⟨ cong₂ _∙C_ refl (cong₂ _∙C_ (sym mlaw2) refl) ⟩
                                                                                                           (bind g) ∙C ((bind h) ∙C return) ∙C f
                                                                                                           ≅⟨ cong₂ _∙C_ refl assC ⟩
                                                                                                           (bind g) ∙C (bind h) ∙C (return ∙C f) ∎)
                                                                                           (λ f g h → proof
                                                                                                          (bind g) ∙C (h ∙C f)
                                                                                                          ≅⟨ cong₂ _∙C_ refl (cong₂ _∙C_ (sym mlaw2) refl) ⟩
                                                                                                          (bind g) ∙C (((bind h) ∙C return) ∙C f)
                                                                                                          ≅⟨ cong₂ _∙C_ refl assC ⟩
                                                                                                          (bind g) ∙C ((bind h) ∙C (return ∙C f)) ∎))
                                                         ≅⟨ {!!} ⟩
                                                         monad T return bind mlaw1 mlaw2 mlaw3 ∎
-}
