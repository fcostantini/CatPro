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
           monad (OMap (R ○ L))
            (left (idenD))
            (λ f → HMap R (right f))
            (proof
              HMap R (right (left (idenD)))
              ≅⟨ cong (HMap R) (lawa (idenD)) ⟩
              HMap R (idenD)
              ≅⟨ fid R ⟩
              idenC ∎)
              (λ {x} {y} {f} → proof
                                 (HMap R (right f)) ∙C (left (idenD))
                                 ≅⟨ sym idrC ⟩
                                 (HMap R (right f) ∙C left (idenD)) ∙C idenC
                                 ≅⟨ assC ⟩
                                 HMap R (right f) ∙C left idenD ∙C idenC
                                 ≅⟨ natleft idenC (right f) idenD ⟩
                                 left (right f ∙D idenD ∙D HMap L idenC)
                                 ≅⟨ cong left (cong₂ _∙D_ refl (cong₂ _∙D_ refl (fid L))) ⟩
                                 left (right f ∙D idenD ∙D idenD)
                                 ≅⟨ cong left (cong₂ _∙D_ refl idrD) ⟩
                                 left (right f ∙D idenD)
                                 ≅⟨ cong left idrD ⟩ 
                                 left (right f)
                                 ≅⟨ lawb f ⟩
                                 f ∎)
              (λ {x} {y} {z} {f} {g} → proof
                                          HMap R (right (HMap R (right g) ∙C f))
                                          ≅⟨ cong (HMap R) (cong right (sym idrC)) ⟩
                                          HMap R (right ((HMap R (right g) ∙C f) ∙C idenC))
                                          ≅⟨  cong (HMap R) (cong right assC) ⟩
                                          HMap R (right (HMap R (right g) ∙C f ∙C idenC))
                                          ≅⟨ cong (HMap R) (natright idenC (right g) f) ⟩
                                          HMap R (right g ∙D right f ∙D HMap L idenC)
                                          ≅⟨ cong (HMap R) (cong₂ _∙D_ refl (cong₂ _∙D_ refl (fid L)) )⟩
                                          HMap R (right g ∙D right f ∙D idenD)
                                          ≅⟨ cong (HMap R) (cong₂ _∙D_ refl idrD ) ⟩
                                          HMap R (right g ∙D right f)
                                          ≅⟨ fcomp R ⟩
                                          HMap R (right g) ∙C HMap R (right f) ∎)

  