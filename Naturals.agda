module Naturals where

open import Library
open import Categories
open import Functors

open Fun

record NatT {a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}(F G : Fun C D) : Set (a ⊔ b ⊔ c ⊔ d) where
  constructor natural
  open Cat
  field cmp : ∀ {X} → Hom D (OMap F X) (OMap G X)
        nat : ∀{X Y}{f : Hom C X Y} → 
              _∙_ D (HMap G f) cmp ≅ _∙_ D cmp (HMap F f)
              
NatTEq : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G : Fun C D}
        → {α β : NatT F G}
        → (∀{X} → NatT.cmp α {X} ≅  NatT.cmp β {X})
        → α ≅ β
NatTEq p with iext (λ X → p {X})
NatTEq {α = natural cmp _} {natural .cmp _} p | refl = 
        cong (natural cmp) (iext λ _ → iext λ _ → iext λ _ → ir _ _)


idNat : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F : Fun C D} → NatT F F
idNat {D = D}{F} = let open Cat D in record {
  cmp = iden;
  nat = λ{X}{Y}{f} → 
    proof
    HMap F f ∙ iden
    ≅⟨ idr ⟩ 
    HMap F f
    ≅⟨ sym idl ⟩ 
    iden ∙ (HMap F f)
    ∎} 

-- Composición vertical
compVNat : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G H : Fun C D} → 
          NatT G H → NatT F G → NatT F H
compVNat {D = D}{F}{G}{H} α β = let open Cat D; open NatT in record {
  cmp = cmp α ∙ cmp β;
  nat = λ{X}{Y}{f} → 
    proof
    HMap H f ∙ (cmp α ∙ cmp β) 
    ≅⟨ sym ass ⟩
    (HMap H f ∙ cmp α) ∙ cmp β
    ≅⟨ cong₂ _∙_ (nat α) refl ⟩
    (cmp α ∙ HMap G f) ∙ cmp β
    ≅⟨ ass ⟩
    cmp α ∙ (HMap G f ∙ cmp β)
    ≅⟨ cong₂ _∙_ refl (nat β) ⟩
    cmp α ∙ (cmp β ∙ HMap F f)
    ≅⟨ sym ass ⟩
    (cmp α ∙ cmp β) ∙ HMap F f 
    ∎}

-- Natural isomorphism

open import Categories.Iso

record NatIso {a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}
             {F G : Fun C D}(η : NatT F G)  : Set (a ⊔ d) where
  constructor natiso
  field cmpIso : ∀{X} -> Iso D (NatT.cmp η {X})


-- composición con funtor (a izquierda y a derecha)

compFNat : ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
            {F G : Fun C D}
         → (J : Fun D E)
         → (η : NatT F G) → NatT (J ○ F) (J ○ G)
compFNat {D = D} {E} {F} {G} J η =
               let open NatT η
                   open Cat D renaming (_∙_ to _∙D_)
                   open Cat E renaming (_∙_ to _∙E_)
               in
               natural (HMap J cmp)
                       (λ {X} {Y} {f} →  proof
                       HMap (J ○ G) f ∙E (HMap J cmp)
                       ≅⟨ sym (fcomp J) ⟩
                       HMap J (HMap G f ∙D cmp)
                       ≅⟨ cong (HMap J) nat ⟩
                       HMap J (cmp ∙D HMap F f)
                       ≅⟨ fcomp J ⟩
                       HMap J cmp ∙E (HMap J (HMap F f)) 
                       ≅⟨ refl ⟩
                       HMap J cmp ∙E (HMap (J ○ F) f)
                       ∎ )

compNatF :  ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
            {J K : Fun D E}
         → (η : NatT J K)
         → (F : Fun C D)
         → NatT (J ○ F) (K ○ F)
compNatF {C = C} {D} {E} {J} {K} η F =
               let open NatT η
                   open Cat D renaming (_∙_ to _∙D_)
                   open Cat E renaming (_∙_ to _∙E_)
               in natural (λ {X} → cmp {OMap F X}) nat

--------------------------------------------------
-- Composición horizontal
compHNat : ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
            {F G : Fun C D}{J K : Fun D E}
            (η : NatT F G)(ε : NatT J K)
            → NatT (J ○ F) (K ○ G)
compHNat {G = G} {J} η ε = compVNat (compNatF ε G) (compFNat J η)


-- La composición horizontal es asociativa

-- ley de intercambio
interchange : ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
               {F G H : Fun C D}{I J K : Fun D E}
              → (α : NatT F G) → (β : NatT G H)
              → (γ : NatT I J) → (δ : NatT J K)
              → compHNat (compVNat β α) (compVNat δ γ) ≅ compVNat (compHNat β δ) (compHNat α γ)
interchange {D = D}{E}{I = I}{J} (natural α _) (natural β _) (natural γ natγ) (natural δ _) =
          let open NatT
              _∙D_ = Cat._∙_ D
              open Cat E
           in NatTEq (
            proof
            (δ ∙ γ) ∙ HMap I (β ∙D α)
            ≅⟨ cong (_∙_ (δ ∙ γ)) (fcomp I) ⟩
            (δ ∙ γ) ∙ HMap I β ∙ HMap I α
            ≅⟨ ass ⟩
            δ ∙ γ ∙ HMap I β ∙ HMap I α
            ≅⟨ cong (_∙_ δ) (sym ass) ⟩
            δ ∙ (γ ∙ HMap I β) ∙ HMap I α
            ≅⟨ cong (λ x → δ ∙ x ∙ HMap I α) (sym natγ) ⟩
            δ ∙ (HMap J β ∙ γ) ∙ HMap I α
            ≅⟨ cong (_∙_ δ) ass ⟩
            δ ∙ HMap J β ∙ γ ∙ HMap I α
            ≅⟨ sym ass ⟩
            (δ ∙ HMap J β) ∙ γ ∙ (HMap I α)
            ∎)
