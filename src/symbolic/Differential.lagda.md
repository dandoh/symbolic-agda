
```
{-# OPTIONS --allow-unsolved-metas #-}

module symbolic.Differential where

open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Nat as Nat using ()
open import Data.Integer as Int using ()
open import Data.Float
open import Data.String
open import Data.Product as Product using ( _×_ ; _,_ ; Σ ; proj₁ ; proj₂ )
open import Level using (Level; lift)
  renaming ( _⊔_ to _⊍_ ; suc to ℓsuc; zero to ℓ₀ )
open import Function as Function using (_$_)


open import symbolic.Exp
open import symbolic.Normalize

```

```

-- differential : {shape : Shape} → Exp shape ℝ → Exp shape 𝟙-form

-- differentialList : {shape : Shape} → List (Exp shape ℝ) → List (Exp shape 𝟙-form)
-- differentialList [] = []
-- differentialList (x ∷ xs) = differential x ∷ differentialList xs

-- differentialList⁺ : {shape : Shape} → List⁺ (Exp shape ℝ) → List⁺ (Exp shape 𝟙-form)
-- differentialList⁺ (x ∷ xs) = differential x ∷ differentialList xs


-- differential {shape} e with (normalize e) | sat-normalize-ℝ e
-- ... | ‵ x | Literal = DZero
-- ... | Var x | Var = DVar x
-- ... | Sum xs | Sum _ =  Sum (differentialList⁺ xs)
-- ... | Product (x ∷ xs) | Product _ = {!!}
-- ... | x ∙ y | Dot _ _ _ _ = {!!}



```

Partial derivative
```

δ_/δ_ : {shape : Shape} → Exp Scalar ℝ → V shape → Exp shape ℝ
δ f /δ x = {!!}
  
  
```
