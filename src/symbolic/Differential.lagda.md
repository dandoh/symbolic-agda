
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

```

```
data ℝ-normalized : {s : Shape} → Exp s ℝ → Set where
  Literal : {shape : Shape} → {x : Float} → ℝ-normalized {s = shape} (‵ x)
  Var : {shape : Shape} → {v : V shape} → ℝ-normalized {s = shape} (Var v)
  Sum : {shape : Shape} → (xs : List⁺ (Σ e ∶ Exp shape ℝ • ℝ-normalized e)) → ℝ-normalized (Sum $ List⁺.map proj₁ xs)
  Product : {shape : Shape} → (xs : List⁺ (Σ e ∶ Exp shape ℝ • ℝ-normalized e)) → ℝ-normalized (Product $ List⁺.map proj₁ xs)
  Dot : {shape : Shape} → (e1 e2 : Exp shape ℝ) → ℝ-normalized e1 → ℝ-normalized e2 → ℝ-normalized (e1 ∙ e2)

data ℂ-normalized {shape : Shape} : Exp shape ℂ → Set where
  ReIm : {e1 e2 : Exp shape ℝ}
       → {ℝ-normalized e1} → {ℝ-normalized e2}
       → ℂ-normalized (e1 + e2 i)
```

```

normalize : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt)
normalizeList : {shape : Shape} → {nt : Number}
              → List (Exp shape (Num nt))
              → List (Exp shape (Num nt))
normalizeList [] = []
normalizeList (x ∷ xs) = normalize x ∷ normalizeList xs


-- normalize-ℂ : {shape : Shape} → Exp shape ℂ → Exp shape ℝ × Exp shape ℝ

-- normalize-ℂ (Sum (e ∷ [])) = normalize-ℂ e
-- normalize-ℂ (Sum (e₁ ∷ e₂ ∷ es)) =  normalize-ℂ (Sum (e₂ ∷ es))
  -- let normalizedEs = List⁺.map normalize-ℂ es
  --     re = Sum $ List⁺.map proj₁ normalizedEs
  --     im =  Sum $ List⁺.map proj₂ normalizedEs
  --  in (re , im)
-- normalize-ℂ (Product x) = {!!}
-- normalize-ℂ (re + im i) =  normalize re , (normalize im) 
-- normalize-ℂ (Dot exp exp₁) = {!!}


normalize = {!!}


sat-normalize-ℝ : {shape : Shape} → (e : Exp shape ℝ) → ℝ-normalized (normalize e)
sat-normalize-ℝ = {!!}


```


```
δ_/δ_ : {shape : Shape} → Exp Scalar ℝ → V shape → Exp shape ℝ
δ f /δ x = {!!}
  
  
```
