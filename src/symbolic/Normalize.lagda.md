
```

{-# OPTIONS --allow-unsolved-metas #-}
module symbolic.Normalize where

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

To compute differential of a ℝ expression, we need first normalize it to ℝ-normalized form.
```
data ℝ-normalized : {s : Shape} → Exp s ℝ → Set where
  Literal : {shape : Shape} → {x : Float} → ℝ-normalized {s = shape} (‵ x)
  Var : {shape : Shape} → {v : V shape} → ℝ-normalized {s = shape} (Var v)
  Sum : {shape : Shape} → (xs : List⁺ (Σ e ∶ Exp shape ℝ • ℝ-normalized e)) → ℝ-normalized (Sum $ List⁺.map proj₁ xs)
  Product : {shape : Shape} → (xs : List⁺ (Σ e ∶ Exp shape ℝ • ℝ-normalized e)) → ℝ-normalized (Product $ List⁺.map proj₁ xs)
  Dot : {shape : Shape} → (e1 e2 : Exp shape ℝ) → ℝ-normalized e1 → ℝ-normalized e2 → ℝ-normalized (e1 ∙ e2)


```
And ℝ-normalized is coupled with ℂ-normalized.
```
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

normalizeList⁺ : {shape : Shape} → {nt : Number}
              → List⁺ (Exp shape (Num nt))
              → List⁺ (Exp shape (Num nt))
normalizeList⁺ (x ∷ xs) = normalize x ∷ normalizeList xs

normalize (‵ x) = ‵ x
normalize (Var x) = Var x
normalize {nt = Real} (Sum xs) = Sum $ normalizeList⁺ xs
normalize {nt = Complex} (Sum xs) = {! !}
normalize (Product x) = {!!}
normalize (e + e₁ i) = {!!}
normalize (Re e) = {!!}
normalize (Im e) = {!!}
normalize (e ∙ e₁) = {!!}

sat-normalize-ℝ : {shape : Shape} → (e : Exp shape ℝ) → ℝ-normalized  (normalize e)
sat-normalize-ℝ = {!!}

sat-normalize-ℂ : {shape : Shape} → (e : Exp shape ℂ) → ℂ-normalized (normalize e)
sat-normalize-ℂ = {!!}



-- normalizeList : {shape : Shape} → {nt : Number}
--               → List (Exp shape (Num nt))
--               → List (Exp shape (Num nt))
-- normalizeList [] = []
-- normalizeList (x ∷ xs) = normalize x ∷ normalizeList xs


-- normalizeℂ : {shape : Shape} → Exp shape ℂ → Exp shape ℂ
-- normalizeℂ (Sum x) = {!!}
-- normalizeℂ (Product x) = {!!}
-- normalizeℂ (e + e₁ i) = {!!}
-- normalizeℂ (e ∙ e₁) = {!!}

-- normalize {nt = .Real} (‵ x) = {!!}
-- normalize {nt = .Real} (Var x) = {!!}
-- normalize {nt = nt} (Sum x) = {!!}
-- normalize {nt = nt} (Product x) = {!!}
-- normalize {nt = .Complex} (re + im i) = {!!}
-- normalize {nt = .Real} (Re c) = {!!}
-- normalize {nt = .Real} (Im c) = {!!}
-- normalize {nt = nt} (x ∙ y) = {!!}

-- sat-normalize-ℝ = {!!}

-- sat-normalize-ℂ = {!!}


```
