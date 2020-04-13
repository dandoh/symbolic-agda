
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
open import Level using (Level; lift) renaming ( _⊔_ to _⊍_ ; suc to ℓsuc; zero to ℓ₀ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; _≗_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning )
open import Function as Function using (_$_)

-- open import symbolic.Exp


```
As addition and multiplication are associative, the first step is to flatten any nested sum or products

Sum [a, Sum [b, Sum [c , d]], e, f] -> Sum [a , b , c , d , e , f]
```
-- sumOperands : {shape : Shape} → {et : ElementType} → Exp shape et → List⁺ (Exp shape et)
-- sumOperands (Sum x) = {!!}
-- sumOperands e = e ∷ []

-- flattenSum : {shape : Shape} → {et : ElementType} → Exp shape et → Exp shape et

-- flattenSumList : {shape : Shape} → {et : ElementType} → List (Exp shape et) → List (Exp shape et)
-- flattenSumList [] = []
-- flattenSumList (x ∷ xs) =  flattenSum x ∷ flattenSumList xs

-- flattenSumList⁺ : {shape : Shape} → {et : ElementType} → List⁺ (Exp shape et) → List⁺ (Exp shape et)
-- flattenSumList⁺ (x ∷ xs) =  flattenSum x ∷ flattenSumList xs

-- flattenSum (Sum xs) = Sum (List⁺.concatMap sumOperands (flattenSumList⁺ xs))
-- flattenSum (Product (x ∷ xs)) = Product (flattenSum x ∷ flattenSumList xs)
-- flattenSum (a + b i) = flattenSum a + flattenSum b i
-- flattenSum (Re e) =  Re (flattenSum e)
-- flattenSum (Im e) = Im (flattenSum e)
-- flattenSum (a ∙ b) =  flattenSum a ∙ flattenSum b
-- flattenSum (a ∙∂ b) = flattenSum a ∙∂ flattenSum b
-- flattenSum (a *∂ b) =  flattenSum a *∂ flattenSum b
-- flattenSum e = e
```


```
-- _ : flattenSum (Sum (E.x ∷ E.y ∷ Sum (E.x ∷ E.z ∷ [] ) ∷ [] )) ≡ Sum (E.x ∷ E.y ∷ E.x ∷ E.z ∷ [])
-- _ = refl

-- _ : flattenSum (Sum (E.x ∷ E.y ∷ Sum (E.x ∷ Sum (E.x ∷ E.y ∷ [])∷ E.z ∷ [] ) ∷ [] )) ≡ Sum (E.x ∷ E.y ∷ E.x ∷ E.x ∷ E.y ∷ E.z ∷ [])
-- _ = refl
```


Now we try to prove there is no nested-sum after flattening

Define a data type NoSum that list every non-sum-constructor ?
```
```



To compute differential of a ℝ expression, we need first normalize it to ℝ-normalized form.
```
-- data ℝ-normalized : {s : Shape} → Exp s ℝ → Set where
--   Literal : {shape : Shape} → {x : Float} → ℝ-normalized {s = shape} (‵ x)
--   Var : {shape : Shape} → {v : V shape} → ℝ-normalized {s = shape} (Var v)
--   Sum : {shape : Shape} → (xs : List⁺ (Σ e ∶ Exp shape ℝ • ℝ-normalized e)) → ℝ-normalized (Sum $ List⁺.map proj₁ xs)
--   Product : {shape : Shape} → (xs : List⁺ (Σ e ∶ Exp shape ℝ • ℝ-normalized e)) → ℝ-normalized (Product $ List⁺.map proj₁ xs)
--   Dot : {shape : Shape} → (e1 e2 : Exp shape ℝ) → ℝ-normalized e1 → ℝ-normalized e2 → ℝ-normalized (e1 ∙ e2)


```
And ℝ-normalized is coupled with ℂ-normalized.
```
-- data ℂ-normalized {shape : Shape} : Exp shape ℂ → Set where
--   ReIm : {e1 e2 : Exp shape ℝ}
--        → {ℝ-normalized e1} → {ℝ-normalized e2}
--        → ℂ-normalized (e1 + e2 i)
```
