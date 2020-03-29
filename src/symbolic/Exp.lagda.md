
```
module symbolic.Exp where

open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as NonEmpty using (List⁺; _∷_)
open import Data.Nat using (ℕ)
open import Data.Float
open import Data.String

```

```
Shape : Set
Shape = List ℕ

Scalar : Shape
Scalar = []

data Number : Set where
  ℝ : Number
  ℂ : Number

data Element : Set where
  Num : Number → Element
  𝟙-form : Element
```  

```
infix 5 δ_/δ_
infixl 6 _+_ 
infixl 7 _*_ _*δ_
infix 8 _∙_ _+_i
infix 9 _[_]

data V : Shape → Set where
  _[_] : String → (shape : Shape) → V shape

data Exp : Shape → Element → Set where
  ‵_ : {shape : Shape} → Float → Exp shape (Num ℝ)
  Var : {shape : Shape} → V shape → Exp shape (Num ℝ)
  DVar : {shape : Shape} → V shape → Exp shape 𝟙-form

  Sum : {shape : Shape} → {et : Element} → List⁺ (Exp shape et) → Exp shape et
  Product : {shape : Shape} → {nt : Number} → List⁺ (Exp shape (Num nt)) → Exp shape (Num nt)


  _+_i : {shape : Shape} → Exp shape (Num ℝ) → Exp shape (Num ℝ) → Exp shape (Num ℂ)
  Re : {shape : Shape} → Exp shape (Num ℂ) → Exp shape (Num ℝ)
  Im : {shape : Shape} → Exp shape (Num ℂ) → Exp shape (Num ℝ)

  _∙_ : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt) → Exp Scalar (Num nt)

  _∙δ_ : {shape : Shape} → Exp shape (Num ℝ) → Exp shape 𝟙-form → Exp Scalar 𝟙-form
  _*δ_ : {shape : Shape} → Exp shape (Num ℝ) → Exp shape 𝟙-form → Exp shape 𝟙-form
```

```
_+_ : {shape : Shape} → {et : Element} → Exp shape et → Exp shape et → Exp shape et
a + b = Sum (a ∷ b ∷ [])

_*_ : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt) → Exp shape (Num nt)
a * b = Product (a ∷ b ∷ [])

```

```
normalize : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt)
normalize = {!!}

```


```
δ_/δ_ : {shape : Shape} → Exp Scalar (Num ℝ) → V shape → Exp shape (Num ℝ)
δ f /δ x = {!!}
  
  
```
