
```
module symbolic.Exp where

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

Σ-syntax : {ℓa ℓb : Level} (A : Set ℓa) (B : A → Set ℓb) → Set (ℓa ⊍ ℓb)
Σ-syntax = Σ

infix 2 Σ-syntax
syntax Σ-syntax A (λ a → B) = Σ a ∶ A • B

```

```
Shape : Set
Shape = List Nat.ℕ

Scalar : Shape
Scalar = []

data Number : Set where
  Real : Number
  Complex : Number

data Element : Set where
  Num : Number → Element
  𝟙-form : Element

ℝ = Num Real

ℂ = Num Complex

```  

```
infix 5 δ_/δ_
infixl 6 _+_ 
infixl 7 _*_ _*δ_
infix 8 _∙_ _+_i
-- infix 8 _**_
infix 9 _[_]

data V : Shape → Set where
  _[_] : String → (shape : Shape) → V shape

data Exp : Shape → Element → Set where
  ‵_ : {shape : Shape} → Float → Exp shape ℝ
  Var : {shape : Shape} → V shape → Exp shape ℝ
  DVar : {shape : Shape} → V shape → Exp shape 𝟙-form

  Sum : {shape : Shape} → {et : Element} → List⁺ (Exp shape et) → Exp shape et
  Product : {shape : Shape} → {nt : Number} → List⁺ (Exp shape (Num nt)) → Exp shape (Num nt)

  -- Power : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Float → Exp shape (Num nt)

  _+_i : {shape : Shape} → Exp shape ℝ → Exp shape ℝ → Exp shape ℂ
  Re : {shape : Shape} → Exp shape ℂ → Exp shape ℝ
  Im : {shape : Shape} → Exp shape ℂ → Exp shape ℝ

  Dot : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt) → Exp Scalar (Num nt)

  _∙δ_ : {shape : Shape} → Exp shape ℝ → Exp shape 𝟙-form → Exp Scalar 𝟙-form
  _*δ_ : {shape : Shape} → Exp shape  ℝ → Exp shape 𝟙-form → Exp shape 𝟙-form
  

data ℝ-normalized : {s : Shape} → Exp s ℝ → Set where
  Literal : {shape : Shape} → {x : Float} → ℝ-normalized {s = shape} (‵ x)
  Var : {shape : Shape} → {v : V shape} → ℝ-normalized {s = shape} (Var v)
  Sum : {shape : Shape} → (xs : List⁺ (Σ e ∶ Exp shape ℝ • ℝ-normalized e)) → ℝ-normalized (Sum $ List⁺.map proj₁ xs)
  Product : {shape : Shape} → (xs : List⁺ (Σ e ∶ Exp shape ℝ • ℝ-normalized e)) → ℝ-normalized (Product $ List⁺.map proj₁ xs)
  -- Power : {shape : Shape} {α : Float} → (e : Exp shape ℝ) → ℝ-normalized e → ℝ-normalized (Power e α)
  Dot : {shape : Shape} → (e1 e2 : Exp shape ℝ) → ℝ-normalized e1 → ℝ-normalized e2 → ℝ-normalized (Dot e1 e2)

data ℂ-normalized {shape : Shape} : Exp shape ℂ → Set where
  ReIm : {e1 e2 : Exp shape ℝ}
       → {ℝ-normalized e1} → {ℝ-normalized e2}
       → ℂ-normalized (e1 + e2 i)
```

```
_+_ : {shape : Shape} → {et : Element} → Exp shape et → Exp shape et → Exp shape et
a + b = Sum (a ∷ b ∷ [])

_*_ : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt) → Exp shape (Num nt)
a * b = Product (a ∷ b ∷ [])

-- _**_ : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Float → Exp shape (Num nt)
-- _**_ = Power

_∙_ : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt) → Exp Scalar (Num nt)
_∙_ = Dot

```

```


data E : Set where
  T : E
  Sum : List E → E

haha : E → Nat.ℕ
hahaList : List E → List Nat.ℕ

hahaList [] = []
hahaList (x ∷ xs) = haha x ∷ hahaList xs

haha T =  1
haha (Sum xs) = List.foldl Nat._+_ 0 $ hahaList xs
  



normalize : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt)
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
δ_/δ_ : {shape : Shape} → Exp Scalar (Num Real) → V shape → Exp shape (Num Real)
δ f /δ x = {!!}
  
  
```
