
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

Our symbolic calculator operates on tensors (i.e multi-dimensional variables, i.e grid of numbers).
The "type" of expression is determined by its shape (e.g 2X3, 3X4X5) and the kind of value (ℝ, ℂ or 𝟙-form)
it contains.

For example, ‶x : Exp (2X3) ℝ″ represents 2x3 matrix:

  x₁₁   x₁₂   x₁₃
  x₂₁   x₂₂   x₂₃
 
  where xᵢⱼ : ℝ

And differential of x, ‶d(x) : Exp (2X3) 𝟙-form″ represents 2x3 matrix:

  d(x₁₁)   d(x₁₂)   d(x₁₃)
  d(x₂₁)   d(x₂₂)   d(x₂₃)
 


Shape is a list of natural numbers each indicate size of corresponding dimension.
An empty list is the shape of scalar values.
```
Shape : Set
Shape = List Nat.ℕ

Scalar : Shape
Scalar = []
```

There are 3 kinds of elements: complex number, real number, and 1-form (differential).
```
data Number : Set where
  Real : Number
  Complex : Number


data Element : Set where
  Num : Number → Element
  𝟙-form : Element

ℝ = Num Real
ℂ = Num Complex

```  

V is our datatype for variable identifier. Each variable is uniquely identified by a name and a shape.
```
data V : Shape → Set where
  VV : String → (shape : Shape) → V shape

```

Now, expression constructors
```
data Exp : Shape → Element → Set where
  -- From literal Float value
  ‵_ : {shape : Shape} → Float → Exp shape ℝ
  -- From variable identifier.
  Var : {shape : Shape} → V shape → Exp shape ℝ

  -- Pointwise sum of expressions
  -- Arguments is non-empty list of expressions because addition is associative
  -- We can only sum same shape and same element type
  -- ℝ, ℂ, or 𝟙-form are all addable.
  Sum : {shape : Shape} → {et : Element} → List⁺ (Exp shape et) → Exp shape et

  -- Pointwise product of expressions
  -- Arguments is non-empty list of expressions because multiplication is associative
  -- We can only take product same shape and same element type
  -- For number type only
  Product : {shape : Shape} → {nt : Number} → List⁺ (Exp shape (Num nt)) → Exp shape (Num nt)

  -- Forming a complex expression from real part and imaginary part
  _+_i : {shape : Shape} → Exp shape ℝ → Exp shape ℝ → Exp shape ℂ
  -- Taking real part
  Re : {shape : Shape} → Exp shape ℂ → Exp shape ℝ
  -- Taking imaginary part
  Im : {shape : Shape} → Exp shape ℂ → Exp shape ℝ
  -- Dot product, multiply pointwise then sum all elements
  _∙_ : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt) → Exp Scalar (Num nt)
```

Constructors 𝟙-form, for computing differentials.

```
  -- Represent differential of a varialbe
  DVar : {shape : Shape} → V shape → Exp shape 𝟙-form
  -- Differential of non-variable is zero, e.g: d(‵ 1) = DZero
  DZero : {shape : Shape} → Exp shape 𝟙-form
  -- Differential dot product, multiply real with diffrential pointwise then sum all elements
  _∙δ_ : {shape : Shape} → Exp shape ℝ → Exp shape 𝟙-form → Exp Scalar 𝟙-form
  -- Pointwise multiplication real with diffrential pointwise then sum all elements
  _*δ_ : {shape : Shape} → Exp shape  ℝ → Exp shape 𝟙-form → Exp shape 𝟙-form

  -- TODO: Add more constructors: scale, power, division, trigonometry, log, exp, fourier-transform
```

```
_+_ : {shape : Shape} → {et : Element} → Exp shape et → Exp shape et → Exp shape et
a + b = Sum (a ∷ b ∷ [])

_*_ : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt) → Exp shape (Num nt)
a * b = Product (a ∷ b ∷ [])

```

```
infixl 6 _+_ 
infixl 7 _*_ _*δ_
infix 8 _∙_ _+_i

```


```


scalar : String → Exp [] ℝ
scalar x = Var (VV x [])

_[_] : String → (n : Nat.ℕ) → Exp (n ∷ []) ℝ
x [ m ] = Var (VV x (m ∷ []))

_[_X_] : String → (m n : Nat.ℕ) → Exp (m ∷ n ∷ []) ℝ
x [ m X n ] = Var (VV x (m ∷ n ∷ []))


```

Examples of expressions

