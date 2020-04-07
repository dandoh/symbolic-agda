
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

* Introduction

Our symbolic calculator operates on tensors (i.e multi-dimensional variables, i.e grid of numbers).
We call them expressions.

The "type" of an expression is determined by its shape (e.g 2x3, 3x4x5) and the kind of value (ℝ, ℂ or 𝟙-form)
it contains.

Shape of expressions can be represented by a list of natural number. 2x3 is [2, 3], 3x4x5 is [3, 4, 5].
Well suited with this, the empty list [] represents sort of "dimension-less" shape,
or we call "scalar".

ℝ and ℂ are real and complex numbers respectively, whereas element type 𝟙-form (or covector) is our mean
for reasoning partial derivatives which we will discuss shortly.


As an example, `x : Exp (2x3) ℂ` represents 2x3 matrix
 | x₁₁     x₁₂     x₁₃ |
 | x₂₁     x₂₂     x₂₃ |
  where each xᵢⱼ is a complex number, xᵢⱼ : ℂ (xᵢⱼ = aᵢⱼ + bᵢⱼ i)


Its shape is 2x3 ([2 , 3]), and its element type is ℂ.

* Operations 

Given `x : Exp (2x3) ℝ`, and `y : Exp (2x3) ℝ`.

** Addition 
Same shape, same element type.
Our tensor addition is pointwise of normal addtion (which we know all of ℝ, ℂ, and 𝟙-form are all addable).
x + y represents:

 | x₁₁ + y₁₁    x₁₂ + y₁₂     x₁₃ + y₁₃ |
 | x₂₁ + y₂₁    x₂₂ + y₂₂     x₂₃ + y₂₃ |

** Multiplication:
Same shape, number type.
Similarly, multiplication is pointwise of normal multiplication, operatable on ℝ and ℂ only.
x * y represents:

 | x₁₁ * y₁₁    x₁₂ * y₁₂     x₁₃ * y₁₃ |
 | x₂₁ * y₂₁    x₂₂ * y₂₂     x₂₃ * y₂₃ |

** Inner product:
Inner product (dot product) for ℝ is pointwise multiplication, then sum all the elements. As a result, dot product gives back a single scalar number.
x ∙ y represents a single real number:
 (x₁₁ * y₁₁) + (x₁₂ * y₁₂) + (x₁₃ * y₁₃) + (x₂₁ * y₂₁) + (x₂₂ * y₂₂) + (x₂₃ * y₂₃)

Inner product for ℂ is the same except the second operand is conjugated.

** Complex & real operations
Taking real part or imaginary part, and forming complex number from 2 real parts is defined pointwise similarly as `+` and `*`.

** Scaling
Scaling behaves like scaling we know in vector space, i.e:
- { field = ℝ, vectors = ℝᵈ } forms a vector space
- { field = ℝ, vectors = ℂᵈ } forms a vector space
- { field = ℂ, vectors = ℂᵈ } forms a vector space

** Subtraction
// TODO: a - b = a + (-1) `scale` b




TODO: More on this later add we add scaling later.

* Partial derivative and 𝟙-form.
** 1-form
We know in first-year math about implicit differentiation e.g, taking derivative y' = dy/dx on the circle
  (r, x, y : ℝ)
   r² = x² + y²
 ⇒ 0 = 2x(dx) + 2y(dy)
 ⇒ dy/dx = - x / y

But what are dx, dy? What is their "type"

However, in the language of differential geometry, their type is `𝟙-form`.
`d` is an operator that turn a scalar field to 𝟙-form field, i.e
          f : ℝ² ⟶ ℝ
      then
         df : ℝ² ⟶ 𝟙-form

But we don't need to know about diffrential geometry. The only thing we care about 𝟙-form is that
𝟙-form and ℝ form a vector space, and that
         df = (∂f/∂x) dx + (∂f/∂y) dy
  and that it gives us a nice way to formalize the type of expressions in the process of computing
  partial derivatives.

** Multi-dimensional partial derivatives
Let x, y : Exp 2x2 ℝ

Let's try to compute partial derivatives of:
  f = (x + y) ∙ x 

  f = (x₁₁ + y₁₁) * x₁₁  + (x₁₂ + y₁₂) * x₁₂ 
    + (x₂₁ + y₂₃) * x₂₁  + (x₂₂ + y₂₂) * x₂₂

  df = x₁₁ d(x₁₁ + y₁₁)  + x₁₂ d(x₁₂ + y₁₂) 
     + x₂₁ d(x₂₁ + y₂₃)  + x₂₂ d(x₂₂ + y₂₂)
     + (x₁₁ + y₁₁) dx₁₁  + (x₁₂ + y₁₂) dx₁₂ 
     + (x₂₁ + y₂₃) dx₂₁  + (x₂₂ + y₂₂) dx₂₂

  ...

  Then we can see ∂f/∂x₁₁ = 2x₁₁ + y₁₁, and 
                  ∂f/∂xᵢⱼ   = 2xᵢⱼ  + yᵢⱼ    ∀ i, j

But this is a description only using scalar. In fact, we can "lift" the `d` operator as well as
partial derivatives pointwisely and it will work as normal:

  df = x d(x + y) + (x + y) dx + y d(x + y) + (x + y) dy
     = (2x + y) dx + (2y + x) dy

  Thus ∂f/∂x = 2x + y, and this agrees with the above calculation.


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
  -- Inner product, multiply pointwise then sum all elements
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


scalarVar : String → Exp [] ℝ
scalarVar x = Var (VV x [])

_[_] : String → (n : Nat.ℕ) → Exp (n ∷ []) ℝ
x [ m ] = Var (VV x (m ∷ []))

_[_X_] : String → (m n : Nat.ℕ) → Exp (m ∷ n ∷ []) ℝ
x [ m X n ] = Var (VV x (m ∷ n ∷ []))


```

Examples of expressions

