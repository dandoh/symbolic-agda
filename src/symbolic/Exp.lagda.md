

```
module symbolic.Exp where

open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Nat as Nat using ()
open import Data.Integer as Int using ()
open import Data.Float

open import Data.String as String using (String)
open import Data.Product as Product using ( _×_ ; _,_ ; Σ ; proj₁ ; proj₂ )
open import Level using (Level; lift)
  renaming ( _⊔_ to _⊍_ ; suc to ℓsuc; zero to ℓ₀ )
open import Function as Function using (_$_)
open import Relation.Nullary using (¬_; Dec; yes; no)

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

Inner product for ℂ is the same but the second operand is conjugated.

** Complex & real operations
Taking real part or imaginary part, and forming complex number from 2 real parts are defined as pointwise operations similarly as `+` and `*`.

** Scaling
Scaling behaves like scaling we know in vector space, i.e:
- { field = ℝ, vectors = ℝᵈ } forms a vector space
- { field = ℝ, vectors = ℂᵈ } forms a vector space
- { field = ℂ, vectors = ℂᵈ } forms a vector space

** Subtraction
// TODO: a - b = a + (-1) `scale` b
// TODO: More on this later as we add scaling.

* Partial derivative and 𝟙-form.
** 1-form
We know in first-year math about implicit differentiation e.g, taking derivative y' = dy/dx on the circle
   r² = x² + y² (r, x, y : ℝ)
 ⇒ 0 = 2x(dx) + 2y(dy)
 ⇒ dy/dx = - x / y

But what are dx, dy? What is their "type"?

In the language of differential geometry, their type is `𝟙-form`.
`d` is an operator that turn a scalar field to 𝟙-form (or covector) field, i.e
          f : ℝ² ⟶ ℝ
      then
         df : ℝ² ⟶ 𝟙-form
 df(xₒ, yₒ) eats a vector in the tangent space at (xₒ, yₒ) and gives us back a real number, or
 in the language of dependent type:
   df : (xₒ yₒ : ℝ) → TM(xₒ, yₒ) → ℝ

But we don't need to know about diffrential geometry. We only need to know that 𝟙-form and ℝ form a vector space,
and as we expect:
         df = (∂f/∂x) dx + (∂f/∂y) dy
  ...and that it gives us a nice way to formalize the type of expressions in the process of computing
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

     = (2x₁₁ + y₁₁) dx₁₁ + (2x₁₂ + y₁₂) dx₁₂ 
     + (2x₂₁ + y₂₁) dx₁₁ + (2x₂₂ + y₂₂) dx₂₂

  We can see that ∂f/∂xᵢⱼ   = 2xᵢⱼ  + yᵢⱼ    ∀ i, j

In our symbolic system, we "lift" the `d` operator as well as partial derivatives to multi-dimensional as:
  dx = | dx₁₁    dx₁₂ |
       | dx₂₁    dx₂₂ |

and
  ∂f / ∂x = | ∂f/∂x₁₁    ∂f/∂x₁₂|
            | ∂f/∂x₂₁    ∂f/∂x₂₂|

In fact, multi-dimensional calculation shows us that:

  df = x d(x + y) + (x + y) dx + y d(x + y) + (x + y) dy
     = (2x + y) dx + (2y + x) dy

  Thus ∂f/∂x = 2x + y, agrees with the above calculation.

Note that f still has to be a scalar real expression !!! 




* Formalize expression in the dependent type

Shape is a list of natural numbers, and an empty list represents dimension-less (scalar) shape.
```
Shape : Set
Shape = List Nat.ℕ

Scalar : Shape
Scalar = []
```

There are 3 element types: complex number, real number, and 1-form (or covector, or differential).
```
data Number : Set where
  Real : Number
  Complex : Number


data ElementType : Set where
  Num : Number → ElementType
  𝟙-form : ElementType

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
data Exp : Shape → ElementType → Set where
  -- From literal Float value
  ‵_ : {shape : Shape} → Float → Exp shape ℝ
  -- From variable identifier.
  Var : {shape : Shape} → V shape → Exp shape ℝ

  -- Pointwise sum of expressions
  -- Arguments is non-empty list of expressions because addition is associative
  -- We can only sum same shape and same element type
  -- ℝ, ℂ, or 𝟙-form are all addable.
  Sum : {shape : Shape} → {et : ElementType} → List⁺ (Exp shape et) → Exp shape et

  -- Pointwise product of expressions
  -- Arguments is non-empty list of expressions because multiplication is associative
  -- We can only take product same shape and same element type
  -- For number type only
  Product : {shape : Shape} → {nt : Number} → List⁺ (Exp shape (Num nt)) → Exp shape (Num nt)
  -- Inner product, multiply pointwise then sum all elements
  _∙_ : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt) → Exp Scalar (Num nt)

  -- -- Forming a complex expression from real part and imaginary part
  -- _+_i : {shape : Shape} → Exp shape ℝ → Exp shape ℝ → Exp shape ℂ
  -- -- Taking real part
  -- Re : {shape : Shape} → Exp shape ℂ → Exp shape ℝ
  -- -- Taking imaginary part
  -- Im : {shape : Shape} → Exp shape ℂ → Exp shape ℝ
```

Constructors 𝟙-form, for computing differentials.

```
  -- Represent differential of a varialbe
  DVar : {shape : Shape} → V shape → Exp shape 𝟙-form
  -- The zero value of 𝟙-form.
  -- Differential of non-variable is zero, e.g: d(‵ 1) = DZero
  DZero : {shape : Shape} → Exp shape 𝟙-form
  -- Pointwise multiplication real with diffrential pointwise 
  -- e.g d(2 * x) = 2 *∂ (dx)
  _*∂_ : {shape : Shape} → Exp shape  ℝ → Exp shape 𝟙-form → Exp shape 𝟙-form
  -- Multiply real with diffrential pointwise then sum all elements
  -- For computing differential of dot product
  _∙∂_ : {shape : Shape} → Exp shape ℝ → Exp shape 𝟙-form → Exp Scalar 𝟙-form

  -- TODO: Add more constructors: scale, power, division, trigonometry, log, exp, fourier-transform
```

```
_+_ : {shape : Shape} → {et : ElementType} → Exp shape et → Exp shape et → Exp shape et
a + b = Sum (a ∷ b ∷ [])

_*_ : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt) → Exp shape (Num nt)
a * b = Product (a ∷ b ∷ [])

```

```
infixl 6 _+_ 
infixl 7 _*_ _*∂_
infix 8 _∙_ _∙∂_
-- _+_i 

```


```


var : String → Exp [] ℝ
var x = Var (VV x [])

var1D : String → (n : Nat.ℕ) → Exp (n ∷ []) ℝ
var1D x m = Var (VV x (m ∷ []))

var2D : String → (m n : Nat.ℕ) → Exp (m ∷ n ∷ []) ℝ
var2D x m n = Var (VV x (m ∷ n ∷ []))

```



* Computing partial derivatives.

If everything is scalar, computing partial derivatives is trivial as we
just need a recursive function, and apply sum rule, product rule and the
chain rule.

Multi-dimensional derivatives, however, is not as so.
We can try:
```
partialDerivative' : {shape : Shape} → (f : Exp Scalar ℝ) → V shape → Exp shape ℝ
```
If f is constant, then partial derivative is 0[shape]
```
partialDerivative' (‵ c) x = ‵ 0.0
```

If f is a scalar variable, then partial derivative is 1[shape] if shape is scalar and
x == y, otherwise 0[shape].
```
partialDerivative' (Var (VV y .[])) (VV x []) with x String.≈? y
... | yes _ =  ‵ 1.0
... | no _ =   ‵ 0.0
partialDerivative' (Var (VV y .[])) (VV x (n:ns)) =  ‵ 0.0
```

Sum and product we can apply sum rule and product rule of derivative.
```
partialDerivative' (Sum ys) x = Sum {! List⁺.map (λ y → partialDerivative y x) ys !}
partialDerivative' (Product ys) x = {! TODO: doable!}

```
But here is where it got tricky!
y and z can be of higher dimensions, and we only have partialDerivative where the first
argument is scalar 
```
partialDerivative' (y ∙ z) x = {!!}
```
So we need other approach.


** Plan

The first step is to take differential (multi-dimensional of course), with the following rules:
  d(x + y) = dx + dy
  d(xy) = ydx + xdy
  d(x ∙ y) = x ∙ dy + y ∙ dx
  d(c) = 0  ∀constant c (here 0 is the zero value of 𝟙-form, not ℝ)

  ...more rules as we add more operators later, such as d(FT(x)) = FT(d(x)) 


```
d : {shape : Shape} → Exp shape ℝ → Exp shape 𝟙-form
dList : {shape : Shape} → List (Exp shape ℝ) → List (Exp shape 𝟙-form)
dList [] = []
dList (x ∷ xs) = d x ∷ dList xs

dList⁺ : {shape : Shape} → List⁺ (Exp shape ℝ) → List⁺ (Exp shape 𝟙-form)
dList⁺ (x ∷ xs) = d x ∷ dList xs


d (‵ x) = DZero
d (Var x) = DVar x
d (Sum xs) = Sum (dList⁺ xs)
d (Product xs) = {!!}
d (x ∙ y) =  Sum ((x ∙∂ d y) ∷ (y ∙∂ d x) ∷ [])
```


After take differential, we can transform the expression so that it always end up with the form

  // TODO: Data type of this form
  Either:
    - DZero (1)
    - (Exp Scalar ℝ) * (DVar x) (2)
    - (Exp shape ℝ) ∙ (Exp shape ℝ) (3)
    - Sum of operands that either in the form of (2) and (3)

Then we can extract all partial derivatives.
