

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
open import Function as Function using (_$_ ; case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary using (Decidable)

open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; _≗_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning )

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

Var is our datatype for variable identifier. Each variable is uniquely identified by a name and a shape.
```

data VarId : Set where
  X : VarId
  Y : VarId
  Z : VarId


_≈_ : (x : VarId) → (y : VarId) → Dec (x ≡ y)
X ≈ X = yes refl
X ≈ Y = no (λ ())
X ≈ Z = no (λ ())
Y ≈ X = no (λ ())
Y ≈ Y = yes refl
Y ≈ Z = no (λ ())
Z ≈ X = no (λ ())
Z ≈ Y = no (λ ())
Z ≈ Z = yes refl


data Var : Shape → Set where
  V : {shape : Shape} → VarId → Var shape



data Prim : Shape → Set where
  PLit : {shape : Shape} → Float → Prim shape
  PVar : {shape : Shape} → Var shape → Prim shape
  




```

Now, expression constructors
```
data Exp : Shape → ElementType → Set where
  -- From primitive
  EPrim : {shape : Shape} → Prim shape → Exp shape ℝ

  -- Pointwise sum of expressions
  -- Arguments is non-empty list of expressions because addition is associative
  Sum : {shape : Shape} →  Exp shape ℝ → Exp shape ℝ  → Exp shape ℝ

  -- Pointwise product of expressions
  -- Arguments is non-empty list of expressions because multiplication is associative
  -- We can only take product same shape and same element type
  -- For number type only
  Product : {shape : Shape} → Exp shape ℝ → Exp shape ℝ → Exp shape ℝ

  -- Inner product, multiply pointwise then sum all elements
  Dot : {shape : Shape} → Exp shape ℝ → Exp shape ℝ → Exp Scalar ℝ

  -- Invariant: scalar must be primitive
  Scale : {shape : Shape} → Prim Scalar → Exp shape ℝ → Exp shape ℝ 

  -- TODO: Add more constructors: scale, power, division, trigonometry, log, exp, fourier-transform

```
Complex number 
```
  -- Forming a complex expression from real part and imaginary part
  _+_i : {shape : Shape} → Exp shape ℝ → Exp shape ℝ → Exp shape ℂ

```
Constructors 𝟙-form, for computing differentials.
```
  -- The zero value of 𝟙-form
  Sumd : {shape : Shape} → Exp shape 𝟙-form → Exp shape 𝟙-form → Exp shape 𝟙-form
  d0 : {shape : Shape} → Exp shape 𝟙-form
  -- Pointwise multiplication real with diffrential pointwise 
  -- e.g d(2 * x) = 2 *∂ (dx)
  _*d_ : {shape : Shape} → Exp shape ℝ → Var shape → Exp shape 𝟙-form
  -- Multiply real with diffrential pointwise then sum all elements
  -- For computing differential of dot product
  _∙d_ : {shape : Shape} → Exp shape ℝ → Var shape → Exp Scalar 𝟙-form
  -- Scaling: multiply the left operand to all differential on the grid
  -- of right operand
  -- For computing differential of scaling
  _*∙d_ : {shape : Shape} → Exp Scalar ℝ → Var shape → Exp shape 𝟙-form
  -- Differential scaling: the otherway around
  -- Multiply all the numbers on the grid of right operand to the
  -- differential on the left 
  -- For computing differential of scaling
  _∙*d_ : {shape : Shape} → Exp shape ℝ → Var Scalar → Exp shape 𝟙-form

```

```
data OExp : Shape → ElementType → Set where
  ELit : {shape : Shape} → Float → OExp shape ℝ
  EVar : {shape : Shape} → Var shape → OExp shape ℝ
  Sum : {shape : Shape} →  OExp shape ℝ → OExp shape ℝ  → OExp shape ℝ
  Product : {shape : Shape} → OExp shape ℝ → OExp shape ℝ → OExp shape ℝ
  Dot : {shape : Shape} → OExp shape ℝ → OExp shape ℝ → OExp Scalar ℝ
  Scale : {shape : Shape} → OExp Scalar ℝ → OExp shape ℝ → OExp shape ℝ 


```

```
infix 5 _+_i 
infixl 6 _+_ 
infixl 7 _*_ 
infix 8 _∙_ 

```


```

_+_ : {shape : Shape} → {et : ElementType} → Exp shape et → Exp shape et → Exp shape et
_+_ = {!!}

_*_ : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt) → Exp shape (Num nt)
_*_ = {!!}

_∙_ : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt) → Exp Scalar (Num nt)
_∙_ = {!!}

_*∙_ : {shape : Shape} → {nt : Number} → Exp Scalar (Num nt) → Exp shape (Num nt) → Exp shape (Num nt)
_*∙_ = {!!}

Re : {shape : Shape} → Exp shape ℂ → Exp shape ℝ
Re (a + b i) = a

Im : {shape : Shape} → Exp shape ℂ → Exp shape ℝ
Im (a + b i) = b

convert : OExp Scalar ℝ → Exp Scalar ℝ
convert (Sum u v) = convert u + convert v
convert (Product u v) = convert u * convert v
convert (Dot (Sum u v) w) = convert (Dot u w) + convert (Dot v w)
convert (Dot (Dot u v) w) = convert (Dot u v) * convert w
convert (Dot (Scale u v) w) = convert u * convert (Dot v w)
convert (Dot (ELit x) w) = {!!}
convert (Dot (EVar x) w) = {!!}
convert (Dot (Product u v) w) = {!!}
convert (Scale u v) = convert u * convert v
convert (ELit x) = EPrim (PLit x)
convert (EVar x) = EPrim (PVar x)

-- convert : {shape : Shape} → OExp shape ℝ → Exp shape ℝ
-- convert (ELit x) = EPrim (PLit x)
-- convert (EVar x) = EPrim (PVar x)
-- convert (Sum u v) = {! convert u + convert v!}
-- convert (Product u u₁) = {!!}
-- convert (Dot u u₁) = {!!}
-- convert (Scale u u₁) = {!!}


-- var : VarId → Exp [] ℝ
-- var x = PVar (V x)

-- var1D : VarId → (n : Nat.ℕ) → Exp (n ∷ []) ℝ
-- var1D x m = PVar (V x)

-- var2D : VarId → (m n : Nat.ℕ) → Exp (m ∷ n ∷ []) ℝ
-- var2D x m n = PVar (V x)

```



* Computing partial derivatives.

If everything is scalar, computing partial derivatives is trivial as we
just need a recursive function, and apply sum rule, product rule and the
chain rule.

Multi-dimensional derivatives, however, is not as so.
We can try:
```
partialDerivative' : {shape : Shape} → (f : Exp Scalar ℝ) → Var shape → Exp shape ℝ
```
If f is constant, then partial derivative is 0[shape]
```
-- partialDerivative' (‵ c) x = ‵ 0.0
```

If f is a scalar variable, then partial derivative is 1[shape] if shape is scalar and
x == y, otherwise 0[shape].
```
-- partialDerivative' {shape = []} (PVar (V y)) (V x) = case (x ≈ y) of λ
--   { (yes _) → ‵ 1.0
--   ; (no _) → ‵ 0.0
--   }
-- partialDerivative' {shape = (n ∷ ns)} (PVar (V y)) (V x) = ‵ 0.0
```

Sum we can apply sum rule
```
partialDerivative' (Sum u v) x = partialDerivative' u x + partialDerivative' v x

```
But here is where it got tricky!
y and z can be of higher dimensions, but we only have partialDerivative where the first
argument is scalar.

We can't make the recursive call!
```
partialDerivative' (Dot u v) x = {!!}
partialDerivative' f = {!!}
```
So we need other approach!



** Plan

We add 𝟙-form and do the transformation

```
times-d : {shape : Shape} → Exp shape ℝ → Exp shape 𝟙-form → Exp shape 𝟙-form
times-d u (Sumd v₁ v₂) = times-d u v₁ + times-d u v₂
times-d u d0 = d0
times-d u (v *d x) =  (u * v)  *d x
times-d u (v ∙d x) =  (u *∙ v) ∙d x 
times-d u (v *∙d x) = (v *∙ u) *d x
times-d u (v ∙*d x) = (u * v) ∙*d x

dot-d : {shape : Shape} → Exp shape ℝ → Exp shape 𝟙-form → Exp Scalar 𝟙-form
dot-d u (Sumd v₁ v₂) = dot-d u v₁ + dot-d u v₂
dot-d u d0 = d0
dot-d u (v *d x) = (u * v)   ∙d x
dot-d u (v ∙d x) = (u *∙ v)  ∙d x
dot-d u (v *∙d x) = (v *∙ u) ∙d x
dot-d u (v ∙*d x) = (u ∙ v)  *d x

scale-d : {shape : Shape} → Exp Scalar ℝ → Exp shape 𝟙-form → Exp shape 𝟙-form
scale-d u (Sumd v₁ v₂) = scale-d u v₁ + scale-d u v₂
scale-d u d0 = d0
scale-d u (v *d x) = (u *∙ v)   *d x
scale-d u (v ∙d x) = (u *∙ v)   ∙d x
scale-d u (v *∙d x) = (u * v)  *∙d x
scale-d u (v ∙*d x) = (u *∙ v) ∙*d x

d : {shape : Shape} → Exp shape ℝ → Exp shape 𝟙-form
d (EPrim (PLit x)) = d0
d (EPrim (PVar x)) = EPrim (PLit 0.0) *d x
d (Sum u v) = d u + d v
d (Product u v) = {!!}
d (Dot u v) = {!!}
d (Scale u@(PLit x) v) =  scale-d (EPrim u) (d v)
d (Scale u@(PVar x) v) = scale-d (EPrim u) (d v) + (v ∙*d x) 
```

```

```

-- After take differential, we can transform the expression so that it always end up with the form

--   // TODO: Data type of this form
--   Either:
--     - DZero (1)
--     - (Exp Scalar ℝ) *∂ (DVar Scalar x) (2)
--     - (Exp shape ℝ) ∙∂ (DVar shape y) (3)
--     - Sum of operands that either in the form of (2) and (3)

-- Then we can extract all partial derivatives.
