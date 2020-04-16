

```
module symbolic.Exp2 where

open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Nat as Nat using ()
open import Data.Integer as Int using ()
open import Data.Float


open import Data.String as String using (String)
open import Data.Product as Product using ( _×_ ; _,_ ; Σ ; proj₁ ; proj₂ )
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
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

```
Shape : Set
Shape = List Nat.ℕ

Scalar : Shape
Scalar = []
```
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

```

Now, expression constructors
```
data Exp : Shape → ElementType → Set where
  ELit : {shape : Shape} → Float → Exp shape ℝ
  EVar : {shape : Shape} → Var shape → Exp shape ℝ
  Sum : {shape : Shape} → Exp shape ℝ → Exp shape ℝ → Exp shape ℝ
  Product : {shape : Shape} → Exp shape ℝ → Exp shape ℝ → Exp shape ℝ
  Dot : {shape : Shape}  → Exp shape ℝ → Exp shape ℝ → Exp Scalar ℝ
  Scale : {shape : Shape} → Exp Scalar ℝ → Exp shape ℝ → Exp shape ℝ 
  _+_i : {shape : Shape} → Exp shape ℝ → Exp shape ℝ → Exp shape ℂ

  -- 𝟙-form related
  -- For computing partial derivatives
  d0 : {shape : Shape} → Exp shape 𝟙-form
  Sumd : {shape : Shape} → Exp shape 𝟙-form → Exp shape 𝟙-form → Exp shape 𝟙-form
  _*d_ : {shape : Shape} → Exp shape ℝ → Var shape → Exp shape 𝟙-form
  _∙d_ : {shape : Shape} → Exp shape ℝ → Var shape → Exp Scalar 𝟙-form
```

```
infix 5 _+_i 
infixl 6 _+_ _-_
infixl 7 _*_ 
infix 8 _∙_ _*∙_

```

```

_+_ : {shape : Shape} → {et : ElementType} → Exp shape et → Exp shape et → Exp shape et
_*_ : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt) → Exp shape (Num nt)
_∙_ : {shape : Shape} → {nt : Number} → Exp shape (Num nt) → Exp shape (Num nt) → Exp Scalar (Num nt)
_*∙_ : {shape : Shape} → {nt : Number} → Exp Scalar (Num nt) → Exp shape (Num nt) → Exp shape (Num nt)
_-_ : {shape : Shape} → Exp shape ℝ → Exp shape ℝ → Exp shape ℝ

_+_ {et = Num Real} = Sum
_+_ {et = Num Complex} (x + y i) (u + v i) = (x + u) + (y + v) i
_+_ {et = 𝟙-form} = Sumd

_*_ {nt = Real} = Product
_*_ {nt = Complex} (x + y i) (u + v i) = (x * u - y * v) + (x * v + y * u) i

_∙_ {nt = Real} = Dot
_∙_ {nt = Complex} (x + y i) (u + v i) = {!!}

_*∙_ {nt = Real} = Scale
_*∙_ {nt = Complex} = {!!}

x - y = x + (ELit (-1.0)) *∙ y

```



The key to computing derivatives is to eliminate `Scale` node out of Exp Scalar ℝ.

```
data NoScale : {shape : Shape} → Exp shape ℝ → Set where
  NSLit : {shape : Shape} → {x : Float} → NoScale (ELit {shape} x)
  NSVar : {shape : Shape} → {x : Var shape} → NoScale (EVar {shape} x)
  NSSum : {shape : Shape} → {u v : Exp shape ℝ} → NoScale u → NoScale v → NoScale (Sum u v)
  NSProduct : {shape : Shape} → {u v : Exp shape ℝ} → NoScale u → NoScale v → NoScale (Product u v)
  NSDot : {shape : Shape}  → {u v : Exp shape ℝ} → NoScale u → NoScale v → NoScale (Dot u v)



```

To do that we some sort of a normal form:
  An expression is in normal form if it is either:
    - Exp with no scaling (1)
    - (x scale y) where x and y have no scaling (2)
    - Sum of normal forms

```
data NSExp : (shape : Shape) → Set where 
  ⟦_,_⟧ : {shape : Shape} → (e : Exp shape ℝ) → NoScale e → NSExp shape


data NF : (shape : Shape) → Set where
  NS : {shape : Shape} → NSExp shape → NF shape
  ScaleNS : {shape : Shape} → NSExp Scalar → NSExp shape → NF shape
  SumNF : {shape : Shape} → NF shape → NF shape → NF shape


```

The function `transform` turn expressions to normal forms.
```
transform : {shape : Shape} → Exp shape ℝ → NF shape
```

To implement which we need several helpers

```
_|*|_ : {shape : Shape} → NF shape → NF shape → NF shape
a |*| SumNF b c = SumNF (a |*| b) (a |*| c)
SumNF a b |*| c = SumNF (a |*| c) (b |*| c)

NS ⟦ x , nsx ⟧ |*| NS ⟦ y , nsy ⟧ = NS ⟦ x * y , NSProduct nsx nsy ⟧
NS ⟦ x , nsx ⟧ |*| ScaleNS y ⟦ z , nsz ⟧ = ScaleNS y ⟦ x * z , NSProduct nsx nsz ⟧
ScaleNS x ⟦ y , nsy ⟧ |*| NS ⟦ z , nsz ⟧ = ScaleNS x ⟦ y * z , NSProduct nsy nsz ⟧
ScaleNS ⟦ a , nsa ⟧ ⟦ x , nsx ⟧ |*| ScaleNS ⟦ b , nsb ⟧ ⟦ y , nsy ⟧
  = ScaleNS ⟦ a * b , NSProduct nsa nsb ⟧ ⟦ x * y , NSProduct nsx nsy ⟧


_|∙|_ : {shape : Shape} → NF shape → NF shape → NF Scalar
a |∙| SumNF b c = SumNF (a |∙| b) (a |∙| c)
SumNF a b |∙| c = SumNF (a |∙| c) (b |∙| c)

NS ⟦ x , nsx ⟧ |∙| NS ⟦ y , nsy ⟧ = NS ⟦ Dot x y , NSDot nsx nsy ⟧
NS ⟦ x , nsx ⟧ |∙| ScaleNS y ⟦ z , nsz ⟧ = ScaleNS y ⟦ x ∙ z , NSDot nsx nsz ⟧
ScaleNS x ⟦ y , nsy ⟧ |∙| NS ⟦ z , nsz ⟧ = ScaleNS x ⟦ y ∙ z , NSDot nsy nsz ⟧
ScaleNS ⟦ a , nsa ⟧ ⟦ x , nsx ⟧ |∙| ScaleNS ⟦ b , nsb ⟧ ⟦ y , nsy ⟧
  = ScaleNS ⟦ a * b , NSProduct nsa nsb ⟧ ⟦ x ∙ y , NSDot nsx nsy ⟧

_|*∙|_ : {shape : Shape} → NF Scalar → NF shape → NF shape
a |*∙| SumNF b c = SumNF (a |*∙| b) (a |*∙| c)
SumNF a b |*∙| c = SumNF (a |*∙| c) (b |*∙| c)

NS x |*∙| NS y = ScaleNS x y
NS ⟦ x , nsx ⟧ |*∙| ScaleNS ⟦ y , nsy ⟧ z = ScaleNS ⟦ (x * y) , NSProduct nsx nsy ⟧ z
ScaleNS ⟦ x , nsx ⟧ ⟦ y , nsy ⟧ |*∙| NS z = ScaleNS ⟦ (x * y) , NSProduct nsx nsy ⟧ z
ScaleNS ⟦ a , nsa ⟧ ⟦ b , nsb ⟧ |*∙| ScaleNS ⟦ c , nsc ⟧ x
  = ScaleNS ⟦ (a * b) * c , NSProduct (NSProduct nsa nsb) nsc ⟧ x

```
We can then put together `transform`
```
transform (ELit x) = NS ⟦ ELit x , NSLit ⟧
transform (EVar x) = NS ⟦ EVar x , NSVar ⟧
transform (Sum u v) = SumNF (transform u) (transform v)
transform (Product u v) = (transform u) |*| (transform v)
transform (Dot u v) = transform u |∙| transform v
transform (Scale u v) = transform u |*∙| transform v
```


If y is scalar, x scale y is equivalent to x * y, therefore we can entirely eliminate scaling
out of any scalar expression.
```
elimScalarNF : NF Scalar → NSExp Scalar
elimScalarNF (NS x) = x
elimScalarNF (ScaleNS ⟦ x , nsx ⟧ ⟦ y , nsy ⟧) = ⟦ x * y , NSProduct nsx nsy ⟧
elimScalarNF (SumNF u v) with elimScalarNF u | elimScalarNF v
... | ⟦ x , nsx ⟧ | ⟦ y , nsy ⟧ = ⟦ x + y , NSSum nsx nsy ⟧

elimScale : Exp Scalar ℝ → NSExp Scalar
elimScale e = elimScalarNF (transform e)
```


Turn any expression ℝ with no-scale to a corresponding expression 𝟙-form
```
times-d : {shape : Shape} → Exp shape ℝ → Exp shape 𝟙-form → Exp shape 𝟙-form
times-d u d0 = d0
times-d u (Sumd v w) = (times-d u v) + (times-d u w)
times-d u (v *d x) = (u *  v) *d x
times-d u (v ∙d x) = (u *∙ v) ∙d x

dot-d : {shape : Shape} → Exp shape ℝ → Exp shape 𝟙-form → Exp Scalar 𝟙-form
dot-d u d0 = d0
dot-d u (Sumd v w) = dot-d u v + dot-d u w
dot-d u (v *d x) = (u *  v) ∙d x
dot-d u (v ∙d x) = (u *∙ v) ∙d x

noscale-d : {shape : Shape} → (e : Exp shape ℝ) → NoScale e → Exp shape 𝟙-form
noscale-d (ELit x) NSLit = d0
noscale-d (EVar x) NSVar = (ELit 1.0) *d x
noscale-d (Sum x y) (NSSum nsx nsy) = noscale-d x nsx + noscale-d y nsy
noscale-d (Product x y) (NSProduct nsx nsy) =  times-d x (noscale-d y nsy) + times-d y (noscale-d x nsx)
noscale-d (Dot x y) (NSDot nsx nsy) = dot-d x (noscale-d y nsy) + dot-d y (noscale-d x nsx)

```


Finally, compute the 𝟙-form of Expression Scalar ℝ because we can eliminate
scaling out of it.

```
d : Exp Scalar ℝ → Exp Scalar 𝟙-form
d u = case elimScale u of λ
  { ⟦ e , x ⟧ → noscale-d e x
  }



```

To compute partial derivatie we just have to traverse the 𝟙-form and extract

```
∂_/∂_ : {shape : Shape} → Exp Scalar ℝ → Var shape → Exp shape ℝ
∂ f /∂ x =  {!!}
```

```
module _  where
  var : VarId → Exp [] ℝ
  var x = EVar (V x)

  var1D : VarId → (n : Nat.ℕ) → Exp (n ∷ []) ℝ
  var1D x m = EVar (V x)

  var2D : VarId → (m n : Nat.ℕ) → Exp (m ∷ n ∷ []) ℝ
  var2D x m n = EVar (V x)

  
```
