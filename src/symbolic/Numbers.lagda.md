```
module symbolic.Numbers where


open import Level using (Level; lift)
  renaming ( _⊔_ to _⊍_ ; suc to ℓsuc; zero to ℓ₀ )

record RealNumber : Set₁ where
  field
    ℝ : Set 
    _+_ : ℝ → ℝ → ℝ
    _*_ : ℝ → ℝ → ℝ
    𝟘 : ℝ
    𝟙 : ℝ

record ComplexNumber : Set₁ where
  field
    Real : RealNumber
  open RealNumber Real public
```
