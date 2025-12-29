import Mathlib.Tactic

variable {α : Type} (A B C : Set α)

-- # Set identities

-- ## Boolean algebra
-- Idempotence
example : A ∪ A = A := by
  ext x; constructor
  case mp =>
    intro hx
    obtain hx1 | hx2 := hx
    case inl => exact hx1
    case inr => exact hx2
  case mpr =>
    intro hx
    left
    exact hx

example : A ∩ A = A := by
  ext x; constructor
  case mp => intro hx ; exact hx.left
  case mpr => intro hx ; exact ⟨hx , hx⟩

-- Identity
example : A ∩ ∅ = ∅ := by
  ext x; constructor
  case mp =>
    intro hx
    exact hx.right
  case mpr =>
    intro hx
    contradiction

example : A ∪ Set.univ = Set.univ := by
  ext x; constructor
  case mp => intro hx; trivial
  case mpr => intro hx ; right; trivial

-- Commutativity
example : A ∩ B = B ∩ A := by
  ext x; constructor
  repeat intro hx; exact ⟨hx.right, hx.left⟩

example : A ∪ B = B ∪ A := by
  ext x; constructor
  repeat
    intro hx
    obtain hx1 | hx2 := hx
    case inl => right; exact hx1
    case inr => left; exact hx2

-- Associativity
example : A ∩ (B ∩ C) = (A ∩ B) ∩ C := by
  ext x; constructor
  case mp =>
    intro hx
    obtain ⟨hx1,⟨hx2,hx3⟩⟩ := hx
    exact  ⟨⟨hx1,hx2⟩,hx3⟩
  case mpr =>
    intro hx
    obtain ⟨⟨hx1,hx2⟩,hx3⟩ := hx
    exact  ⟨hx1,⟨hx2,hx3⟩⟩

example : A ∪ (B ∪ C) = (A ∪ B) ∪ C := by
  ext x; constructor
  case mp =>
    intro hx
    obtain hx1 | (hx2 | hx3) := hx
    case inl => left; left; exact hx1
    case inr.inl => left; right; exact hx2
    case inr.inr => right; exact hx3
  case mpr =>
    intro hx
    obtain (hx1 | hx2) | hx3 := hx
    case inl.inl => left; exact hx1
    case inl.inr => right; left; exact hx2
    case inr => right; right; exact hx3

-- Distributivity
example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  intro hx
  case mp =>
    obtain hxa | ⟨hxb, hxc⟩ := hx
    case inl =>
      constructor
      case left => left ; exact hxa
      case right => left ; exact hxa
    case inr =>
      constructor
      case left => right ; exact hxb
      case right => right ; exact hxc
  case mpr =>
    intro hx
    obtain ⟨hxa1 | hxb, hxa2 | hxc⟩ := hx
    case inl.inl => left ; exact hxa1
    case inl.inr => left ; exact hxa1
    case inr.inl => left ; exact hxa2
    case inr.inr => right ; exact ⟨hxb, hxc⟩

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x; constructor
  case mp =>
    intro hx
    obtain ⟨hx1, hx2 | hx3⟩ := hx
    case inl => left; exact ⟨hx1,hx2⟩
    case inr => right; exact ⟨hx1,hx3⟩
  case mpr =>
    intro hx
    obtain ⟨hx1,hx2⟩ | ⟨ hx3, hx4⟩ := hx
    case inl => exact ⟨hx1, Or.inl hx2⟩
    case inr => exact ⟨hx3, Or.inr hx4⟩

-- DeMorgan
theorem deMorgan_union : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  constructor
  case mp =>
    intro hx
    constructor
    case left =>
      intro ha
      have wab : x ∈ A ∪ B := by
        left ; exact ha
      exact hx wab
    case right =>
      intro hb
      have wab : x ∈ A ∪ B := by
        right ; exact hb
      exact hx wab
  case mpr =>
    intro hx
    obtain ⟨hx1, hx2⟩ := hx
    intro hab
    obtain ha | hb := hab
    case inl => contradiction
    case inr => contradiction

example : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rw [← compl_compl (Aᶜ ∪ Bᶜ)]
  rw [deMorgan_union, compl_compl, compl_compl]

-- ## Empty set
example : A = ∅ ↔ ∀ x : α, ¬(x ∈ A) := by
  constructor
  case mp =>
    intro ha x xa
    rw [ha] at xa
    contradiction
  case mpr =>
    intro ha
    ext x; constructor
    case mp => intro hx; specialize ha x; contradiction
    case mpr => intro hx; contradiction

example : A ≠ ∅ ↔ ∃ x, x ∈ A := by
  constructor
  case mp =>
    intro ha
    by_contra hc
    apply ha
    push_neg at hc
    ext x; constructor
    case mp =>
      intro hx; specialize hc x; contradiction
    case mpr =>
      intro hx; contradiction
  case mpr =>
    intro hx ha
    rw [ha] at hx
    obtain ⟨x, x_in_empty⟩ := hx
    contradiction

example : A ∩ B = ∅ ↔ A ⊆ Bᶜ := by
  constructor
  case mp =>
    intro hab a ha hb
    have w : a ∈ A ∩ B := ⟨ha, hb⟩
    rw [hab] at w
    contradiction
  case mpr =>
    intro hab
    ext x; constructor
    case mp =>
      intro hx
      obtain ⟨hxa, hxb⟩ := hx
      apply hab at hxa
      contradiction
    case mpr => intro hx; contradiction

-- ## Containment properties
example : A ⊆ B → B ⊆ A → A = B := by sorry
example : A ⊆ B ↔ A ∪ B = B := by sorry

example : A ⊆ B ↔ A ∩ B = A := by
  constructor
  case mp =>
    intro haib
    ext x
    constructor
    case mp =>
      intro hab
      exact hab.left
    case mpr =>
      intro ha
      have hb : x ∈ B := haib ha
      exact ⟨ha, hb⟩
  case mpr =>
    intro h
    rw [← h]
    intro x xab
    exact xab.right


example : A ⊆ B → B ⊆ C → A ⊆ C := by sorry
example : A ⊆ B ∧ A ⊆ C → A ⊆ B ∩ C := by sorry
example : A ⊆ C ∧ B ⊆ C → A ∪ B ⊆ C := by sorry
example {F G : Set (Set α)} (h : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by sorry
example {F G : Set (Set α)} (h : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by sorry

-- # Functions

variable {β : Type} (U V : Set β) (f : α → β)

-- ## Images
example (hab : A ⊆ B) : f '' A ⊆ f '' B := by
  intro b hb
  obtain ⟨a, ⟨ha1, ha2⟩⟩ := hb
  apply hab at ha1
  use a

example : f '' (A ∪ B) = (f '' A) ∪ (f '' B) := by sorry
example : f '' (A  ∩ B) ⊆  (f '' A) ∩  (f '' B) := by sorry

example {F : Set (Set α)} : f '' ⋃₀ F = ⋃₀ {V : Set β | ∃ U ∈ F, V = f '' U} := by sorry
example {F : Set (Set α)} : f '' ⋂₀ F ⊆ ⋂₀ {V : Set β | ∃ U ∈ F, V = f '' U} := by sorry

-- ## Preimages
example (huv : U ⊆ V) : f ⁻¹' U ⊆ f ⁻¹' V := by
  intro a ha
  apply huv at ha
  exact ha

example : f ⁻¹' (U  ∩ V ) = (f ⁻¹' U) ∩ (f ⁻¹' V )  := by
  ext x; constructor
  repeat
    intro hx
    exact hx

example :  f ⁻¹' (U  ∪ V ) = (f ⁻¹' U) ∪ (f ⁻¹' V ) := by sorry

example {F : Set (Set β)} : f ⁻¹' (⋂₀ F ) = ⋂ (V : Set β) (hV: V ∈  F), f ⁻¹' V := by sorry

example {F : Set (Set β)} : f ⁻¹' (⋂₀ F ) = ⋂₀ { (f ⁻¹' V) | V ∈ F} := by
  ext x; constructor
  case mp =>
    intro hx; rw [Set.mem_preimage] at hx
    intro t ht
    obtain ⟨v, ⟨hv1, hv2⟩⟩ := ht
    sorry
  case mpr =>
    sorry


example {F : Set (Set β)} : f ⁻¹' (⋃₀ F ) = ⋃ (V : Set β) (hV: V ∈  F), f ⁻¹' V := by sorry

example {F : Set (Set β)} : f ⁻¹' (⋃₀ F ) = ⋃₀ {(f ⁻¹' V) | V ∈  F} := by sorry

-- ## Interaction
-- Loop
example : f '' (f ⁻¹' V ) ⊆ V := by
  intro b hb
  rw [Set.mem_image] at hb
  obtain ⟨x, ⟨hx1, hx2⟩⟩ := hb
  rw [Set.mem_preimage, hx2] at hx1
  exact hx1

example : A ⊆ f ⁻¹' (f '' A) := by
  intro a ha
  rw [Set.mem_preimage, Set.mem_image]
  use a

-- Galois connection
example : f '' A ⊆ U ↔ A ⊆ f ⁻¹' U := by
  constructor
  case mp =>
    intro imf a ha
    have fa : f a ∈ f '' A := by use a
    specialize imf fa
    exact imf
  case mpr =>
    intro h y hy
    rw [Set.mem_image] at hy
    obtain ⟨x, hx⟩ := hy
    obtain ⟨hx1, hx2⟩ := hx
    specialize h hx1
    rw [Set.mem_preimage, hx2] at h
    exact h
