namespace hidden

constants (α : Type) (op : α → α → α)

notation a `*` b := op a b

def identity_element (e : α) := ∀ x : α, e * x = x ∧ x * e = x
-- We don't need to define this axiom, because we'll define an identity element later
axiom exists_idetity_element : ∃ e : α, identity_element e
-- Define an element e is identity element
constant e : α
constant identity_e : identity_element e

def inverse (x : α) (y : α) := identity_element (x * y) ∧ identity_element (y * x)
axiom exists_inverse : ∀ x : α, ∃ y: α, inverse x y
axiom associative_law : ∀  x : α, ∀ y : α, ∀ z : α, (x * y) * z = x * (y * z)

theorem unique_identity_element : ∀ e₁ : α, identity_element e₁ → e₁ = e :=
    assume e₁ : α,
    assume h : identity_element e₁,
    calc e₁ = e₁ * e    : by rw (identity_e e₁).right
        ... = e         : by rw (h e).left

example : ∀ x: α , ∀ z: α, inverse x z → x * z = e :=
    assume x : α,
    assume z : α,
    assume h : inverse x z,
    have identity_element (x * z), from h.left,
    show (x * z) = e, from unique_identity_element (x * z) h.left

theorem unique_inverse : ∀ x : α, ∀ y : α, ∀ z : α, inverse x y ∧ inverse x z → y = z :=
    assume x : α,
    assume y : α,
    assume z : α,
    assume h : inverse x y ∧ inverse x z,
    calc y  = y * e         : by rw (identity_e y).right
        ... = y * (x * z)   : by rw unique_identity_element (x * z) h.right.left
        ... = (y * x) * z   : by rw associative_law
        ... = e * z         : by rw unique_identity_element (y * x) h.left.right
        ... = z             : by rw (identity_e z).left

theorem double_inverse : ∀ x : α, ∀ y : α, ∀ z: α, inverse x y ∧ inverse y z → x = z :=
    assume x : α, assume y : α, assume z : α,
    assume h : inverse x y ∧ inverse y z,
    calc x  = x * e         : by rw (identity_e x).right
        ... = x * (y * z)   : by rw unique_identity_element (y * z) h.right.left
        ... = (x * y) * z   : by rw associative_law
        ... = e * z         : by rw unique_identity_element (x * y) h.left.left
        ... = z             : by rw (identity_e z).left

-- subgroup
variable p : α → Prop
def associative := let β := subtype p in
    ∀ x : β, ∀ y : β, ∀ z : β, (x * y) * z = x * (y * z)
def contains_identity_element := let β := subtype p in
    ∃ e : β, identity_element e
def contains_inverse := let β := subtype p in
    ∀ x : β, ∃ y: β, inverse x y
def closed_under_op := let β := subtype p in
    ∀ x : β, ∀ y : β, ∃ z : β, x * y = z
def is_subgroup :=
    (∃ x : subtype p, true) ∧ associative p ∧ contains_identity_element p ∧ contains_inverse p ∧ closed_under_op p

set_option eqn_compiler.zeta true

example : (∃ x : subtype p, true) → (closed_under_op p ∧ contains_inverse p → is_subgroup p) := let β := subtype p in
    assume not_empty: ∃ x: β, true,
    assume h: closed_under_op p ∧ contains_inverse p,
    have h₁: associative p, from (
        assume x : β, assume y : β, assume z : β,
        associative_law x y z
    ),
    have h₂: ∃ e : β, identity_element e, from (
        match not_empty with ⟨w, hw⟩ :=
            match (h.right w) with ⟨iw, hiw⟩ :=
                match (h.left w iw) with ⟨e, he⟩ :=
                    have identity_element (w * iw), from hiw.left,
                    have identity_element e, from he ▸ this,
                    exists.intro e this
                end
            end
        end
    ),
    show is_subgroup p, from ⟨ not_empty, h₁, h₂, h.right, h.left ⟩

example : (∃ x : subtype p, true) → (∀ x : subtype p, ∀ y : subtype p, ∃ z : subtype p, ∃ w : subtype p, inverse y z ∧ x * z = w) → is_subgroup p := let β := subtype p in
    assume not_empty: ∃ x: β, true,
    assume h: ∀ x : β, ∀ y : β, ∃ z : β, ∃ w : β, inverse y z ∧ x * z = w,
    have h₁: associative p, from (
        assume x : β, assume y : β, assume z : β,
        associative_law x y z
    ),
    have h₂: ∃ e : β, identity_element e, from (
        match not_empty with ⟨x, hx⟩ :=
            match (h x x) with ⟨ix, hix⟩ :=
                match hix with ⟨e, he⟩ :=
                    have identity_element (x * ix), from he.left.left,
                    have identity_element e, from he.right ▸ this,
                    exists.intro e this
                end
            end
        end
    ),
    have h₃: ∀ x : β, ∃ y: β, inverse x y, from (
        assume x: β,
        match h₂ with ⟨e, he⟩ :=
            match (h e x) with ⟨ix, hix⟩ :=
                match hix with ⟨ix₂, hix₂⟩ :=
                    have inverse x ix, from hix₂.left,
                    have ha: e * ix = ix₂, from hix₂.right,
                    have hb: e * ix = ix, from (he ix).left,
                    have inverse x (e * ix), from (eq.symm hb) ▸ ‹inverse x ix›,
                    have inverse x ix₂, from ha ▸ this,
                    exists.intro ix₂ this
                end
            end
        end
    ),
    have h₄: ∀ x : β, ∀ y : β, ∃ z : β, x * y = z, from (
        assume x: β,
        assume y: β,
        match (h₃ y) with ⟨iy, hiy⟩ :=
            match (h x iy) with ⟨y₂, hy₂⟩ :=
                match hy₂ with ⟨z, hz⟩ :=
                    have ↑y = ↑y₂, from double_inverse y iy y₂ (⟨hiy, hz.left⟩),
                    have x * y = z, from eq.symm this ▸ hz.right,
                    show ∃ z: β, x * y = z, from exists.intro z this
                end
            end
        end
    ),
    show is_subgroup p, from ⟨ not_empty, h₁, h₂, h₃, h₄ ⟩

end hidden
