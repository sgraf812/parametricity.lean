import Mathlib.Data.Set.Basic

namespace Parametricity

-- simple types:
namespace SimpleTypes
inductive Ty : Type where
  | unit : Ty
  | bool : Ty
  | fn (dom : Ty) (cod : Ty) : Ty

def Ty.interp : Ty → Type
  | .unit => Unit
  | .bool => Bool
  | .fn dom cod => dom.interp → cod.interp

inductive Exp' (ρ : Ty → Type) : Ty → Type where
  | var (x : ρ ty) : Exp' ρ ty
  | unit : Exp' ρ .unit
  | boolLit (b : Bool) : Exp' ρ .bool
  | app (f : Exp' ρ (.fn dom cod)) (x : Exp' ρ dom) : Exp' ρ cod
  | lam (dom : Ty) (body : ρ dom → Exp' ρ cod) : Exp' ρ (.fn dom cod)
def Exp (ty : Ty) := ∀{ρ : Ty → Type}, Exp' ρ ty

def Exp'.interp {ty : Ty} : Exp' Ty.interp ty → ty.interp
  | .var x => x
  | .unit => ()
  | .boolLit b => b
  | .app f x => f.interp x.interp
  | .lam dom body => fun x => (body x).interp
end SimpleTypes

-- System Fω types:
namespace SystemFProp

inductive Ty' (ρ : Type u) : Type u where
  | var (x : ρ) : Ty' ρ
  | unit : Ty' ρ
  | bool : Ty' ρ
  | fn (dom : Ty' ρ) (cod : Ty' ρ) : Ty' ρ
  | forall (body : ρ → Ty' ρ) : Ty' ρ
--  | abs (body : Ξ dom → Ty' Ξ ran) : Ty' Ξ (.arrow dom ran)
--  | app (f : Ty' Ξ (.arrow dom ran)) (x : Ty' Ξ dom) : Ty' Ξ ran
def Ty : Type (u + 1) := ∀{ρ}, Ty' ρ

def Set.fn (dom : Set Type) (cod : Set Type) : Set Type :=
  { f | ∃ d c, f = (d → c) ∧ d ∈ dom ∧ c ∈ cod }

def Set.forall (body : Set Type → Set Type) : Set Type :=
  { f | ∃ x, f ∈ body x }

@[reducible, simp]
def Ty'.interp : Ty' (Set Type) → Set Type
  | .var x => x
  | .unit => {Unit}
  | .bool => {Bool}
  | .fn dom cod => Set.fn dom.interp cod.interp
  | .forall body => Set.forall (fun x => (body x).interp)

set_option hygiene false in
notation τ₁ "[" τ₂ "]↦ " τ₃ => RelSubst τ₁ τ₂ τ₃
inductive RelSubst : {α : Type u} → (α → Ty' α) → Ty' α → Ty' α → Prop where
  | id : .var [τ]↦ τ
  | var : (fun _ => .var x)[τ]↦ (.var x)
  | bool : (fun _ => .bool)[τ]↦ .bool
  | unit : (fun _ => .unit)[τ]↦ .unit
  | fn (dom : τ₁[τ]↦ τ₁') (ran : τ₂[τ]↦ τ₂')
    : (fun α => .fn (τ₁ α) (τ₂ α))[τ]↦ .fn τ₁' τ₂'
  | forall {τ₁ : α → α → Ty' α} {τ₁' : α → Ty' α}
           (body : ∀ α', RelSubst (fun α => τ₁ α α') τ (τ₁' α'))
    : RelSubst (fun α => .forall (τ₁ α)) τ (.forall τ₁')

class RelSubst2 {α : Type u} (τ₁ : α → Ty' α) (τ₂ : Ty' α) (τ' : outParam (Ty' α)) where
  subst : τ₁[τ₂]↦ τ'

instance : RelSubst2 .var τ τ where
  subst := RelSubst.id

instance : RelSubst2 (fun _ => Ty'.var x) τ (.var x) where
  subst := RelSubst.var

instance : RelSubst2 (fun _ => Ty'.bool) τ .bool where
  subst := RelSubst.bool

instance : RelSubst2 (fun _ => Ty'.unit) τ .unit where
  subst := RelSubst.unit

instance [dom : RelSubst2 τ₁ τ τ₁'] [ran : RelSubst2 τ₂ τ τ₂'] :
  RelSubst2 (fun α => Ty'.fn (τ₁ α) (τ₂ α)) τ (.fn τ₁' τ₂') where
  subst := RelSubst.fn dom.subst ran.subst

instance (τ₁ : α → α → Ty' α) (τ₁' : α → Ty' α)
  [body : ∀ α', RelSubst2 (fun α => τ₁ α α') τ (τ₁' α')] :
  RelSubst2 (fun α => Ty'.forall (τ₁ α)) τ (.forall τ₁') where
  subst := RelSubst.forall (fun α => (body α).subst)

-- def RelSubst.f : ∀{ki₁ ki₂ : Ki} {Ξ : Ki → Type} (τ₁ : Ξ ki₁ → Ty' Ξ ki₂) (τ₂ : Ty' Ξ ki₁) ,

abbrev Elem (ty : Set Type) := ∀ τ, τ ∈ ty → Set τ -- ∀ (τ : Subtype ty), τ.val → Prop
def Elem.mem (x : α) {ty : Set Type} (s : Elem ty) : Prop := ∃ h : α ∈ ty, s α h x
open Classical in
def Elem.singleton {ty : Set Type} (x : α) : Elem ty := fun τ _ y => if h : τ = α then h ▸ x = y else False
def Elem.app {dom cod : Set Type} (f : Elem (Set.fn dom cod)) (a : Elem dom) : Elem cod := fun τ _ =>
  { efa | ∀ τ' (hf : (τ' → τ) ∈ (Set.fn dom cod)) (ha : τ' ∈ dom)
          ef ea (hef : ef ∈ f (τ' → τ) hf) (hea : ea ∈ a τ' ha),
          ef ea = efa }
def Elem.abs {dom cod : Set Type} (body : Elem dom → Elem cod) : Elem (Set.fn dom cod) := fun τ _ =>
  { efn | ∀ τ₁ τ₂ (h : τ = (τ₁ → τ₂)) (hτ₁ : τ₁ ∈ dom) (hτ₂ : τ₂ ∈ cod),
          ∀ (ea : τ₁), body (Elem.singleton ea) τ₂ hτ₂ (cast h efn ea) }
def Elem.tyapp (f : Elem (Set.forall body)) (a : Set Type) : Elem (body a) := fun τ _ =>
  { efa | ∀ τ' (hf : (τ' → τ) ∈ (Set.fn dom cod)) (ha : τ' ∈ dom)
          ef ea (hef : ef ∈ f (τ' → τ) hf) (hea : ea ∈ a τ' ha),
          ef ea = efa }

example : Elem.app (dom := {Unit}) (Elem.abs (fun x => x)) (Elem.singleton ()) Unit (by rfl) () := by
  simp[Elem.abs, Elem.app]
  trivial

example : Elem.app (dom := {Unit}) (Elem.abs (fun x => x)) (Elem.singleton ()) Unit (by rfl) () := by
  simp[Elem.abs, Elem.app]
  trivial

notation "€" => Elem.mem

inductive Exp' {ρ : Type u} (Γ : Ty' ρ → Type 1) : Ty' ρ → Type (max 1 u) where
--  | var (x : Elem (Γ ty)) : Exp' Γ ty
  | var (x : Γ ty) : Exp' Γ ty
  | unit : Exp' Γ .unit
  | boolLit (b : Bool) : Exp' Γ .bool
  | app (f : Exp' Γ (.fn dom cod)) (x : Exp' Γ dom) : Exp' Γ cod
  | abs (dom : Ty' ρ) (body : Γ dom → Exp' Γ cod) : Exp' Γ (.fn dom cod)
  | tyabs {τ : ρ → Ty' ρ} (body : (x : ρ) → Exp' Γ (τ x))
    : Exp' Γ (.forall τ)
  | tyapp (τ₁ : ρ → Ty' ρ) (e : Exp' Γ (.forall τ₁)) (τ₂ : ρ)
    : Exp' Γ (τ₁ τ₂)

-- def Exp {ρ : Type u} (ty : Ty) := ∀ {Γ : Ty' ρ → Type u}, Exp' Γ ty

def Ty'.apply ()

open Classical in
@[reducible]
def Exp'.interp {ty : Ty' (Set Type)} : Exp' (Elem ∘ Ty'.interp) ty → Elem (Ty'.interp ty)
  | .var x => x
  | .unit => Elem.singleton ()
  | .boolLit b => Elem.singleton b
  | .app f x => Elem.app f.interp x.interp
  | .abs dom body => Elem.abs (fun x => (body x).interp)
  | .tyapp scheme f τ => Elem.tyapp f.interp τ
--  | .tyabs body => fun x => (body x).interp
  | _ => sorry

declare_syntax_cat systemf_kind
syntax:max "[ki|" systemf_kind "|]" : term
syntax:max "(" systemf_kind ")" : systemf_kind
syntax:max "⋆" : systemf_kind
syntax:50 systemf_kind:51 " → " systemf_kind:50 : systemf_kind
macro_rules
  | `([ki|($k)|]) => `([ki|$k|])
  | `([ki|⋆|]) => `(Ki.star)
-- | `([ki| $k₁ → $k₂ |]) => `(Ki.arrow [ki|$k₁|] [ki|$k₂|])

-- #check [ki|(⋆ → ⋆) → ⋆ → ⋆|]

declare_syntax_cat systemf_type
syntax:max "[ty|" systemf_type " |]" : term
syntax:max "(" systemf_type ")" : systemf_type
syntax:max "Unit" : systemf_type
syntax:max "Bool" : systemf_type
syntax:max ident : systemf_type
syntax:80 systemf_type:80 systemf_type:81 : systemf_type
syntax:50 systemf_type:51 " → " systemf_type:50 : systemf_type
syntax:lead "∀" ident ", " systemf_type:20 : systemf_type
syntax:lead "∀" ident ":" systemf_kind ", " systemf_type:20 : systemf_type

macro_rules
  | `([ty|($ty)|]) => `([ty|$ty|])
  | `([ty|Unit|]) => `(Ty'.unit)
  | `([ty|Bool|]) => `(Ty'.bool)
  | `([ty| $x:ident |]) => `(Ty'.var $x)
  | `([ty| $f $x |]) => `(Ty'.app [ty|$f|] [ty|$x|])
  | `([ty| $ty₁ → $ty₂ |]) => `(Ty'.fn [ty|$ty₁|] [ty|$ty₂|])
  | `([ty|∀ $x, $ty|]) => `(Ty'.forall (fun $x => [ty|$ty|]))
  | `([ty|∀ $x : $_ki, $ty|]) => `(Ty'.forall (fun $x => [ty|$ty|]))

#check [ty|(Bool → Unit) → Unit → Bool|]
#check [ty|∀ x, x |]
#check [ty|∀ x : ⋆, x |]
-- #check [ty|∀ x : ⋆ → ⋆, x Unit |]
-- #check [ty|∀ x : ⋆ → ⋆ → ⋆, x Unit Bool |]

declare_syntax_cat systemf_term
syntax:max "[exp| " systemf_term " |]" : term

syntax:max "()" : systemf_term
syntax:max "(" systemf_term ")" : systemf_term
syntax:max "true" : systemf_term
syntax:max "false" : systemf_term
syntax:max ident : systemf_term
syntax:80 systemf_term:80 systemf_term:81 : systemf_term
syntax:lead "λ" ident "," systemf_term:20 : systemf_term
syntax:lead "λ" ident ":" systemf_type "," systemf_term:20 : systemf_term
syntax:max systemf_term:max "[" systemf_type:max "]" : systemf_term
syntax:lead "Λ" ident "," systemf_term:20 : systemf_term
syntax:lead "Λ" ident ":" systemf_kind "," systemf_term:20 : systemf_term

macro_rules
  | `([exp| $e |]) => `(systemf_term|$e)
  | `(systemf_term|($e)) => `(systemf_term|$e)
  | `(systemf_term|()) => `(Exp'.unit)
  | `(systemf_term|true) => `(Exp'.boolLit Bool.true)
  | `(systemf_term|false) => `(Exp'.boolLit Bool.false)
  | `(systemf_term|$x:ident) => `(Exp'.var $x)
  | `(systemf_term|λ$x, $e) => `(Exp'.abs _ (fun $x => [exp|$e|]))
  | `(systemf_term|λ$x : $ty, $e) => `(Exp'.abs [ty|$ty|] (fun $x => [exp|$e|]))
  | `(systemf_term|$f $a) => `(Exp'.app [exp|$f|] [exp|$a|])
  | `(systemf_term|Λ$x, $e) => `(Exp'.tyabs (fun $x => [exp|$e|]))
  | `(systemf_term|Λ$x : $_ki, $e) => `(Exp'.tyabs (fun $x => [exp|$e|]))
  | `(systemf_term|$f[$ty]) => `(Exp'.tyapp [exp|$f|] [ty|$ty|] (RelSubst2.subst)) -- tODO fix

#check [exp| () |]
#check [exp| (λ x, x) |]
#check [exp| (λ x : Unit, x) |]
#check [exp| (Λ α, λ x : α, x) |]
-- #check [exp| (Λ α : ⋆, λ x : α, x)[Unit] () |]

-- example : Exp' Ty'.interp0 .unit := [exp| (Λ α : ⋆, λ x : α, x)[Unit] () |]

end SystemFProp

-- System Fω types:
namespace SystemF

inductive Ki : Type u where
  | star : Ki
--  | arrow (dom : Ki) (cod : Ki) : Ki

--def Ki.up : Ki.{u} → Ki.{max u v}
--  | .star => .star

--def Ki.interp : Ki → Type (u + 1)
--  | .star => Type u
--  | .arrow dom cod => dom.interp → cod.interp

--def Ki.interp_up : (ki : Ki) → Ki.interp.{u} ki → Ki.interp.{max u v} ki.up
--  | .star, x => ULift.{max u v} x
--  | .arrow dom cod, f => fun x => Ki.interp_up cod (f x)

--theorem Ki.interp_ulift.{u} (ki : Ki) : ULift (Ki.interp.{u} ki) = Ki.interp.{u+1} ki := by
--  intro ki
--  induction ki
--  case star =>
--    rfl
--  case arrow dom cod ihDom ihCod =>
--    rw [←ihDom]

inductive Ty' (ρ : Type u) : Type u where
  | var (x : ρ) : Ty' ρ
  | unit : Ty' ρ
  | bool : Ty' ρ
  | fn (dom : Ty' ρ) (cod : Ty' ρ) : Ty' ρ
  | forall (body : ρ → Ty' ρ) : Ty' ρ
--  | abs (body : Ξ dom → Ty' Ξ ran) : Ty' Ξ (.arrow dom ran)
--  | app (f : Ty' Ξ (.arrow dom ran)) (x : Ty' Ξ dom) : Ty' Ξ ran
def Ty : Type (u + 1) := ∀{ρ}, Ty' ρ

def Ty'.ULift.pull.{u} {ρ : Type u} : Ty'.{max u v} (ULift ρ) → ULift.{v} (Ty'.{u} ρ)
  | .var x => .up (.var x.down)
  | .unit => .up .unit
  | .bool => .up .bool
  | .fn dom cod => .up (.fn (Ty'.ULift.pull dom).down (Ty'.ULift.pull cod).down)
  | .forall body => .up (.forall (fun x => (Ty'.ULift.pull (body (.up x))).down))

def Ty'.ULift.push.{u} {ρ : Type u} (ty : ULift.{v} (Ty' ρ)) : Ty'.{max u v} (ULift ρ) := go ty.down where
  go : (Ty' ρ) → Ty' (ULift ρ)
    | .var x => .var (.up x)
    | .unit => .unit
    | .bool => .bool
    | .fn dom cod => .fn (go dom) (go cod)
    | .forall body => .forall (fun x => go (body x.down))

theorem Ty'.ULift.pull_push {ρ : Type} (ty : Ty'.{u} (ULift ρ)) :
  Ty'.ULift.push (Ty'.ULift.pull ty) = ty := by
    induction ty <;> simp_all[push, push.go, pull]

theorem Ty'.ULift.push_pull {ρ : Type} (ty : ULift.{u} (Ty'.{0} ρ)) :
  Ty'.ULift.pull (Ty'.ULift.push ty) = ty := by
    cases ty
    next ty =>
    induction ty <;> simp_all[pull, push, push.go]

set_option pp.universes true in
def Ty'.interp.{u} : Ty' (ULift.{u} Type) → ULift.{u} (Type 1)
  | .var x => .up (ULift x.down)
  | .unit => .up (ULift Unit)
  | .bool => .up (ULift Bool)
  | .fn dom cod => .up (dom.interp.down → cod.interp.down)
  | .forall body => .up (∀ x, (body (.up x)).interp.down)
#check Ty'.interp.{0}

def Ty'.interp' : Ty' (Set Type) → Set Type
  | .var x => x
  | .unit => {Unit}
  | .bool => {Bool}
  | .fn dom cod => { f | ∃ d ∈ dom.interp', ∃ c ∈ cod.interp', f = (d → c) }
  | .forall body => { f | ∃ x, f ∈ (body x).interp' }

def Ty'.interp0 (ty : Ty' Type) : Type 1 :=
  (Ty'.interp.{0} (Ty'.ULift.push (.up ty))).down

theorem Better.forall_congr {α : Sort u} {p q : α → Sort v} (h : ∀ a, p a = q a) : (∀ a, p a) = (∀ a, q a) :=
  (funext h : p = q) ▸ rfl

set_option pp.universes true in
theorem Ty'.interp0_interp {ty : Ty' Type} : Ty'.interp0 ty = (Ty'.interp (Ty'.ULift.push (.up ty))).down := by
  induction ty <;> simp_all[interp0, interp, ULift.push, ULift.push.go]
  next ih =>
  apply Better.forall_congr
  intro x
  exact (ih x)

--theorem Ty'.interp_up : Ty'.interp.{u} ty = Ty'.interp.{max u v} (Ty'.up ty) := by

set_option hygiene false in
notation τ₁ "[" τ₂ "]↦ " τ₃ => RelSubst τ₁ τ₂ τ₃
inductive RelSubst : {α : Type u} → (α → Ty' α) → Ty' α → Ty' α → Prop where
  | id : .var [τ]↦ τ
  | var : (fun _ => .var x)[τ]↦ (.var x)
  | bool : (fun _ => .bool)[τ]↦ .bool
  | unit : (fun _ => .unit)[τ]↦ .unit
  | fn (dom : τ₁[τ]↦ τ₁') (ran : τ₂[τ]↦ τ₂')
    : (fun α => .fn (τ₁ α) (τ₂ α))[τ]↦ .fn τ₁' τ₂'
  | forall {τ₁ : α → α → Ty' α} {τ₁' : α → Ty' α}
           (body : ∀ α', RelSubst (fun α => τ₁ α α') τ (τ₁' α'))
    : RelSubst (fun α => .forall (τ₁ α)) τ (.forall τ₁')

class RelSubst2 {α : Type u} (τ₁ : α → Ty' α) (τ₂ : Ty' α) (τ' : outParam (Ty' α)) where
  subst : τ₁[τ₂]↦ τ'

instance : RelSubst2 .var τ τ where
  subst := RelSubst.id

instance : RelSubst2 (fun _ => Ty'.var x) τ (.var x) where
  subst := RelSubst.var

instance : RelSubst2 (fun _ => Ty'.bool) τ .bool where
  subst := RelSubst.bool

instance : RelSubst2 (fun _ => Ty'.unit) τ .unit where
  subst := RelSubst.unit

instance [dom : RelSubst2 τ₁ τ τ₁'] [ran : RelSubst2 τ₂ τ τ₂'] :
  RelSubst2 (fun α => Ty'.fn (τ₁ α) (τ₂ α)) τ (.fn τ₁' τ₂') where
  subst := RelSubst.fn dom.subst ran.subst

instance (τ₁ : α → α → Ty' α) (τ₁' : α → Ty' α)
  [body : ∀ α', RelSubst2 (fun α => τ₁ α α') τ (τ₁' α')] :
  RelSubst2 (fun α => Ty'.forall (τ₁ α)) τ (.forall τ₁') where
  subst := RelSubst.forall (fun α => (body α).subst)

-- def RelSubst.f : ∀{ki₁ ki₂ : Ki} {Ξ : Ki → Type} (τ₁ : Ξ ki₁ → Ty' Ξ ki₂) (τ₂ : Ty' Ξ ki₁) ,

inductive Exp' (Γ : Ty' Type → Type 1) : Ty' Type → Type 1 where
  | var (x : Γ ty) : Exp' Γ ty
  | unit : Exp' Γ .unit
  | boolLit (b : Bool) : Exp' Γ .bool
  | app (f : Exp' Γ (.fn dom cod)) (x : Exp' Γ dom) : Exp' Γ cod
  | abs (dom : Ty' Type) (body : Γ dom → Exp' Γ cod) : Exp' Γ (.fn dom cod)
  | tyabs {τ : Type → Ty' Type} (body : (x : Type) → Exp' Γ (τ x))
    : Exp' Γ (.forall τ)
  | tyapp {τ₁ : Type → Ty' Type} (e : Exp' Γ (.forall τ₁)) (τ₂ : Type)
    : Exp' Γ (τ₁ τ₂)

-- def Exp {ρ : Type u} (ty : Ty) := ∀ {Γ : Ty' ρ → Type u}, Exp' Γ ty

declare_syntax_cat systemf_kind
syntax:max "[ki|" systemf_kind "|]" : term
syntax:max "(" systemf_kind ")" : systemf_kind
syntax:max "⋆" : systemf_kind
syntax:50 systemf_kind:51 " → " systemf_kind:50 : systemf_kind
macro_rules
  | `([ki|($k)|]) => `([ki|$k|])
  | `([ki|⋆|]) => `(Ki.star)
-- | `([ki| $k₁ → $k₂ |]) => `(Ki.arrow [ki|$k₁|] [ki|$k₂|])

-- #check [ki|(⋆ → ⋆) → ⋆ → ⋆|]

declare_syntax_cat systemf_type
syntax:max "[ty|" systemf_type " |]" : term
syntax:max "(" systemf_type ")" : systemf_type
syntax:max "Unit" : systemf_type
syntax:max "Bool" : systemf_type
syntax:max ident : systemf_type
syntax:80 systemf_type:80 systemf_type:81 : systemf_type
syntax:50 systemf_type:51 " → " systemf_type:50 : systemf_type
syntax:lead "∀" ident ", " systemf_type:20 : systemf_type
syntax:lead "∀" ident ":" systemf_kind ", " systemf_type:20 : systemf_type

macro_rules
  | `([ty|($ty)|]) => `([ty|$ty|])
  | `([ty|Unit|]) => `(Ty'.unit)
  | `([ty|Bool|]) => `(Ty'.bool)
  | `([ty| $x:ident |]) => `(Ty'.var $x)
  | `([ty| $f $x |]) => `(Ty'.app [ty|$f|] [ty|$x|])
  | `([ty| $ty₁ → $ty₂ |]) => `(Ty'.fn [ty|$ty₁|] [ty|$ty₂|])
  | `([ty|∀ $x, $ty|]) => `(Ty'.forall (fun $x => [ty|$ty|]))
  | `([ty|∀ $x : $_ki, $ty|]) => `(Ty'.forall (fun $x => [ty|$ty|]))

#check [ty|(Bool → Unit) → Unit → Bool|]
#check [ty|∀ x, x |]
#check [ty|∀ x : ⋆, x |]
-- #check [ty|∀ x : ⋆ → ⋆, x Unit |]
-- #check [ty|∀ x : ⋆ → ⋆ → ⋆, x Unit Bool |]

declare_syntax_cat systemf_term
syntax:max "[exp| " systemf_term " |]" : term

syntax:max "()" : systemf_term
syntax:max "(" systemf_term ")" : systemf_term
syntax:max "true" : systemf_term
syntax:max "false" : systemf_term
syntax:max ident : systemf_term
syntax:80 systemf_term:80 systemf_term:81 : systemf_term
syntax:lead "λ" ident "," systemf_term:20 : systemf_term
syntax:lead "λ" ident ":" systemf_type "," systemf_term:20 : systemf_term
syntax:max systemf_term:max "[" systemf_type:max "]" : systemf_term
syntax:lead "Λ" ident "," systemf_term:20 : systemf_term
syntax:lead "Λ" ident ":" systemf_kind "," systemf_term:20 : systemf_term

macro_rules
  | `([exp| $e |]) => `(systemf_term|$e)
  | `(systemf_term|($e)) => `(systemf_term|$e)
  | `(systemf_term|()) => `(Exp'.unit)
  | `(systemf_term|true) => `(Exp'.boolLit Bool.true)
  | `(systemf_term|false) => `(Exp'.boolLit Bool.false)
  | `(systemf_term|$x:ident) => `(Exp'.var $x)
  | `(systemf_term|λ$x, $e) => `(Exp'.abs _ (fun $x => [exp|$e|]))
  | `(systemf_term|λ$x : $ty, $e) => `(Exp'.abs [ty|$ty|] (fun $x => [exp|$e|]))
  | `(systemf_term|$f $a) => `(Exp'.app [exp|$f|] [exp|$a|])
  | `(systemf_term|Λ$x, $e) => `(Exp'.tyabs (fun $x => [exp|$e|]))
  | `(systemf_term|Λ$x : $_ki, $e) => `(Exp'.tyabs (fun $x => [exp|$e|]))
  | `(systemf_term|$f[$ty]) => `(Exp'.tyapp [exp|$f|] [ty|$ty|] (RelSubst2.subst)) -- tODO fix

#check [exp| () |]
#check [exp| (λ x, x) |]
#check [exp| (λ x : Unit, x) |]
#check [exp| (Λ α, λ x : α, x) |]
-- #check [exp| (Λ α : ⋆, λ x : α, x)[Unit] () |]

-- example : Exp' Ty'.interp0 .unit := [exp| (Λ α : ⋆, λ x : α, x)[Unit] () |]

def Exp'.interp {ty : Ty' Type} : Exp' Ty'.interp0 ty → (Ty'.interp.{1} (Ty'.ULift.push (.up ty))).down
  | .var x => Ty'.interp0_interp ▸ x
  | .unit => Ty'.interp0_interp ▸ .up ⟨⟩
  | .boolLit b => Ty'.interp0_interp ▸ .up b
  | .app f x => f.interp x.interp
  | .abs dom cod => fun x => (cod (Ty'.interp0_interp ▸ x)).interp
  | .tyabs body => fun x => (body x).interp
  | @Exp'.tyapp _ _ _ _ => sorry -- e.interp τ
  | _ => sorry

end SystemF
