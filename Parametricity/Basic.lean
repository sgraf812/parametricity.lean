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

def Exp.interp : Exp Ty.interp ty → ty.interp
  | .var x => x
  | .unit => ()
  | .boolLit b => b
  | .app f x => f.interp (x.interp)
  | .lam dom body => fun x => body x.interp
end SimpleTypes

-- System Fω types:
namespace SystemF

inductive Ki : Type where
  | star : Ki
  | arrow (dom : Ki) (cod : Ki) : Ki

def Ki.interp : Ki → Type 1
  | .star => Type
  | .arrow dom cod => dom.interp → cod.interp

inductive Ty' (Ξ : Ki → Type u) : Ki → Type u where
  | var (x : Ξ ki) : Ty' Ξ ki
  | unit : Ty' Ξ .star
  | bool : Ty' Ξ .star
  | fn (dom : Ty' Ξ .star) (cod : Ty' Ξ .star) : Ty' Ξ .star
  | forall (body : Ξ .star → Ty' Ξ .star) : Ty' Ξ .star
  | abs (body : Ξ dom → Ty' Ξ ran) : Ty' Ξ (.arrow dom ran)
  | app (f : Ty' Ξ (.arrow dom ran)) (x : Ty' Ξ dom) : Ty' Ξ ran
def Ty (ki : Ki) : Type (u + 1) := ∀{Ξ}, Ty' Ξ ki

def Ty'.interp : Ty' Ki.interp ki → ki.interp
  | .var x => x
  | .unit => Unit
  | .bool => Bool
  | .fn dom cod => dom.interp → cod.interp
  | .forall body => ∀ x, (body x).interp
  | .abs body => fun x => (body x).interp
  | .app f x => f.interp x.interp

set_option hygiene false in
notation τ₁ "[" τ₂ "]↦ " τ₃ => RelSubst τ₁ τ₂ τ₃
inductive RelSubst : {Ξ : Ki → Type 1} → {ki₁ : Ki} → {ki₂ : Ki} → (Ξ ki₁ → Ty' Ξ ki₂) → Ty' Ξ ki₁ → Ty' Ξ ki₂ → Prop where
  | id : .var [τ]↦ τ
  | var : (fun _ => .var x)[τ]↦ (.var x)
  | bool : (fun _ => .bool)[τ]↦ .bool
  | unit : (fun _ => .unit)[τ]↦ .unit
  | fn (dom : τ₁[τ]↦ τ₁') (ran : τ₂[τ]↦ τ₂')
    : (fun α => .fn (τ₁ α) (τ₂ α))[τ]↦ .fn τ₁' τ₂'
  | forall {τ₁ : Ξ ki → Ξ dom → Ty' Ξ ran} {τ₁' : Ξ dom → Ty' Ξ ran}
           (body : ∀ α', RelSubst (ki₁:=ki) (fun α => τ₁ α α') τ (τ₁' α'))
    : RelSubst (ki₁ := ki) (fun α => .forall (τ₁ α)) τ (.forall τ₁')

class RelSubst2 {Ξ : Ki → Type 1} {ki₁ : Ki} {ki₂ : Ki} (τ₁ : Ξ ki₁ → Ty' Ξ ki₂) (τ₂ : Ty' Ξ ki₁) (τ' : outParam (Ty' Ξ ki₂)) where
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

instance (τ₁ : Ξ ki → Ξ dom → Ty' Ξ ran) (τ₁' : Ξ dom → Ty' Ξ ran)
  [body : ∀ α', RelSubst2 (ki₁:=ki) (fun α => τ₁ α α') τ (τ₁' α')] :
  RelSubst2 (fun α => Ty'.forall (τ₁ α)) τ (.forall τ₁') where
  subst := RelSubst.forall (fun α => (body α).subst)

-- def RelSubst.f : ∀{ki₁ ki₂ : Ki} {Ξ : Ki → Type} (τ₁ : Ξ ki₁ → Ty' Ξ ki₂) (τ₂ : Ty' Ξ ki₁) ,

inductive Exp' (Ξ : Ki → Type 1) (Γ : (ki:Ki) → Ty' Ξ ki → ki.interp) : {ki:Ki} → Ty' Ξ ki → Type 1 where
  | var (x : Γ .star ty) : Exp' Ξ Γ ty
  | unit : Exp' Ξ Γ .unit
  | boolLit (b : Bool) : Exp' Ξ Γ .bool
  | app (f : Exp' Ξ Γ (.fn dom cod)) (x : Exp' Ξ Γ dom) : Exp' Ξ Γ cod
  | abs (dom : Ty' Ξ .star) (body : Γ .star dom → Exp' Ξ Γ cod) : Exp' Ξ Γ (.fn dom cod)
  | tyabs (dom : Ki) {τ : Ξ dom → Ty' Ξ ran} (body : (x : Ξ dom) → Exp' Ξ Γ (τ x))
    : Exp' Ξ Γ (.forall τ)
  | tyapp {τ₁ : Ξ dom → Ty' Ξ ran}
          (e : Exp' Ξ Γ (.forall τ₁)) (τ₂ : Ty' Ξ dom) (subst : RelSubst τ₁ τ₂ τ')
    : Exp' Ξ Γ τ'

def Exp (ki : Ki) (ty : Ty ki) := ∀ {Ξ : Ki → Type 1} {Γ : (ki : Ki) → Ty' Ξ ki → ki.interp}, Exp' Ξ Γ ty

declare_syntax_cat systemf_kind
syntax:max "[ki|" systemf_kind "|]" : term
syntax:max "(" systemf_kind ")" : systemf_kind
syntax:max "⋆" : systemf_kind
syntax:50 systemf_kind:51 " → " systemf_kind:50 : systemf_kind
macro_rules
  | `([ki|($k)|]) => `([ki|$k|])
  | `([ki|⋆|]) => `(Ki.star)
  | `([ki| $k₁ → $k₂ |]) => `(Ki.arrow [ki|$k₁|] [ki|$k₂|])

#check [ki|(⋆ → ⋆) → ⋆ → ⋆|]

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
  | `([ty|∀ $x : $ki, $ty|]) => `(Ty'.forall (dom := [ki|$ki|]) (fun $x => [ty|$ty|]))

#check [ty|(Bool → Unit) → Unit → Bool|]
#check [ty|∀ x, x |]
#check [ty|∀ x : ⋆, x |]
#check [ty|∀ x : ⋆ → ⋆, x Unit |]
#check [ty|∀ x : ⋆ → ⋆ → ⋆, x Unit Bool |]

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
  | `(systemf_term|Λ$x, $e) => `(Exp'.tyabs _ (fun $x => [exp|$e|]))
  | `(systemf_term|Λ$x : $ki, $e) => `(Exp'.tyabs [ki|$ki|] (fun $x => [exp|$e|]))
  | `(systemf_term|$f[$ty]) => `(Exp'.tyapp [exp|$f|] [ty|$ty|] (RelSubst2.subst))

#check [exp| () |]
#check [exp| (λ x, x) |]
#check [exp| (λ x : Unit, x) |]
#check [exp| (Λ α, λ x : α, x) |]
#check [exp| (Λ α, λ x : α, x)[Unit] () |]

example : Exp .star .unit := [exp| (Λ α, λ x : α, x)[Unit] () |]

def Exp'.interp {ty : Ty' Ki.interp .star} : Exp' Ki.interp @Ty'.interp ty → Ty'.interp ty
  | .var x => x
  | .unit => ⟨⟩
  | .boolLit b => b
  | .app f x => f.interp x.interp
  | .abs dom cod => fun x => (cod x).interp
  | .tyabs dom body => let x := ty; _
--  | .tyapp e τ subst => e.interp τ

end SystemF
