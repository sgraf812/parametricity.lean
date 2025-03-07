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

def Exp'.interp : Exp' Ty.interp ty → ty.interp
  | .var x => x
  | .unit => ()
  | .boolLit b => b
  | .app f x => f.interp (x.interp)
  | .lam dom body => fun x => (body x).interp
end SimpleTypes

-- System Fω types:
namespace SystemF

inductive Ki : Type where
  | star : Ki
  | arrow (dom : Ki) (cod : Ki) : Ki
def Ki.interp : Ki → Type 1
  | .star => Type
  | .arrow dom cod => dom.interp → cod.interp

inductive Ty : Type where
  | var (x : Nat) : Ty
  | unit : Ty
  | bool : Ty
  | fn (dom : Ty) (cod : Ty) : Ty
  | forall (x : String) (dom : Ki) (body : Ty) : Ty
  | abs (x : String) (dom : Ki) (body : Ty) : Ty
  | app (f : Ty) (a : Ty) : Ty

abbrev Name := String

-- As in TAPL
def Ty.shift (d : Nat) (cutoff : Nat) : Ty → Ty
  | .var x => .var (if x < cutoff then x else x + d)
  | .unit => .unit
  | .bool => .bool
  | .fn dom cod => .fn (Ty.shift d cutoff dom) (Ty.shift d cutoff cod)
  | .forall x dom body => .forall x dom (Ty.shift d (cutoff + 1) body)
  | .abs x dom body => .abs x dom (Ty.shift d (cutoff + 1) body)
  | .app f a => .app (Ty.shift d cutoff f) (Ty.shift d cutoff a)

-- subst e for var j, and shift e by d (number of entered binders)
def Ty.subst : Ty → Nat → Ty → (d : _ := 0) → Ty
  | .var i, j, e, d => if i < d then .var i else if i = j then Ty.shift d 0 e else .var (i - 1)
  | .unit, _, _, _ => .unit
  | .bool, _, _, _ => .bool
  | .fn dom cod, j, e, d => .fn (dom.subst j e d) (cod.subst j e d)
  | .forall x dom body, j, e, d => .forall x dom (body.subst (j + 1) e (d + 1))
  | .abs x dom body, j, e, d => .abs x dom (body.subst (j + 1) e (d + 1))
  | .app f a, j, e, d => .app (f.subst j e d) (a.subst j e d)

section
notation:65 τ₁ "[" i " ↦ " τ₂ "]" => Ty.subst τ₁ i τ₂
set_option hygiene false
local notation:65 Γ " ⊩ " τ " : " κ:30 => Ty.DefEq Γ τ τ κ
local notation:65 Γ " ⊩ " τ₁ " ≡ " τ₂ " : " κ:30 => Ty.DefEq Γ τ₁ τ₂ κ
inductive Ty.DefEq : List Ki → Ty → Ty → Ki → Prop where
  | symm : Γ ⊩ τ₁ ≡ τ₂ : κ → Γ ⊩ τ₂ ≡ τ₁ : κ
  | trans : Γ ⊩ τ₁ ≡ τ₂ : κ → Γ ⊩ τ₂ ≡ τ₃ : κ → Γ ⊩ τ₁ ≡ τ₃ : κ
  | var : Γ[i]? = .some κ → Γ ⊩ .var i : κ
  | unit : Γ ⊩ .unit : .star
  | bool : Γ ⊩ .bool : .star
  | fn :
      Γ ⊩ dom₁ ≡ dom₂ : κ
    → Γ ⊩ cod₁ ≡ cod₂ : κ
    --------------------------------------------
    → Γ ⊩ .fn dom₁ cod₁ ≡ .fn dom₂ cod₂ : κ

  | forall :
      (dom::Γ) ⊩ body₁ ≡ body₂ : .star
    ------------------------------------------------------------
    → Γ ⊩ .forall _ dom body₁ ≡ .forall _ dom body₂ : .star

  | abs :
      (dom::Γ) ⊩ body₁ ≡ body₂ : cod
    -----------------------------------------------------------------
    → Γ ⊩ .abs _ dom body₁ ≡ .abs _ dom body₂ : .arrow dom cod

  | app :
      Γ ⊩ f₁ ≡ f₂ : .arrow dom cod
    → Γ ⊩ a₁ ≡ a₂ : dom
    ----------------------------------------
    → Γ ⊩ .app f₁ a₁ ≡ .app f₂ a₂ : cod

  | beta :
      dom::Γ ⊩ body : cod
    → Γ ⊩ τ : dom
    ----------------------------------------
    → Γ ⊩ .app (.abs _ dom body) τ ≡ body[0 ↦ τ] : cod

-- def Ty'.interp (free : Name → Type) : Ty' Name → Type
--   | .var x => free x
--   | .unit => Unit
--   | .bool => Bool
--   | .fn dom cod => dom.interp free → cod.interp free
--   | .forall _x dom body => (κ : dom.interp free) → (body κ).interp free
--   | .abs _x dom body => fun (x : dom.interp free) => (body x).interp free
--   | .app f a => f.interp free (a.interp free)

-- inductive Ty where
--   | bvar (x : BName) : Ty
--   | fvar (x : FName) : Ty
--   | unit : Ty
--   | bool : Ty
--   | fn (dom : Ty) (cod : Ty) : Ty
--   | forall (x : FName) (κ : Ki) (body : Ty) : Ty
--   | abs (x : FName) (κ : Ki) (body : Ty) : Ty
--   | app (f : Ty) (a : Ty) : Ty

abbrev FName := Nat
abbrev BName := FName × Nat
inductive Exp where
  | bvar (x : BName) : Exp
  | fvar (x : FName) : Exp
  | unit : Exp
  | boolLit (b : Bool) : Exp
  | abs (x : FName) (τ : Ty) (body : Exp) : Exp
  | app (f : Exp) (a : Exp) : Exp
  | tyabs (x : FName) (κ : Ki) (body : Exp) : Exp
  | tyapp (e : Exp) (τ : Ty) : Exp

inductive TyOrKi where
  | ty (τ : Ty)
  | ki (κ : Ki)
abbrev Ctxt := List (BName × TyOrKi)

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
syntax:lead "∀" ident ":" systemf_kind ", " systemf_type:20 : systemf_type
syntax:lead "λ" ident ":" systemf_kind ", " systemf_type:20 : systemf_type

open Lean in
macro_rules
  | `([ty|($ty)|]) => `([ty|$ty|])
  | `([ty|Unit|]) => `(Ty.unit)
  | `([ty|Bool|]) => `(Ty.bool)
  | `([ty| $x:ident |]) => `(Ty.var $(quote x.getId.toString))
  | `([ty| $f $x |]) => `(Ty.app [ty|$f|] [ty|$x|])
  | `([ty| $ty₁ → $ty₂ |]) => `(Ty.fn [ty|$ty₁|] [ty|$ty₂|])
  | `([ty|∀ $x : $ki, $ty|]) => `(Ty.forall $(quote x.getId.toString) [ki|$ki|] [ty|$ty|])
  | `([ty|λ$x : $ki, $ty|]) => `(Ty.abs $(quote x.getId.toString) [ki|$ki|] [ty|$ty|])

#check [ty|(Bool → Unit) → Unit → Bool|]
-- #check [ty|∀ x, x |]
#check [ty|∀ x : ⋆, x |]
#check [ty|∀ x : ⋆ → ⋆, x Unit |]
#check [ty|∀ x : ⋆ → ⋆ → ⋆, x Unit Bool |]
#check [ty|λ x : ⋆ → ⋆ → ⋆, x Unit Bool |]

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

open Lean in
macro_rules
  | `([exp| $e |]) => `(systemf_term|$e)
  | `(systemf_term|($e)) => `(systemf_term|$e)
  | `(systemf_term|()) => `(Exp.unit)
  | `(systemf_term|true) => `(Exp.boolLit Bool.true)
  | `(systemf_term|false) => `(Exp.boolLit Bool.false)
  | `(systemf_term|$x:ident) => `(Exp.var $(quote x.getId.toString))
  | `(systemf_term|λ$x : $ty, $e) => `(Exp.abs $(quote x.getId.toString) [ty|$ty|] [exp|$e|])
  | `(systemf_term|$f $a) => `(Exp.app [exp|$f|] [exp|$a|])
  | `(systemf_term|Λ$x : $ki, $e) => `(Exp.tyabs $(quote x.getId.toString) [ki|$ki|] [exp|$e|])
  | `(systemf_term|$f[$ty]) => `(Exp.tyapp [exp|$f|] [ty|$ty|])

#check [exp| () |]
#check [exp| (λ x : Unit, x) |]
#check [exp| (Λ α : ⋆, λ x : α, x) |]
#check [exp| (Λ α : ⋆, λ x : α, x)[Unit] () |]

declare_syntax_cat systemf_systemf_ctxt_item
syntax:50 ident " : " systemf_kind : systemf_systemf_ctxt_item
syntax:50 ident " : " systemf_type : systemf_systemf_ctxt_item
syntax:max "[systemf_ctxt| " systemf_systemf_ctxt_item,* " |]" : term
open Lean in
macro_rules
  | `([systemf_ctxt| |]) => `([])
  | `([systemf_ctxt| $x:ident : $ki:systemf_kind |]) => `([($(quote x.getId.toString), TyOrKi.ki [ki|$ki|])])
  | `([systemf_ctxt| $x:ident : $ki:systemf_kind, $ctx,* |]) => `([systemf_ctxt| $ctx,* |] ++ [($(quote x.getId.toString), TyOrKi.ki [ki|$ki|])])
  | `([systemf_ctxt| $x:ident : $ty:systemf_type |]) => `([($(quote x.getId.toString), TyOrKi.ty [ty|$ty|])])
  | `([systemf_ctxt| $x:ident : $ty:systemf_type, $ctx,* |]) => `([systemf_ctxt| $ctx,* |] ++ [($(quote x.getId.toString), TyOrKi.ty [ty|$ty|])])

#check [systemf_ctxt| |]
#check [systemf_ctxt| α : ⋆, β : ⋆ → ⋆ |]
#check [systemf_ctxt| α : ⋆, β : ⋆ → ⋆, γ : ⋆ → ⋆ → ⋆ |]
#check [systemf_ctxt| x : Bool, β : ⋆ → ⋆, x : Unit |]

inductive Ty.Eq : Ty → Ty → Prop
  | refl (τ : Ty) : Ty.Eq τ τ
  | symm (τ₁ : Ty) (τ₂ : Ty) : Ty.Eq τ₁ τ₂ → Ty.Eq τ₂ τ₁
  | trans (τ₁ : Ty) (τ₂ : Ty) (τ₃ : Ty) : Ty.Eq τ₁ τ₂ → Ty.Eq τ₂ τ₃ → Ty.Eq τ₁ τ₃
  | congr_fn (τ₁ : Ty) (τ₂ : Ty) : Ty.Eq τ₁ τ₂ → Ty.Eq (.fn τ₁ τ₂) (.fn τ₁ τ₂)
  | congr_forall (x : Name) (κ : Ki) (τ₁ : Ty) (τ₂ : Ty) : Ty.Eq τ₁ τ₂ → Ty.Eq (.forall x κ τ₁) (.forall x κ τ₂)
  | congr_app (τ₁ : Ty) (τ₂ : Ty) : Ty.Eq τ₁ τ₂ → Ty.Eq (.app τ₁ τ₂) (.app τ₁ τ₂)
  | congr_abs (x : Name) (κ : Ki) (τ₁ : Ty) (τ₂ : Ty) : Ty.Eq τ₁ τ₂ → Ty.Eq (.abs x κ τ₁) (.abs x κ τ₂)


/-
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
-/

end SystemF
