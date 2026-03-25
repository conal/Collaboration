-- Telomare: A Denotational Specification of a Total Functional Language
-- Following Conal Elliott's Denotational Design + Type Class Morphisms methodology.
--
-- Core idea: every computation is a function (Tel → Maybe (a × Tel)).
-- Tel (the "telomere") strictly decreases on each recursive unfolding,
-- guaranteeing totality. Time and space are bounded by initial tel.

{-# OPTIONS --guardedness #-}
module telomare where

open import Data.Nat             using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Maybe           using (Maybe; just; nothing; _>>=_)
open import Data.Product         using (_×_; _,_; proj₁; proj₂)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Unit            using (⊤; tt)
open import Data.Bool            using (Bool; true; false; not; if_then_else_)
open import Function             using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Agda.Primitive                        using (lzero)

-- ─────────────────────────────────────────────────────────────────────────────
-- § 1.  SEMANTIC MODEL  (Denotational Design: choose the model first)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- The denotation of every computation is:
--
--   ⟦ e : τ ⟧ : Tel → Maybe (⟦τ⟧ × Tel)
--
-- where Tel = ℕ (the "telomere").
-- • just (v , g') means: produced value v, g' tel remains.
-- • nothing       means: telomere exhausted — program halts gracefully.
--
-- This is the Kleisli category of the monad TelM.

Tel : Set
Tel = ℕ

TelM : Set → Set
TelM A = Tel → Maybe (A × Tel)

-- ─────────────────────────────────────────────────────────────────────────────
-- § 2.  TelM IS A MONAD  (instances follow from the semantic model — TCM)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- TCM = Type Class Morphism (Elliott, ICFP 2009).
-- A TCM is a function h : A → B that is a homomorphism for a given type class:
-- the class structure on A corresponds to the class structure on B via h.
-- Here h = ⟦·⟧ (the denotation function).
--
-- TCM principle (Elliott): "the instance's meaning follows the meaning's instance."
-- TelM A ≅ StateT Tel Maybe A, so all instances are derived homomorphically.

return-tel : {A : Set} → A → TelM A
return-tel a g = just (a , g)          -- pure values cost 0 tel

bind-tel : {A B : Set} → TelM A → (A → TelM B) → TelM B
bind-tel m f g = m g >>= λ { (a , g') → f a g' }

-- Consume exactly 1 unit of tel (one "step" / one telomere shortening)
step : {A : Set} → TelM A → TelM A
step m zero    = nothing               -- telomere exhausted
step m (suc g) = m g                   -- consume 1, continue

-- ─────────────────────────────────────────────────────────────────────────────
-- § 3.  TYPES OF THE OBJECT LANGUAGE
-- ─────────────────────────────────────────────────────────────────────────────

data Ty : Set where
  unit  : Ty
  bool  : Ty
  nat   : Ty
  _⊗_   : Ty → Ty → Ty              -- product
  _⊕_   : Ty → Ty → Ty              -- sum
  _⇒_   : Ty → Ty → Ty              -- function (costs tel on apply)

-- Denotation of types as Agda types
⟦_⟧T : Ty → Set
⟦ unit  ⟧T = ⊤
⟦ bool  ⟧T = Bool
⟦ nat   ⟧T = ℕ
⟦ A ⊗ B ⟧T = ⟦ A ⟧T × ⟦ B ⟧T
⟦ A ⊕ B ⟧T = ⟦ A ⟧T ⊎ ⟦ B ⟧T
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → TelM ⟦ B ⟧T   -- functions live in TelM

-- ─────────────────────────────────────────────────────────────────────────────
-- § 4.  THE KLEISLI CATEGORY OF TelM
--       (Compiling to Categories: programs are morphisms in this category)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Objects  : Agda types (or ⟦τ⟧T for object-language types)
-- Morphisms: A →K B  =  A → TelM B
--
-- Identity and composition satisfy the category laws provably.

infixr 0 _→K_
_→K_ : Set → Set → Set
A →K B = A → TelM B

idK : {A : Set} → A →K A
idK = return-tel

_∘K_ : {A B C : Set} → (B →K C) → (A →K B) → (A →K C)
(g ∘K f) a = bind-tel (f a) g

-- Cartesian structure (fork / projections)
forkK : {A B C : Set} → (A →K B) → (A →K C) → (A →K (B × C))
forkK f g a = bind-tel (f a) λ b →
              bind-tel (g a) λ c →
              return-tel (b , c)

exlK : {A B : Set} → (A × B) →K A
exlK = return-tel ∘ proj₁

exrK : {A B : Set} → (A × B) →K B
exrK = return-tel ∘ proj₂

-- ─────────────────────────────────────────────────────────────────────────────
-- § 5.  THE ONLY RECURSION PRIMITIVE — fix with mandatory tel consumption
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Every unfolding of fix costs 1 tel.
-- Therefore recursion depth ≤ initial tel.  Totality follows immediately.
--
-- Implementation note: Agda requires structural recursion.  We satisfy this
-- with the "fuel" pattern: fix-aux recurses on an explicit Tel fuel argument
-- that decreases by 1 on each unfolding.  The computation tel t' is threaded
-- independently.  fix ties the fuel to the computation's own tel supply,
-- so the bound is tight: depth ≤ initial tel.

private
  fix-aux : {A : Set} → Tel → ((A →K A) → (A →K A)) → A →K A
  fix-aux zero    _    _ _       = nothing          -- fuel exhausted ⟹ halt
  fix-aux (suc f) body a g       = body (fix-aux f body) a g

fix : {A : Set} → ((A →K A) → (A →K A)) → A →K A
fix body a g = fix-aux g body a g
-- The fuel equals the tel: each unfolding reduces both by 1 (via body's
-- internal step calls), keeping the bound tight.

-- Generalised fixpoint: input type S may differ from output type R.
-- (fix is the special case S = R.)
private
  fixT-aux : {S R : Set} → Tel → ((S →K R) → S →K R) → S →K R
  fixT-aux zero    _    _ _ = nothing
  fixT-aux (suc f) body s   = step (body (fixT-aux f body) s)

fixT : {S R : Set} → ((S →K R) → S →K R) → S →K R
fixT body s g = fixT-aux g body s g

-- ─────────────────────────────────────────────────────────────────────────────
-- § 6.  COMPLEXITY BOUNDS  (derived from the semantic model)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Let c : TelM A.  Run it with initial tel t₀.
--
--   Time  (steps taken) = t₀ − t_final    ≤ t₀
--   Depth (call depth)  ≤ t₀              (each recursive call costs ≥ 1)
--   Space               = O(depth × frame) = O(t₀)
--
-- Formally: if c t₀ = just (v , t_f) then the number of `step` calls ≤ t₀.

-- Helper: tel consumed
tel-consumed : {A : Set} → TelM A → Tel → Maybe ℕ
tel-consumed c g₀ = c g₀ >>= λ { (_ , gf) → just (g₀ ∸ gf) }

-- ─────────────────────────────────────────────────────────────────────────────
-- § 7.  TOTALITY THEOREM
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Every TelM computation terminates: it returns just or nothing, never diverges.
-- This holds by construction — TelM A = Tel → Maybe (A × Tel) is a total function.
-- No partiality, no ⊥, no coinduction needed.
--
-- Proof sketch (by induction on tel):
--   Base:  step m 0       = nothing                       ✓ terminates
--   Step:  step m (suc t) = m t   (recurse on strictly smaller tel)  ✓

-- Stated as a proposition: running any TelM computation is decidable.
data Result (A : Set) : Set where
  halted   : Result A           -- out of tel
  finished : A → ℕ → Result A  -- value + tel remaining

run : {A : Set} → TelM A → Tel → Result A
run c g with c g
... | nothing       = halted
... | just (v , gf) = finished v gf

-- ─────────────────────────────────────────────────────────────────────────────
-- § 8.  TYPE CLASS MORPHISM LAWS  (Elliott's TCM principle as propositions)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- The denotation ⟦·⟧ must be a homomorphism for Category:
--
--   ⟦ id ⟧       ≡ idK
--   ⟦ g ∘ f ⟧    ≡ ⟦g⟧ ∘K ⟦f⟧
--
-- Stated for the Kleisli category laws:

-- Left identity:  idK ∘K f ≡ f
left-id : {A B : Set} (f : A →K B) (a : A) (t : Tel) →
          (idK ∘K f) a t ≡ f a t
left-id f a t with f a t
... | nothing      = refl
... | just (b , t') = refl

-- Right identity: f ∘K idK ≡ f
right-id : {A B : Set} (f : A →K B) (a : A) (t : Tel) →
           (f ∘K idK) a t ≡ f a t
right-id f a t with f a t
... | nothing      = refl
... | just (b , t') = refl

-- ─────────────────────────────────────────────────────────────────────────────
-- § 9.  FELIX INTEGRATION  (github.com/conal/felix)
--
--  Felix is Conal Elliott's Agda library for category-theoretic denotational
--  design. It provides formal interfaces — Category, Cartesian, CategoryH —
--  that our Kleisli category of TelM already satisfies.
--
--  Here we instantiate those interfaces, making the connection explicit:
--
--    FR.Category  _→K_   — raw category (idK and ∘K)
--    FR.Cartesian _→K_   — Cartesian structure (forkK, exlK, exrK)
--    FL.Category  _→K_   — lawful category (identity laws + associativity)
--
--  The denotation function ⟦_⟧ : Telomare syntax → _→K_ would be a
--  FL.Homomorphism.CategoryH, making the TCM principle machine-checkable.
-- ─────────────────────────────────────────────────────────────────────────────

import Felix.Object      as FO
import Felix.Equiv       as FE
import Felix.Raw         as FR
import Felix.Laws        as FL
import Felix.Homomorphism as FH

-- 9a.  Products for Set — needed so Felix knows ⊤ and × for objects
instance
  Set-Products : FO.Products Set
  Set-Products = record { ⊤ = ⊤ ; _×_ = _×_ }

-- 9b.  Equivalence on Kleisli morphisms: pointwise propositional equality
--       f ≈ g  iff  ∀ a t → f a t ≡ g a t
instance
  →K-Equiv : FE.Equivalent lzero _→K_
  →K-Equiv = record
    { _≈_   = λ f g → ∀ a t → f a t ≡ g a t
    ; equiv = record
        { refl  = λ _ _ → refl
        ; sym   = λ p a t → sym (p a t)
        ; trans = λ p q a t → trans (p a t) (q a t)
        }
    }

-- 9c.  Raw Category: idK and ∘K satisfy Felix's Category interface
instance
  →K-RawCat : FR.Category _→K_
  →K-RawCat = record { id = idK ; _∘_ = _∘K_ }

-- 9d.  Raw Cartesian: forkK / exlK / exrK satisfy Felix's Cartesian interface
instance
  →K-RawCart : FR.Cartesian _→K_
  →K-RawCart = record { ! = λ _ → return-tel tt ; _▵_ = forkK ; exl = exlK ; exr = exrK }

-- 9e.  Proofs for the lawful Category instance
--
--  We need three lemmas beyond §8's left-id / right-id:
--    Maybe->>=-assoc : monad associativity for Maybe (needed for assoc-tel)
--    assoc-tel       : ((h ∘K g) ∘K f) a t ≡ (h ∘K (g ∘K f)) a t
--    >>=-congˡ       : helper for congruence proof
--    ∘≈-tel          : h ≈ k → f ≈ g → h ∘K f ≈ k ∘K g  (pointwise)

private
  -- Associativity of Kleisli composition by direct case analysis on f a t.
  assoc-tel : {A B C D : Set} {f : A →K B} {g : B →K C} {h : C →K D}
            → ∀ a t → ((h ∘K g) ∘K f) a t ≡ (h ∘K (g ∘K f)) a t
  assoc-tel {f = f} {g} {h} a t with f a t
  ... | nothing       = refl
  ... | just (b , t') with g b t'
  ...   | nothing        = refl
  ...   | just (c , t'') = refl

  -- Congruence of >>= in the first argument (the Maybe value).
  >>=-congˡ : ∀ {α β : Set} (m : Maybe α) {f g : α → Maybe β}
            → (∀ x → f x ≡ g x) → (m >>= f) ≡ (m >>= g)
  >>=-congˡ nothing  _  = refl
  >>=-congˡ (just x) pf = pf x

  -- Congruence of Kleisli composition:
  --   h ≈ k  →  f ≈ g  →  h ∘K f ≈ k ∘K g  (all ≈ are pointwise)
  ∘≈-tel : ∀ {α β γ : Set} {h k : β →K γ} {f g : α →K β}
         → (∀ b t → h b t ≡ k b t)
         → (∀ a t → f a t ≡ g a t)
         → ∀ a t → (h ∘K f) a t ≡ (k ∘K g) a t
  ∘≈-tel {h = h} {g = g} h≈k f≈g a t =
    trans (cong (λ m → m >>= λ { (b , t') → h b t' }) (f≈g a t))
          (>>=-congˡ (g a t) λ { (b , t') → h≈k b t' })

-- 9f.  Lawful Category instance: _→K_ satisfies Felix's Laws.Category
instance
  →K-LawCat : FL.Category _→K_
  →K-LawCat = record
    { identityˡ = λ {_} {_} {f}             → left-id  f
    ; identityʳ = λ {_} {_} {f}             → right-id f
    ; assoc     = λ {_} {_} {_} {_} {f} {g} {h} → assoc-tel {f = f} {g = g} {h = h}
    ; ∘≈        = λ {_} {_} {_} {f} {g} {h} {k} → ∘≈-tel   {h = h} {k = k} {f = f} {g = g}
    }

-- ─────────────────────────────────────────────────────────────────────────────
-- § 10.  DENOTATION HOMOMORPHISM  (the TCM principle, machine-checked)
--
-- We define Telomare's SYNTAX CATEGORY _⇨S_ and prove that the denotation
-- function ⟦_⟧ is a Felix CategoryH (functor) into the Kleisli category _→K_.
--
-- This makes the TCM equations machine-checked:
--
--   ⟦ idS    ⟧ = idK              (F-id,  by definition)
--   ⟦ g ∘S f ⟧ = ⟦g⟧ ∘K ⟦f⟧     (F-∘,   by definition)
--   f ≈S g   ⟹  ⟦f⟧ ≈ ⟦g⟧       (F-cong, proved below)
--
-- Any violation would be an abstraction leak: implementation behaviour
-- diverges from the semantic model, making equational reasoning unsound.
-- ─────────────────────────────────────────────────────────────────────────────

-- 10a.  Syntax morphisms — the free category over Telomare's primitives.
--       Objects are Telomare types (Ty); morphisms are terms-in-context.
infix 0 _⇨S_
data _⇨S_ : Ty → Ty → Set where
  idS   : {A : Ty} → A ⇨S A
  _∘S_  : {A B C : Ty} → (B ⇨S C) → (A ⇨S B) → (A ⇨S C)
  !S    : {A : Ty} → A ⇨S unit
  forkS : {A B C : Ty} → (A ⇨S B) → (A ⇨S C) → (A ⇨S (B ⊗ C))
  exlS  : {A B : Ty} → (A ⊗ B) ⇨S A
  exrS  : {A B : Ty} → (A ⊗ B) ⇨S B
  -- Nat primitives
  zeroS      : unit ⇨S nat
  sucS       : nat ⇨S nat
  predS      : nat ⇨S nat
  addS       : (nat ⊗ nat) ⇨S nat
  isNonZeroS : nat ⇨S bool
  -- Conditional: test, then-branch, else-branch (all from same input)
  condS      : {A B : Ty} → (A ⇨S bool) → (A ⇨S B) → (A ⇨S B) → A ⇨S B
  -- Function application (cartesian closed structure)
  evalS      : {A B : Ty} → ((A ⇒ B) ⊗ A) ⇨S B
  -- Recursion: body receives (recur, state), returns result
  fixTS      : {S R : Ty} → (((S ⇒ R) ⊗ S) ⇨S R) → S ⇨S R

-- 10b.  Syntactic equivalence — the equational theory of the syntax category.
--       Identifies morphisms up to the category laws (identity, associativity,
--       congruence) without collapsing to propositional equality on terms.
infix 4 _≈S_
data _≈S_ : {A B : Ty} → (A ⇨S B) → (A ⇨S B) → Set where
  reflS   : {A B : Ty} {f : A ⇨S B}
          → f ≈S f
  symS    : {A B : Ty} {f g : A ⇨S B}
          → f ≈S g → g ≈S f
  transS  : {A B : Ty} {f g h : A ⇨S B}
          → f ≈S g → g ≈S h → f ≈S h
  -- Category laws (generating the equational theory)
  ∘-idlS  : {A B : Ty} {f : A ⇨S B}
          → (idS ∘S f) ≈S f
  ∘-idrS  : {A B : Ty} {f : A ⇨S B}
          → (f ∘S idS) ≈S f
  ∘-assS  : {A B C D : Ty} {f : A ⇨S B} {g : B ⇨S C} {h : C ⇨S D}
          → ((h ∘S g) ∘S f) ≈S (h ∘S (g ∘S f))
  ∘-congS : {A B C : Ty} {f f' : A ⇨S B} {g g' : B ⇨S C}
          → g ≈S g' → f ≈S f' → (g ∘S f) ≈S (g' ∘S f')

-- 10c.  Denotation of syntax morphisms into the Kleisli category.
--       ⟦_⟧ maps each syntactic term to its semantic Kleisli morphism.
⟦_⟧ : {A B : Ty} → (A ⇨S B) → (⟦ A ⟧T →K ⟦ B ⟧T)
⟦ idS        ⟧ = idK
⟦ g ∘S f     ⟧ = ⟦ g ⟧ ∘K ⟦ f ⟧
⟦ !S         ⟧ = λ _ → return-tel tt
⟦ forkS f g  ⟧ = forkK ⟦ f ⟧ ⟦ g ⟧
⟦ exlS       ⟧ = exlK
⟦ exrS       ⟧ = exrK
⟦ zeroS         ⟧ = λ _ → return-tel 0
⟦ sucS          ⟧ = λ n → return-tel (suc n)
⟦ predS         ⟧ = λ { zero → return-tel zero ; (suc n) → return-tel n }
⟦ addS          ⟧ = λ { (m , n) → return-tel (m + n) }
⟦ isNonZeroS    ⟧ = λ { zero → return-tel false ; (suc _) → return-tel true }
⟦ condS test t f ⟧ = λ a → bind-tel (⟦ test ⟧ a) (λ b → if b then ⟦ t ⟧ a else ⟦ f ⟧ a)
⟦ evalS         ⟧ = λ { (f , a) → f a }
⟦ fixTS body    ⟧ = fixT (λ recur s → ⟦ body ⟧ (recur , s))

-- 10d.  Felix instances for the syntax category.

-- Equivalence: use the syntactic equational theory as the setoid.
instance
  ⇨S-Equiv : FE.Equivalent lzero _⇨S_
  ⇨S-Equiv = record
    { _≈_   = _≈S_
    ; equiv = record { refl = reflS ; sym = symS ; trans = transS }
    }

-- Raw category: idS and _∘S_ directly.
instance
  ⇨S-RawCat : FR.Category _⇨S_
  ⇨S-RawCat = record { id = idS ; _∘_ = _∘S_ }

-- Lawful category: the syntactic laws are the constructors of _≈S_.
instance
  ⇨S-LawCat : FL.Category _⇨S_
  ⇨S-LawCat = record
    { identityˡ = λ {_} {_} {f}             → ∘-idlS  {f = f}
    ; identityʳ = λ {_} {_} {f}             → ∘-idrS  {f = f}
    ; assoc     = λ {_} {_} {_} {_} {f} {g} {h} → ∘-assS  {f = f} {g = g} {h = h}
    ; ∘≈        = λ {_} {_} {_} {f} {g} {h} {k} → ∘-congS {f = f} {f' = g} {g = h} {g' = k}
    }

-- 10e.  Homomorphism structure.

-- Object map: Ty → Set via ⟦_⟧T.
instance
  Ty→Set-Hₒ : FH.Homomorphismₒ Ty Set
  Ty→Set-Hₒ = record { Fₒ = ⟦_⟧T }

-- Morphism map: _⇨S_ → _→K_ via ⟦_⟧.
instance
  ⟦⟧-H : FH.Homomorphism _⇨S_ _→K_
  ⟦⟧-H = record { Fₘ = ⟦_⟧ }

-- 10f.  ⟦_⟧ preserves syntactic equivalence (F-cong).
--       Each constructor of _≈S_ maps to the corresponding law on _→K_.
⟦⟧-cong : {A B : Ty} {f g : A ⇨S B}
         → f ≈S g
         → ∀ a t → ⟦ f ⟧ a t ≡ ⟦ g ⟧ a t
⟦⟧-cong reflS                               a t = refl
⟦⟧-cong (symS p)                            a t = sym   (⟦⟧-cong p a t)
⟦⟧-cong (transS p q)                        a t = trans (⟦⟧-cong p a t) (⟦⟧-cong q a t)
⟦⟧-cong (∘-idlS  {f = f})                  a t = left-id  ⟦ f ⟧ a t
⟦⟧-cong (∘-idrS  {f = f})                  a t = right-id ⟦ f ⟧ a t
⟦⟧-cong (∘-assS  {f = f} {g = g} {h = h})  a t = assoc-tel {f = ⟦ f ⟧} {g = ⟦ g ⟧} {h = ⟦ h ⟧} a t
⟦⟧-cong (∘-congS {f = f} {f' = f'} {g = g} {g' = g'} p q) a t =
  ∘≈-tel {h = ⟦ g ⟧} {k = ⟦ g' ⟧} {f = ⟦ f ⟧} {g = ⟦ f' ⟧} (⟦⟧-cong p) (⟦⟧-cong q) a t

-- 10g.  THE HOMOMORPHISM THEOREM.
--       ⟦_⟧ is a CategoryH — a functor from the syntax category to _→K_.
--
--       F-id and F-∘ hold by DEFINITION (refl): the denotation of idS is idK,
--       and the denotation of composition IS Kleisli composition.
--       F-cong is proved by induction on the syntactic equivalence above.
instance
  ⟦⟧-CategoryH : FH.CategoryH _⇨S_ _→K_
  ⟦⟧-CategoryH = record
    { F-cong = ⟦⟧-cong
    ; F-id   = λ _ _ → refl    -- ⟦ idS ⟧ = idK,          definitionally
    ; F-∘    = λ _ _ → refl    -- ⟦ g ∘S f ⟧ = ⟦g⟧ ∘K ⟦f⟧, definitionally
    }

-- ─────────────────────────────────────────────────────────────────────────────
-- § 11.  OBJECT-LANGUAGE FIBONACCI  (full pipeline: syntax → ⟦_⟧ → run)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Here we write fibonacci entirely in the object language (_⇨S_), denote it
-- into the Kleisli category via ⟦_⟧, and run it.  This is the full pipeline:
--
--   syntax term  ─⟦_⟧─▸  Kleisli morphism  ─run─▸  Result
--
-- Point-free categorical style is verbose — this is exactly what
-- "Compiling to Categories" (Elliott, ICFP 2017) automates away.

-- State type: (counter, (fib_k, fib_{k+1}))
FibStateT : Ty
FibStateT = nat ⊗ (nat ⊗ nat)

-- The body of the fixpoint.
-- Input type: (recur, (cnt, (a, b)))  where recur : FibStateT ⇒ nat
-- If cnt ≠ 0: recur (pred cnt, (b, a + b))
-- If cnt = 0: return a
private
  BodyIn : Ty
  BodyIn = (FibStateT ⇒ nat) ⊗ FibStateT

  -- Projections from (recur, (cnt, (a, b)))
  recurP : BodyIn ⇨S (FibStateT ⇒ nat)
  recurP = exlS

  cntP : BodyIn ⇨S nat
  cntP = exlS ∘S exrS

  aP : BodyIn ⇨S nat
  aP = exlS ∘S (exrS ∘S exrS)

  bP : BodyIn ⇨S nat
  bP = exrS ∘S (exrS ∘S exrS)

  -- New state: (pred cnt, (b, a + b))
  newStateP : BodyIn ⇨S FibStateT
  newStateP = forkS (predS ∘S cntP)
                     (forkS bP (addS ∘S forkS aP bP))

  -- Apply recur to new state
  recurCallP : BodyIn ⇨S nat
  recurCallP = evalS ∘S forkS recurP newStateP

fibBodyS : BodyIn ⇨S nat
fibBodyS = condS (isNonZeroS ∘S cntP) recurCallP aP

-- The fixpoint: FibStateT → nat
fibInnerS : FibStateT ⇨S nat
fibInnerS = fixTS fibBodyS

-- Initial state setup: n ↦ (n, (0, 1))
initStateS : nat ⇨S FibStateT
initStateS = forkS idS (forkS (zeroS ∘S !S) (sucS ∘S (zeroS ∘S !S)))

-- The complete program: nat → nat
fibS : nat ⇨S nat
fibS = fibInnerS ∘S initStateS

-- ── Execution: denote then run ────────────────────────────────────────────
fibS-0  : Result ℕ ;  fibS-0  = run (⟦ fibS ⟧ 0)  2
fibS-1  : Result ℕ ;  fibS-1  = run (⟦ fibS ⟧ 1)  3
fibS-5  : Result ℕ ;  fibS-5  = run (⟦ fibS ⟧ 5)  7
fibS-10 : Result ℕ ;  fibS-10 = run (⟦ fibS ⟧ 10) 12

fibS-10-starved : Result ℕ
fibS-10-starved = run (⟦ fibS ⟧ 10) 5

-- ─────────────────────────────────────────────────────────────────────────────
-- § 12.  FIBONACCI IN THE SEMANTIC DOMAIN  (for comparison)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- The same computation, but written directly as a Kleisli morphism —
-- bypassing the syntax category.  Much shorter, but no machine-checked
-- homomorphism connecting it to the object language.
--
-- Iterative Fibonacci using fixT directly:
--
--   State S = ℕ × ℕ × ℕ   (counter, fib_k, fib_{k+1})
--   Result R = ℕ
--
--   The body checks the counter: if non-zero, step forward; if zero, return.
--   Each unfolding costs 1 tel (via fixT's step).
--   Tel cost: exactly n + 1 steps.

private
  isNonZero : ℕ → Bool
  isNonZero zero    = false
  isNonZero (suc _) = true

  predℕ : ℕ → ℕ
  predℕ zero    = zero
  predℕ (suc k) = k

FibState : Set
FibState = ℕ × ℕ × ℕ    -- (counter, a = fib_k, b = fib_{k+1})

fib : ℕ →K ℕ
fib n = fixT {S = FibState} {R = ℕ}
          (λ recur s →
            let cnt = proj₁ s
                a   = proj₁ (proj₂ s)
                b   = proj₂ (proj₂ s)
            in if isNonZero cnt
                 then recur (predℕ cnt , b , a + b)
                 else return-tel a)
          (n , 0 , 1)

-- ── Running Fibonacci ───────────────────────────────────────────────────────

fib-0  : Result ℕ ;  fib-0  = run (fib 0)  2
fib-1  : Result ℕ ;  fib-1  = run (fib 1)  3
fib-2  : Result ℕ ;  fib-2  = run (fib 2)  4
fib-3  : Result ℕ ;  fib-3  = run (fib 3)  5
fib-4  : Result ℕ ;  fib-4  = run (fib 4)  6
fib-5  : Result ℕ ;  fib-5  = run (fib 5)  7
fib-6  : Result ℕ ;  fib-6  = run (fib 6)  8
fib-7  : Result ℕ ;  fib-7  = run (fib 7)  9
fib-8  : Result ℕ ;  fib-8  = run (fib 8)  10
fib-9  : Result ℕ ;  fib-9  = run (fib 9)  11
fib-10 : Result ℕ ;  fib-10 = run (fib 10) 12

-- Out-of-tel example:
fib-10-starved : Result ℕ
fib-10-starved = run (fib 10) 5    -- needs 11, given 5 → halted

-- ─────────────────────────────────────────────────────────────────────────────
-- § 13.  MAIN  (run fibonacci results via GHC backend)
-- ─────────────────────────────────────────────────────────────────────────────

open import IO            using (IO; putStrLn; Main; _>>_)
open import Data.Nat.Show using (show)
open import Data.String   using (String; _++_)

showVal : Result ℕ → String
showVal halted          = "?"
showVal (finished v _)  = show v

showResultRow : String → Result ℕ → String
showResultRow label r = label ++ " = " ++ showVal r
                ++ "  [tel remaining: " ++ telLeft r ++ "]"
  where
    telLeft : Result ℕ → String
    telLeft halted          = "exhausted"
    telLeft (finished _ g)  = show g

main : Main
main = IO.run do
  putStrLn "── Object-language fibonacci (§11): syntax → ⟦_⟧ → run ──"
  putStrLn (showResultRow "fibS( 0)" fibS-0)
  putStrLn (showResultRow "fibS( 1)" fibS-1)
  putStrLn (showResultRow "fibS( 5)" fibS-5)
  putStrLn (showResultRow "fibS(10)" fibS-10)
  putStrLn ("Out-of-tel: fibS(10) with tel 5 → " ++ showVal fibS-10-starved)
  putStrLn ""
  putStrLn "── Semantic-domain fibonacci (§12): direct Kleisli ──"
  putStrLn (showResultRow "fib( 0)" fib-0)
  putStrLn (showResultRow "fib( 1)" fib-1)
  putStrLn (showResultRow "fib( 2)" fib-2)
  putStrLn (showResultRow "fib( 3)" fib-3)
  putStrLn (showResultRow "fib( 4)" fib-4)
  putStrLn (showResultRow "fib( 5)" fib-5)
  putStrLn (showResultRow "fib( 6)" fib-6)
  putStrLn (showResultRow "fib( 7)" fib-7)
  putStrLn (showResultRow "fib( 8)" fib-8)
  putStrLn (showResultRow "fib( 9)" fib-9)
  putStrLn (showResultRow "fib(10)" fib-10)
  putStrLn ""
  putStrLn ("Out-of-tel: fib(10) with tel 5 → " ++ showVal fib-10-starved)
