# Telomare — Agda Specification

A denotational specification of Telomare's semantics in Agda, following
Conal Elliott's **Denotational Design** and **Type Class Morphisms** methodology.

---

## The central idea

Every Telomare computation has a **telomere** — a natural number that strictly
decreases on every recursive call. When it reaches zero the program halts
gracefully. This single design decision gives three things for free:

- **Totality** — all programs terminate, by construction
- **Time bound** — steps taken ≤ initial tel
- **Space bound** — call depth ≤ initial tel, so space = O(tel)

---

## Denotational Design (Elliott's methodology)

Denotational Design (Conal Elliott, ICFP 2009) says:

> Choose a mathematical model for your types first.
> Derive every operation as a homomorphism with respect to that model.
> Laws come for free; abstraction leaks become detectable failures.

The methodology has four steps:

1. **Pick a semantic model** — assign a precise mathematical meaning to every
   type before writing any implementation.
2. **Specify operations as homomorphisms** — require that the meaning function
   commutes with every operation: `⟦f a⟧ = f' ⟦a⟧`.
3. **Calculate implementations** — the homomorphism equations often determine
   the implementation uniquely. No guessing.
4. **Laws are inherited** — if the model satisfies a law (e.g. monad
   associativity), every derived instance satisfies it too.

### Applied to Telomare

**Step 1 — the model.** The meaning of a computation returning type `A` is:

```
⟦ e : A ⟧  :  Tel → Maybe (A × Tel)      where Tel = ℕ
```

- Input `Tel`: the telomere available at the start.
- Output `just (v, g')`: succeeded, produced `v`, `g'` tel remains.
- Output `nothing`: telomere exhausted — graceful halt.

This is `StateT Tel Maybe`, a standard mathematical object.  We name it `TelM`:

```agda
TelM : Set → Set
TelM A = Tel → Maybe (A × Tel)
```

**Step 2–3 — derive the operations.**
Asking "what must `return` and `bind` be so that `⟦·⟧` is a monad
homomorphism?" yields the only possible answers:

```agda
return-tel a g   = just (a , g)              -- 0 tel consumed
bind-tel m f g   = m g >>= λ (a, g') → f a g'  -- thread tel through
step m zero      = nothing                   -- telomere exhausted
step m (suc g)   = m g                       -- consume 1, continue
```

None of these were invented — they were *calculated* from the model.

### Where the homomorphism requirement appears in the code

The equation `⟦f a⟧ = f' ⟦a⟧` shows up in three places, at different levels
of explicitness:

**§2 — implicitly, through derivation.**
`return-tel` and `bind-tel` are the unique solutions to the homomorphism
equations for the `Monad` structure.  The requirement is:

```
⟦ return a ⟧  =  return-tel ⟦a⟧
⟦ m >>= f  ⟧  =  ⟦m⟧ >>= (⟦·⟧ ∘ f)
```

Solving for what `return` and `>>=` must be on `TelM` forces exactly the
definitions written.  Any other definition would violate the equation.

**§3 — explicitly in the type denotation.**

```agda
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → TelM ⟦ B ⟧T
```

This line *is* a homomorphism equation for the function type constructor `⇒`:

```
⟦ A ⇒ B ⟧  =  ⟦A⟧ →K ⟦B⟧
```

Writing `⟦ A ⇒ B ⟧T = ⟦A⟧T → ⟦B⟧T` (a plain function) would violate the
homomorphism — function application would not commute with `⟦·⟧` because tel
consumption would be lost.

**§8 — explicitly proved as Agda propositions.**

```agda
left-id  : (idK ∘K f) a t ≡ f a t
right-id : (f ∘K idK) a t ≡ f a t
```

These are the Kleisli category laws written as literal `≡` propositions.
Both proofs proceed by case analysis on `f a t` and then `refl` in each case —
the equations hold *definitionally* within each branch.

**Summary table:**

| Location | Operation | Homomorphism equation |
|---|---|---|
| §2 | `return` | `⟦ return a ⟧ t = just (a, t)` |
| §2 | `bind` | `⟦ m >>= f ⟧ = ⟦m⟧ >>= ⟦f⟧` with tel threading |
| §3 | `⇒` type | `⟦ A ⇒ B ⟧ = ⟦A⟧ →K ⟦B⟧` |
| §8 | `id` (left) | `⟦ id ∘ f ⟧ ≡ idK ∘K ⟦f⟧` |
| §8 | `id` (right) | `⟦ f ∘ id ⟧ ≡ ⟦f⟧ ∘K idK` |

§2 and §3 are where the **derivation** happens (calculate what operations must
be); §8 is where the **verification** happens (prove the equations hold).

**Step 4 — laws for free.**
Monad laws (left/right identity, associativity) hold on `TelM` because they
hold on `StateT Tel Maybe`.  The Kleisli category laws are proved in §8, and
the full lawful category instance (including associativity and congruence) is
assembled in §9f.

---

## The Kleisli Category

Once `TelM` is chosen as the semantic domain, a category of programs falls
out automatically — the **Kleisli category of `TelM`**.

| Component | Definition |
|---|---|
| **Objects** | Agda `Set`s (denotations of Telomare types) |
| **Morphisms** `A →K B` | `A → TelM B` = `A → Tel → Maybe (B × Tel)` |
| **Identity** `idK` | `return-tel` — zero tel, passes everything through |
| **Composition** `g ∘K f` | run `f`, thread remaining tel into `g` |
| **Pairing** `forkK f g` | run `f` then `g` on same input, costs add sequentially |
| **Projections** `exlK`, `exrK` | extract from pair, zero tel |

This category is **Cartesian** (has products).  `fixT` adds a feedback
operator on top: the tel is the trace resource that bounds the feedback depth.

### The category is the denotational design

These are not two separate things.  The category is the semantic model given
its full algebraic structure:

- **Objects** are denotations of types.
- **Morphisms** are denotations of programs.
- The **TCM** (**Type Class Morphism**) **principle** (homomorphism requirement)
  is exactly the **functor condition**: `⟦·⟧` is a functor from the syntactic
  category of programs to the Kleisli category of `TelM`.
  A TCM is a function `h : A → B` that is a homomorphism for a given type
  class — the class structure on `A` corresponds to the class structure on `B`
  via `h`.  Here `h = ⟦·⟧`.

```
⟦ id ⟧       = idK          -- identity preserved
⟦ g ∘ f ⟧    = ⟦g⟧ ∘K ⟦f⟧  -- composition preserved
⟦ fork f g ⟧ = forkK ⟦f⟧ ⟦g⟧
```

Each equation says the denotation doesn't leak — meaning of a composition
equals composition of meanings.  This is compositional semantics, and the
category is what makes compositionality precise.

---

## Type Class Morphisms (TCM principle)

Elliott's TCM principle states:

> *"The instance's meaning follows the meaning's instance."*

A function `h : A → B` is a **type class morphism** for class `C` if it is a
homomorphism — i.e. the `C` structure on `A` corresponds to the `C` structure
on `B` via `h`.

For `Monad`:
```
h (return a)  = return (h a)
h (m >>= f)   = h m >>= (h ∘ f)
```

In our spec `h = ⟦·⟧` and the monad on the left is Telomare's operational
sequencing; on the right is `TelM`'s `bind-tel`.  A violation of this
equation would be an **abstraction leak**: the implementation's behaviour
would diverge from the model, making equational reasoning unsound.

---

## Types and their denotations

```agda
⟦ unit  ⟧T = ⊤
⟦ bool  ⟧T = Bool
⟦ nat   ⟧T = ℕ
⟦ A ⊗ B ⟧T = ⟦A⟧T × ⟦B⟧T
⟦ A ⊕ B ⟧T = ⟦A⟧T ⊎ ⟦B⟧T
⟦ A ⇒ B ⟧T = ⟦A⟧T → TelM ⟦B⟧T   -- functions live in TelM
```

The critical line is the last one: a function type `A ⇒ B` does **not**
denote a plain function `⟦A⟧T → ⟦B⟧T`.  It denotes a **morphism** in the
Kleisli category.  Applying a function is a computational event that consumes
tel.  This is where the telomere enters the type system.

---

## Recursion and totality

### `fixT` — the only recursion primitive

```agda
private
  fixT-aux : {S R : Set} → Tel → ((S →K R) → S →K R) → S →K R
  fixT-aux zero    _    _ _ = nothing
  fixT-aux (suc f) body s   = step (body (fixT-aux f body) s)

fixT body s g = fixT-aux g body s g
```

Every unfolding calls `step`, consuming 1 tel.  Agda accepts this via the
**fuel pattern**: `fixT-aux` recurses structurally on its first `Tel`
argument (the fuel), which decreases by 1 on every call.  The fuel is tied to
the computational tel so the bound is tight.

There is also `fix` (§5), the special case where input and output types are
the same (`S = R`), which does not call `step` internally — the body is
expected to include its own `step` calls.

### Totality theorem

`TelM A = Tel → Maybe (A × Tel)` is a **total** Agda function.  There is no
`⊥`, no coinduction, no partiality at the meta-level.  The only "failure" is
`nothing`, a legitimate mathematical value meaning "tel ran out".  This holds
by construction — no proof needed beyond the type.

### Complexity bounds

For a computation run with initial tel `g₀`:

```
tel consumed  =  number of `step` calls  ≤  g₀
call depth    ≤  g₀
space         =  O(g₀ × frame size)
```

These bounds are read directly from the initial tel — no separate complexity
analysis required.

---

## Limited recursion: `{x, y, z}` in Telomare

Telomare's surface syntax for recursion is:

```
{ x , y , z } v
```

where:
- `x` — test: if truthy, keep recursing; if falsy, take the base case
- `y` — body: receives `recur` (the recursive continuation) explicitly
- `z` — base: the answer returned when `x` fails

Unfolding:
```
{ x , y , z } v  =  if x(v)  then  y (fix {...}) v
                               else  z v
```

This is **not a new primitive**.  It is `fixT` with a guard.  In the Agda
code, this pattern is expressed directly using `fixT` with an inline
conditional rather than a separate combinator:

```agda
fixT (λ recur s →
  if test s then body recur s
            else base s)
```

### Examples from the Telomare standard library

```
-- d2c (data-to-Church numeral)
d2c = \n f b -> { id
                , \recur i -> f (recur (left i))
                , \i -> b
                } n

-- gcd (Euclidean algorithm)
gcd = \a b -> { \p -> not (dEqual (right p) 0)
              , \recur p -> recur (right p, dMod (left p) (right p))
              , \p -> left p
              } (a, b)

-- map over a linked list
map = \f -> { id
            , \recur l -> (f (left l), recur (right l))
            , \l -> 0
            }
```

In each case:
- The test `x` tells the telomere whether to keep unwinding.
- Each recursive call costs 1 tel (via `fixT-aux`'s `step`).
- The tel consumed equals the number of successful test evaluations.

---

## Fibonacci: two implementations

The Agda file contains two fibonacci implementations that compute the same
values, demonstrating the full pipeline at different levels.

### §11 — Object-language fibonacci (syntax → ⟦\_⟧ → run)

Written entirely in the syntax category `_⇨S_` using point-free categorical
combinators, then denoted into the Kleisli category via `⟦_⟧` and executed.
This is the full pipeline:

```
syntax term  ─⟦_⟧─▸  Kleisli morphism  ─run─▸  Result
```

The code defines `fibS : nat ⇨S nat` as a composition of `fixTS` with an
initial-state setup morphism.  The point-free style is verbose — this is
exactly what "Compiling to Categories" (Elliott, ICFP 2017) automates away.

### §12 — Semantic-domain fibonacci (direct Kleisli)

The same computation written directly as a Kleisli morphism, bypassing the
syntax category.  Much shorter, but without the machine-checked homomorphism:

```agda
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
```

This is the `{x, y, z}` limited-recursion pattern expressed directly with
`fixT` and an inline conditional.

### Output

Running with `tel = n + 2` (one spare):

```
fib( 0) = 0   [tel remaining: 1]
fib( 1) = 1   [tel remaining: 1]
fib( 2) = 1   [tel remaining: 1]
fib( 3) = 2   [tel remaining: 1]
fib( 4) = 3   [tel remaining: 1]
fib( 5) = 5   [tel remaining: 1]
fib( 6) = 8   [tel remaining: 1]
fib( 7) = 13  [tel remaining: 1]
fib( 8) = 21  [tel remaining: 1]
fib( 9) = 34  [tel remaining: 1]
fib(10) = 55  [tel remaining: 1]

Out-of-tel: fib(10) with tel 5 → ?
```

Tel consumed = `n + 1` exactly.  The telomere is a tight bound, not a loose one.

---

## Felix integration

[Felix](https://github.com/conal/felix) is Conal Elliott's Agda library for
categorical denotational design.  It provides the modules that `telomare.agda`
imports:

| Module | What it contributes |
|---|---|
| `Felix.Object` | `Products` / `Coproducts` type-class interfaces |
| `Felix.Equiv` | `Equivalent` — setoid-based morphism equality |
| `Felix.Raw` | `Category` (raw) — `id` and `_∘_` without laws |
| `Felix.Laws` | `Category` (lawful) — identity and associativity laws |
| `Felix.Homomorphism` | `CategoryH` — functors between lawful categories |

### What Felix guarantees

Felix's `CategoryH` record bundles three machine-checked obligations:

```agda
record CategoryH (src tgt : Cat) where
  field
    F-cong : f ≈ g  →  Fₘ f ≈ Fₘ g     -- preserves equivalence
    F-id   : Fₘ id  ≈  id               -- preserves identity
    F-∘    : Fₘ (g ∘ f) ≈ Fₘ g ∘ Fₘ f  -- preserves composition
```

Filling `⟦⟧-CategoryH` (§10g) makes the **TCM equations machine-checked**:
Agda will reject any denotation function `⟦_⟧` that fails to be a functor
from the syntax category `_⇨S_` into the Kleisli category `_→K_`.

### Why this matters

Without Felix a proof obligation like `⟦ g ∘S f ⟧ = ⟦g⟧ ∘K ⟦f⟧` would be an
informal convention.  With `CategoryH` it is a **type error** to violate it.
Concretely:

- `F-∘` holding by `refl` (§10g) means compositionality is **definitional**,
  not just propositional — no proof term is needed.
- `F-id` holding by `refl` means the identity axiom is also definitional.
- `F-cong` (the inductive proof in `⟦⟧-cong`, §10f) ensures the denotation
  respects the equational theory of the syntax category, closing the
  abstraction under rewriting.

---

## File structure (`telomare.agda`)

| Section | Content |
|---|---|
| §1 | Semantic model — `Tel`, `TelM` |
| §2 | Monad operations — `return-tel`, `bind-tel`, `step` |
| §3 | Object language types and their denotations `⟦_⟧T` |
| §4 | Kleisli category — `→K`, `idK`, `∘K`, `forkK`, `exlK`, `exrK` |
| §5 | Recursion primitives — `fix`, `fixT` (fuel pattern) |
| §6 | Complexity bounds |
| §7 | Totality — `run`, `Result` |
| §8 | Kleisli category laws — `left-id`, `right-id` |
| §9 | Felix integration — `→K-Equiv`, `→K-RawCat`, `→K-RawCart`, `→K-LawCat` |
| §10 | Denotation homomorphism — `_⇨S_`, `_≈S_`, `⟦_⟧`, `⟦⟧-CategoryH` |
| §11 | Object-language fibonacci — `fibS` (syntax → `⟦_⟧` → run) |
| §12 | Semantic-domain fibonacci — `fib` (direct Kleisli) |
| §13 | `main` — IO runner |

---

## Key references

- Conal Elliott, *Denotational Design with Type Class Morphisms*, Haskell
  Symposium 2009
- Conal Elliott, *Compiling to Categories*, ICFP 2017
- Conal Elliott, *The Simple Essence of Automatic Differentiation*, ICFP 2018
- Conal Elliott, *Generalized Convolution and Efficient Language Recognition*,
  arXiv 1903.10677
