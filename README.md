# Lean4 Work

I use this repository to compile my results written in `Lean4`. 

So far, I have solved all of Kevin Buzzards Maths Challenges and the Natural Number Game. More to come!

# Converting Lean3 to Lean4 Code

There are some challenges in converting `Lean3` code to `Lean4` code. I outline some of those lessons I've learned doing this.


## Imports
`Lean4` imports/libraries are camel-case and start with an upper-case letter; whereas `Lean3` seems to be snake-case and all lower-case. Moreover, the organization of theorems and definitions in Mathlib4 may be different than it was in Mathlib3. So you may have to go searching to find the packages you're looking for. 

### Example: Xena Challenge 3

For instance, let's look at Challenge 3, whose solution only requires the import `import data.real.basic`.

We can derive the corresponding import for `Lean4` by appending `Mathlib` onto the front and capitalizing the first letter of each directory name: `import Mathlib.Data.Real.Basic`

### Example: Xena Challenge 5

The imports for Challenge 5 seem a bit messed up. They initially read: `import data.finset algebra.big_operators tactic.ring`, but should have read:

```
import data.finset.basic  algebra.big_operators.ring tactic.ring
```

Adding spaces between the paths in `Lean3` is like importing three different libraries at different paths. A bit more cleanly, it'd be written:

```
import data.finset.basic  
import algebra.big_operators.ring 
import tactic.ring
```

We could achieve the same in `Lean4` as follows:

```
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic.Ring
```

Notice that I have to prepend by `Mathlib`, some capitalization was added, and some notation switched from snake case to camel case.

## Begin-End Blocks
Any time you see `begin`-`end` blocks in `Lean3`, remove them and just write `by` at the beginning to get something suitable for `Lean4`. 

## Tactics and Notation
Some proofs you may read in `Lean3` just don't work well in `Lean4`. They may have the right idea but need small syntactic adjusting. For some others, I have not found quick replacements that give me the same behavior, so I've needed to invent a new proof method. Certain commands like `simp`, `change`, `apply`, `rw`, `norm_num`, and `rfl` seem to have changed in their behavior to varying degrees. In particular, I had to *import* `norm_num` myself despite it seeming native in `Lean3`. The extra import used `import Mathlib.Tactic.NormNum`.

In particular, one should use the bracketed notation `rw [...]` for the `rewrite` tactic, as well as the spaced-out notation `f a` or `f (a)` when applying a function or tactic `f` to input `a`.

## Setup
There exists a [Lean4 online editor](https://live.lean-lang.org/). One may also set up a new project in VSCode that uses `Mathlib4`. 

## Official Instructions

This is advice taken from the official \[mathlib4](https://github.com/leanprover-community/mathlib4/blob/master/README.md) community. For users familiar with `Lean3` who want to get up to speed in `Lean4` and migrate their existing
`Lean3` code, there is:

- A [survival guide](https://github.com/leanprover-community/mathlib4/wiki/Lean-4-survival-guide-for-Lean-3-users)
  for `Lean3` users
- [Instructions to run `mathport`](https://github.com/leanprover-community/mathport#running-on-a-project-other-than-mathlib)
  on a project other than mathlib. `mathport` is the tool the community used to port the entirety
  of `mathlib` from `Lean3` to `Lean4`.

# Introduction to Lean

*Information taken from Haoyuan Luo at Penn State University*

## As a Programming Language

Define a new term: `def [identifier] [context] : [type] :=` 

Write a function: `def f : Nat -> Nat := fun x1 … xn ⇒ …` 

Check expressions for type: `#check` 

Evaluate command: `#eval`

Notation for functions: $\texttt{Nat} \rightarrow \texttt{Nat} \rightarrow \texttt{Nat}$, which equals $\texttt{Nat} \rightarrow (\texttt{Nat} \rightarrow \texttt{Nat})$ is a function with two arguments. Alternatively: `def g' (n: Nat) : Nat -> Nat := fun x => x + n` is equivalent to `def g : Nat -> Nat -> Nat := fun x y => x + y` 

## Theorem Proving

Each proposition is actually a type. And to prove a proposition is to construct a term of this type. 

`theorem` is just another name for `def`

*Example*: to prove a theorem of the form `theorem thm : \forall a : Nat, \exists b , b > a + 1 := ...`, we need to construct a pair `<b, proof>` where `b` is the number for a given `a` and `proof` is a proof that `b > a + 1`.

Alternatively casted as `thm' : (a : Nat) -> (\exists b, b > a + 1) := ...`. Has same form as previous written version. That means `thm` and `thm1` are the same type.

One valid proof would be `:= fun a => \lang a + 2, by simp \rang`. This is very by-hand. Alternatively, and more commonly, we use tactics after the `by` command. But that complicates the readability of proofs. 

# Dependent Types

These are functions or pairs where the type of later variables can depend on the previous ones. 

`(a : Nat) -> (a > 0)`: proposition that for all natural numbers `a`, it holds that `a > 0`

`(b : Nat) \cross (b > 0)`: proposition that there exists a natural number `b` such that `b > 0` 

This second one is “forbidden”, we usually write `\exists b, b > 0`. Only use the $\times$ symbol when the type of the last variable is a proposition.

We may leave `_` in expressions to ask Lean to fill in this hole automatically.

`{A : Type}` asks Lean to infer `A` automatically, so `Type` is sort of a *universal type*.

Example: `def term1 : (A : Type) -> (A -> A) := fun _ a => a`

vs. `def term1' : {A : Type} -> (A -> A) := fun a => a` both return the identity function. This is an example of a dependent type.

`\<...\>` is the *anonymous constructor*. 

## Variable Declarations and Namespaces

Keyword `variable` to declare variables without defining them

`variable (a1 : Type1) ... (an : Typen)` 

This declaration is valid inside a namespace:

`namespace [name]`

Inside a namespace, declared variables can be used directly in definitions and proofs. To call definitions inside a namespace, write: `[namespace].[identifier]`. 

And if you call a definition inside a namespace, the variables declared inside this namespace that are used by this definition will be automatically added to this definition as context. 

You can end a namespace is `end [name]`. 

## Type system in Lean

The type system has a hierarchy: `Type n` is said to have universe level `n`. A dependent type `(t1 : Type u1) -> ... -> (tn : Type un)` typically has `Type max{u1 + 1, ..., un + 1}`. However, if `tn` is of type `Prop`, the whole dependent type will be of type `Prop`. So propositions are like the “privileged” type in Lean.

`Prop : Type : Type 1 : Type 2 : ...`. Really, these are called `Sort 0`, `Sort 1`, … Read this as `Type` is of type `Type 1`, etc.

`Type _` (or `Type*`) is used to avoid giving an arbitrary universe a name

The default “type”? Real numbers are always `Type` or `Sort 1`. 

## Inductive Types

All user defined types in Lean are inductive types. We can construct inductive types using the syntax:

```
inductive [name] (a1:[type]) ... (an:[type]) : Sort u where
	| constructor_1 : ... -> [name] a1 ... an
	...
	| constructor_m : ... -> [name] a1 ... a_n
```

`a1, ..., an` should be types instead of terms, and they should be able to be inferred from the input of constructors. The `Sort u` specification of the universe level of this inductive type should be strictly greater than the universe level of constructors. A constructor can construct a term of the inductive type it belongs to. We can use `[name].constructor` to call a constructor. We might also use `[term].constructor` when the `[term]` is of this inductive type and the constructor we are calling takes in a term of this inductive type.

Example:

```jsx
inductive myList (A : Type) : Type where
| c1 : (a : A) -> myList A
| c2 : (myList A) -> (a : A) -> myList A 

#check ((myList.c1 4).c2 6).c2 5 -- of type myList Nat
-- constructor c2 appends a into the list
```

Notice how `Nat` is constructed:

```
inductive Nat : Type where
| zero : Nat
| succ : MyNat -> MyNat

#eval Nat.zero -- 0
#eval Nat.zero.succ.succ.succ -- 3
```

Uses two constructors: `zero` and `succ`.