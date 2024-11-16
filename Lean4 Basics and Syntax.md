# Lean4 Basics/Syntax

*Information taken from Haoyuan Luo of Penn State*

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

```python
inductive [name] (a1:[type]) ... (an:[type]) : Sort u where
	| constructor_1 : ... -> [name] a1 ... an
	...
	| constructor_m : ... -> [name] a1 ... a_n
```

`a1, ..., an` should be types instead of terms, and they should be able to be inferred from the input of constructors. The `Sort u` specification of the universe level of this inductive type should be strictly greater than the universe level of constructors. A constructor can construct a term of the inductive type it belongs to. We can use `[name].constructor` to call a constructor. We might also use `[term].constructor` when the `[term]` is of this inductive type and the constructor we are calling takes in a term of this inductive type.

*Example*:

```jsx
inductive myList (A : Type) : Type where
| c1 : (a : A) -> myList A
| c2 : (myList A) -> (a : A) -> myList A 

#check ((myList.c1 4).c2 6).c2 5 -- of type myList Nat
-- constructor c2 appends a into the list
```

Notice how `Nat` is constructed:

```jsx
inductive Nat : Type where
| zero : Nat
| succ : MyNat -> MyNat

#eval Nat.zero -- 0
#eval Nat.zero.succ.succ.succ -- 3
```

Uses two constructors: `zero` and `succ`.

Case distinction comes with these constructors using the `match` syntax, have to give commands for each case which depends on the constructor

```jsx
match [term] with
	| constructor_1 ... => ...
	...
	| constructor_m ... => ...
```

*Examples* of functions using matching for lists in our `MyList` class:

```jsx
def myList.moreThanOne {A: Type}: myList A -> Nat := 
	fun l => 
	match l with
		|.c1 _ => 0
		|.c2 _ _ => 1

-- checks the outermost
#eval ((myList.c1 4).c2 5).moreThanOne -- outputs 1

def myList.last {A : Type} : myList A -> A :=
	fun l => 
	match l with
		|.c1 a => a
		|.c2 a => a
	
def myList.first {A : Type} : myList A -> A :=
	fun l => 
	match l with
		|.c1 a => a
		|.c2 penultimate_l _ => penultimate_l.first -- recursive... Lean checks that this recursion indeed stops. Otherwise requires more proof
```

Lean natively has `List` which can be constructed just with square bracket notations. 

We can use `let [identifier] : [type] := ...` to define local variables for substitutions within a proof. Or even useful outside the tactics mode. 

Likewise, `have [identifier] : [result] := [its proof]`

Can also have more complicated matching, not just the constructors themselves, but something like for Naturals:

```jsx
theorem ...
match a with 
	|.zero => ...
	|.succ .zero => ...
	|.succ (.succ .zero) => ...
	|.succ (.succ (.succ a''')) => ...
```

## Calculations

Start a section of tactics that are like algebraic: `calc` like inequalities, equalities, …

*Example*:

```jsx
goal is (2 + b <= b * b) => by
simp
calc
2 + b <= b + b := by simp [hypothesis]
_ = 1 * b + 1 * b := by simp
_ = _ := by rw [ <- Nat.right_distrib ] -- or, replace these last two lines by _ = _ := by ring
```

The underscores on the left hand side are just placeholders from the right hand side of the previous line. And the underscore on the right hand side of the last line is just a placeholder for the right hand side of the goal. 

## Structures

A variation on inductive types only with one constructor

```jsx
structure [name] [parameter] where
[field1] : ...
[field2] : ...
```

We can define a term of this structure using the anonymous constructor

```jsx
[identifier] : [type] := <field1, ..., fieldn>
```

or

```jsx
{field1 := ..., ..., fieldn := ... : [type]}
```

*Example*

```jsx
structure myGroup (S : Type) where
	mul : S -> S -> S
	e : S
	id : \forall x : S, (mul e x = x) \AND (mul x e = x)
	inv : \forall x : S, _x' : S, (mul x x' = e) \AND (mul x' x = e)
	assoc : \forall x y z : S, mul (mul x y) z = mul x (mul y z)
	
def myG : myGroup Int := \langle
	fun x y => x + y, 0,
	by intro x; simp,
	by intro x; refine' \langle -x, _ \rangle; simp [Int.add_right_neg, Int.add_left_neg], Int.add_assoc \rangle

#print myG
#check myG.assoc
```

## Classes and Instances

Classes are variation of structures. Structures are anonymous. We’d need to declare an instance to use methods (fields of structures)…

## Axioms and sorry

Declare an axiom: `axiom [identifier] : [Type]`, and `sorry` tactic to fill in the proof of any proposition. 

```jsx
namespace wrong
axiom w: 1 + 1 = 3
theorem thw: 5 + 7 = 0: by
	...
```