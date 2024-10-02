# Lean4 Work

I use this repository to compile my results written in `Lean4`. 

So far, I have solved all of Kevin Buzzards Maths Challenges. More to come!

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