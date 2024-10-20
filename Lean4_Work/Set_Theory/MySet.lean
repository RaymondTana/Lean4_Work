-- MySet α is a type alias for α → Prop
-- This means any time you have an element a : α, then an object of type : MySet α will return True or False
def MySet (α : Type u) := α → Prop

namespace MySet

-- I.e., Anything of type (MySet α) is a function that represents the characteristic function of a set. Call MySet α a function type, for that reason.

--  Membership predicate (mem a s): shorthand for s a
def mem (a : α) (s : MySet α) : Prop := s a
-- Infix membership (a ∈ s) : shorthand for s a
infix:50 " ∈ " => mem -- 50 refers to the precedence, order of operations

-- Empty set
def empty : MySet α := λ _ => False

-- Universal set
def univ : MySet α := λ _ => True

-- Union
def union (s t : MySet α) : MySet α := λ a => s a ∨ t a
infix:65 " ∪ " => union

-- Intersection
def inter (s t : MySet α) : MySet α := λ a => s a ∧ t a
infix:70 " ∩ " => inter

-- Complement
def compl (s : MySet α) : MySet α := λ a => ¬ s a
prefix:75 " ᶜ" => compl

end MySet
