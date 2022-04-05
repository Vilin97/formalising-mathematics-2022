/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal. 

## Tactics 

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : A ∪ A = A :=
begin
  ext,
  split,
  intro h,
  cases h with h1 h2,
  exact h1,
  exact h2,

  intro h,
  left,
  exact h,
end

example : A ∩ A = A :=
begin
  ext,
  split,
  intro h,
  cases h with h1 h2,
  exact h1,

  intro h,
  split,
  exact h,
  exact h,
end

example : A ∩ ∅ = ∅ :=
begin
  ext,
  split,
  intro h,
  cases h with h1 h2,
  exact h2,

  intro h,
  exfalso,
  exact h,
end

example : A ∪ univ = univ :=
begin
  ext,
  split,
  intro h,
  cases h with h1 h2,
  simp,
  exact h2,

  intro h,
  right,
  exact h,
end

example : A ⊆ B → B ⊆ A → A = B :=
begin
  intros h1 h2,
  ext,
  split,
  intro h,
  exact h1 h,
  intro h,
  exact h2 h,
end

example : A ∩ B = B ∩ A :=
begin
  exact inf_comm,
end

example : A ∩ (B ∩ C) = (A ∩ B) ∩ C :=
begin
  symmetry,
  exact inf_assoc,
end

example : A ∪ (B ∪ C) = (A ∪ B) ∪ C :=
begin
  symmetry,
  exact sup_assoc,
end

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
begin
  exact union_distrib_left A B C,
end

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  exact inter_distrib_left A B C,
end

