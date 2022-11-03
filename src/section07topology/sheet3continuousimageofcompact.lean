/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import topology.continuous_function.compact -- continuous functions, compact sets

/-!

# Topology : continuous image of compact is compact

Useful API for this proof:

* `continuous.is_open_preimage` : preimage of open under continuous map is open


-/

-- let X & Y be topological spaces
variables (X Y : Type) [topological_space X] [topological_space Y]

-- let S be a subset of X
variable (S : set X)

-- Let `f : X → Y` be a function
variables (f : X → Y) 

-- If f is continuous and S is compact, then the image f(S) is also compact.
example (hf : continuous f) (hS : is_compact S) : is_compact (f '' S) :=
begin
  -- Figure out the maths proof first, and then see if you can 
  -- formalise it in Lean.
  -- `rw is_compact_iff_finite_subcover at hS ⊢,` might be a good first line
  rw is_compact_iff_finite_subcover at hS ⊢,
  intros ι U Hopen Hcover,
  have Hpreimcover : S ⊆ ⋃ (i : ι), f⁻¹' U i,
  {
    simp only [set.image_subset_iff, set.preimage_Union] at Hcover,
    exact Hcover,
  },
  specialize hS (λ i, f⁻¹' (U i)) (λ (i:ι), (continuous.is_open_preimage hf (U i) (Hopen i))) Hpreimcover,
  cases hS with t Hfinitecover,
  use t,
  simp [Hfinitecover],
end
#check continuous.is_open_preimage

example (n k : ℕ) (hleq: n ≤ k) (hneq: n ≠ k) : (n < k) :=
begin
exact (ne.le_iff_lt hneq).mp hleq,
end

example (n k : ℕ) (hgeq: n ≥ k) (hneq: n ≠ k) : (n > k) :=
(ne.symm hneq).le_iff_lt.mp hgeq

