/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import section14polynomials.sheet02noetherian

/-!

# An auxiliary construction

I haven't talked about which proof of the Hilbert Basis Theorem we'll
be formalising, so let me say a bit about this here. The theorem
states that if `R` is a Noetherian (commutative) ring then so is
the polynomial ring `R[X]`. So, given an ideal `I` of `R[X]` we need
to come up with a finite set of generators, and the only tool we have
is that any ideal of `R` has a finite set of generators. So, however
this proof goes, we are going to probably be wanting to construct
ideals of `R` given an ideal of `R[X]`. 

The `aux_ideal` construction is of this nature. An ideal of `R[X]`
is by definition an `R[X]`-submodule of `R[X]` so it's also
an `R`-submodule of `R[X]` (this is a bit like saying that a complex
vector space is obviously also a real vector space). The `lcoeff`
maps, taking a polynomial to its coefficient of `X^n`,  are `R`-linear
maps from `R[X]` to `R`, so we can push `R`-submodules of `R[X]` along
these maps (i.e. look at their images) to get `R`-submodules of `R`,
which is the same thing as ideals of `R`. The submodules we will push
forward are the following: given an ideal `I` of `R[X]`, and a natural
number `n`, we will consider `I` as an `R`-submodule of `R[X]`, we will
intersect it with `M R n` (the `R`-submodule of polynomials of degree
at most `n`), and we will then look at its image under `lcoeff R n`.
By definition then, the elements of `aux_ideal I n` will be the
coeficients of `X^n` of the polynomials in `I` which have degree
at most `n`, and this abstract way of describing this set shows that
it is an ideal of `R`.

Again, more briefly: if `I` is an ideal of `R[X]` and `n` is a natural,
then `aux_ideal I n` is the ideal of `R` consisting of the coefficients
of `X^n` of the elements of `I` with `nat_degree` at most `n`. 

The first result we are aiming for in this file is that
`aux_ideal I n` is monotone as a function of `n`, that is, if `n ≤ m`
then `aux_ideal I n ≤ aux_ideal I m`.

-/

variables {R : Type} [comm_ring R] (I : ideal (polynomial R))

open polynomial

/-

`I.restrict_scalars R` means the ideal `I`, regarded as an `R`-submodule
of `R[X]`. The `⊓` is just intersection of submodules. The `map`
is `submodule.map` which is the function which eats a linear map
(in this case `lcoeff R n`) and outputs a function sending submodules
of the domain of the map to submodules of the codomain; the function
itself is just "image of the submodule under the linear map".

-/

/-- If `I` is an ideal of `polynomial R` then `aux_ideal I n` is the ideal of `R`
obtained by pushing forward `I ∩ {polynomials of degree ≤ n}` along the linear map `lcoeff n`
sending a polynomial to its coefficient of `X^n`. 

One can imagine `aux_ideal I n` as the ideal consisting of `0` and the coefficient of `X^n`
in all of the degree `n` polynomials in `I`, but this case split definition is harder
to work with in practice. -/
noncomputable def aux_ideal (n : ℕ) :=
(I.restrict_scalars R ⊓ M R n).map (lcoeff R n)

namespace aux_ideal

/-

We're going to prove that `aux_ideal I n` is monotone for fixed `I`, i.e. it gets 
bigger as `n` gets bigger. 

Make sure you know a maths proof before embarking on this.

Useful API: 

`I.mul_mem_right r : p ∈ I → p * r ∈ I`
`polynomial.nat_degree_mul_le : (p * q).nat_degree ≤ p.nat_degree + q.nat_degree`
`p.coeff_mul_X : (n : ℕ), (p * X).coeff (n + 1) = p.coeff n`

and note that `lcoeff R n f` is definitionally `f.coeff n`.

-/

noncomputable def poly {n : ℕ} {J : ideal (polynomial R)} {r : R} (h : r ∈ (aux_ideal J n) ) : polynomial R :=
h.some

lemma coeff_poly {n : ℕ} {J : ideal (polynomial R)} {r : R} (h : r ∈ (aux_ideal J n) ) : (poly h ∈ ((J.restrict_scalars R ⊓ M R n) : set (polynomial R))) ∧ (lcoeff R n (poly h) = r) := 
h.some_spec

lemma mono_aux (n : ℕ) :
  aux_ideal I n ≤ aux_ideal I (n + 1) :=
begin
  intros r h,
  have hp := coeff_poly h,
  use ((poly h) * X),
  split,
  {
    split,
    {
      apply I.mul_mem_right X,
      exact hp.left.left,
    },
    {
      refine le_trans (nat_degree_mul_le) _,
      exact add_le_add hp.left.right nat_degree_X_le,
    },
  },
  {
    dsimp,
    rw coeff_mul_X (poly h) n,
    exact hp.right,
  },
end

#check coeff_mul_X

-- this is now a one-liner
lemma mono : monotone (aux_ideal I) :=
begin
  exact monotone_nat_of_le_succ (mono_aux I),
end

/- Given an ideal `I` and a natural number `n`, we have been
considering the map from `I ∩ {degree ≤ n}` to `R` defined by
"take coefficient of `X^n`". The `lift` function below is
a one-sided inverse to this map. Given an element of `R`,
if it's in the image then we send it to a random preimage
in `I ∩ (degree ≤ n)` and if it's not then we just send it to 0.
Note the use of `exists.some`; the statement "I am in the image"
is definitionally equal to "there exists something in the domain
which maps to me", and `exists.some` chooses a random thing in the
image with this property.

-/

noncomputable def lift (n : ℕ) (r : R) [decidable (r ∈ aux_ideal I n)] : polynomial R :=
if hr : r ∈ aux_ideal I n then (submodule.mem_map.1 hr).some else 0

variables {n : ℕ} {r : R} [decidable (r ∈ aux_ideal I n)]

lemma lift_def (n : ℕ) (r : R) [decidable (r ∈ aux_ideal I n)] : 
lift I n r = if hr : r ∈ aux_ideal I n then (submodule.mem_map.1 hr).some else 0 :=
begin
  refl,
end

variable {I}

-- you can use `dif_neg` to prove this lemma.
lemma lift_eq_zero_of_ne (hr : ¬ r ∈ aux_ideal I n) : lift I n r = 0 :=
begin
  apply dif_neg,
  exact hr,
end

-- you need to do a case split for this one. The definition of `lift`
-- used ` (submodule.mem_map.1 hr).some` so this proof will need
-- ` (submodule.mem_map.1 hr).some_spec` somewhere. Note also `dif_pos` :-)
lemma lift_mem :
  (lift I n r) ∈ submodule.restrict_scalars R I ⊓ M R n :=
begin
  rw lift_def,
  split_ifs with hr,
  exact (submodule.mem_map.1 hr).some_spec.left,
  exact (submodule.restrict_scalars R I ⊓ M R n).zero_mem,
end

-- this is a one-liner
lemma lift_mem_I : lift I n r ∈ I :=
begin
  -- rw lift_def,
  -- split_ifs with hr,
  -- exact (submodule.mem_map.1 hr).some_spec.left.left,
  -- exact I.zero_mem,
  exact lift_mem.left,
end

-- this is a one-liner too (thanks to definitional equality abuse)
lemma lift_nat_degree_le :
  (lift I n r).nat_degree ≤ n :=
begin
  exact lift_mem.right,
end

lemma lift_spec (hr : r ∈ aux_ideal I n) :
  lcoeff R n (lift I n r) = r :=
begin
  rw lift_def,
  split_ifs,
  exact (submodule.mem_map.1 hr).some_spec.right,
end

end aux_ideal
