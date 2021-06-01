/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson, Jalex Stark.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.matrix
import Mathlib.data.rel
import Mathlib.combinatorics.simple_graph.basic
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Adjacency Matrices

This module defines the adjacency matrix of a graph, and provides theorems connecting graph
properties to computational properties of the matrix.

## Main definitions

* `adj_matrix` is the adjacency matrix of a `simple_graph` with coefficients in a given semiring.

-/

namespace simple_graph


/-- `adj_matrix G R` is the matrix `A` such that `A i j = (1 : R)` if `i` and `j` are
  adjacent in the simple graph `G`, and otherwise `A i j = 0`. -/
def adj_matrix {α : Type u} [fintype α] (R : Type v) [semiring R] (G : simple_graph α)
    [DecidableRel (adj G)] : matrix α α R :=
  sorry

@[simp] theorem adj_matrix_apply {α : Type u} [fintype α] {R : Type v} [semiring R]
    (G : simple_graph α) [DecidableRel (adj G)] (v : α) (w : α) :
    adj_matrix R G v w = ite (adj G v w) 1 0 :=
  rfl

@[simp] theorem transpose_adj_matrix {α : Type u} [fintype α] {R : Type v} [semiring R]
    (G : simple_graph α) [DecidableRel (adj G)] :
    matrix.transpose (adj_matrix R G) = adj_matrix R G :=
  sorry

@[simp] theorem adj_matrix_dot_product {α : Type u} [fintype α] {R : Type v} [semiring R]
    (G : simple_graph α) [DecidableRel (adj G)] (v : α) (vec : α → R) :
    matrix.dot_product (adj_matrix R G v) vec =
        finset.sum (neighbor_finset G v) fun (u : α) => vec u :=
  sorry

@[simp] theorem dot_product_adj_matrix {α : Type u} [fintype α] {R : Type v} [semiring R]
    (G : simple_graph α) [DecidableRel (adj G)] (v : α) (vec : α → R) :
    matrix.dot_product vec (adj_matrix R G v) =
        finset.sum (neighbor_finset G v) fun (u : α) => vec u :=
  sorry

@[simp] theorem adj_matrix_mul_vec_apply {α : Type u} [fintype α] {R : Type v} [semiring R]
    (G : simple_graph α) [DecidableRel (adj G)] (v : α) (vec : α → R) :
    matrix.mul_vec (adj_matrix R G) vec v = finset.sum (neighbor_finset G v) fun (u : α) => vec u :=
  sorry

@[simp] theorem adj_matrix_vec_mul_apply {α : Type u} [fintype α] {R : Type v} [semiring R]
    (G : simple_graph α) [DecidableRel (adj G)] (v : α) (vec : α → R) :
    matrix.vec_mul vec (adj_matrix R G) v = finset.sum (neighbor_finset G v) fun (u : α) => vec u :=
  sorry

@[simp] theorem adj_matrix_mul_apply {α : Type u} [fintype α] {R : Type v} [semiring R]
    (G : simple_graph α) [DecidableRel (adj G)] (M : matrix α α R) (v : α) (w : α) :
    matrix.mul (adj_matrix R G) M v w = finset.sum (neighbor_finset G v) fun (u : α) => M u w :=
  sorry

@[simp] theorem mul_adj_matrix_apply {α : Type u} [fintype α] {R : Type v} [semiring R]
    (G : simple_graph α) [DecidableRel (adj G)] (M : matrix α α R) (v : α) (w : α) :
    matrix.mul M (adj_matrix R G) v w = finset.sum (neighbor_finset G w) fun (u : α) => M v u :=
  sorry

theorem trace_adj_matrix {α : Type u} [fintype α] (R : Type v) [semiring R] (G : simple_graph α)
    [DecidableRel (adj G)] : coe_fn (matrix.trace α R R) (adj_matrix R G) = 0 :=
  sorry

theorem adj_matrix_mul_self_apply_self {α : Type u} [fintype α] {R : Type v} [semiring R]
    (G : simple_graph α) [DecidableRel (adj G)] (i : α) :
    matrix.mul (adj_matrix R G) (adj_matrix R G) i i = ↑(degree G i) :=
  sorry

@[simp] theorem adj_matrix_mul_vec_const_apply {α : Type u} [fintype α] {R : Type v} [semiring R]
    {G : simple_graph α} [DecidableRel (adj G)] {r : R} {v : α} :
    matrix.mul_vec (adj_matrix R G) (function.const α r) v = ↑(degree G v) * r :=
  sorry

theorem adj_matrix_mul_vec_const_apply_of_regular {α : Type u} [fintype α] {R : Type v} [semiring R]
    {G : simple_graph α} [DecidableRel (adj G)] {d : ℕ} {r : R} (hd : is_regular_of_degree G d)
    {v : α} : matrix.mul_vec (adj_matrix R G) (function.const α r) v = ↑d * r :=
  sorry

end Mathlib