(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * Memory.v : Abstract memory module *)


Set Implicit Arguments.

Require Import Relations.
Require Export Variables.


Module Type MEM (UT:UTYPE) (T:TYPE UT) (Var:VAR UT T).

 Parameter t : nat -> Type.
 
 Parameter get : forall k, t k -> forall v:Var.t, T.interp k (Var.btype v).
 Parameter upd : forall k, t k -> forall v:Var.t, T.interp k (Var.btype v) -> t k.

 Coercion get : t >-> Funclass.

 Notation "m '[' x '<--' v ']'" := (upd m x v) (at level 60).

 Parameter get_upd_same : forall k (m:t k) (tx:T.type) (x:Var.var tx) v, 
  m[(Var.mkV x) <-- v] (Var.mkV x) = v.

 Parameter get_upd_diff : forall k (m:t k) tx (x:Var.var tx) ty (y:Var.var ty) v,
  Var.mkV x <> Var.mkV y -> m[(Var.mkV x) <-- v] (Var.mkV y) = m (Var.mkV y).

 Parameter global : forall k, t k -> t k.

 Parameter return_mem : forall k, t k -> t k -> t k.

 Parameter global_spec : forall k (m:t k) tx (x:Var.var tx), 
  Var.is_global (Var.mkV x) -> m (Var.mkV x) = global m (Var.mkV x).

 Parameter global_local : forall k m tx (x:Var.var tx),
  Var.is_local (Var.mkV x) -> global m (Var.mkV x) = T.default k tx.

 Parameter return_mem_local : forall k (m mf:t k) tx (x:Var.var tx),
  Var.is_local (Var.mkV x) -> return_mem m mf (Var.mkV x) = m (Var.mkV x).

 Parameter return_mem_global : forall k (m mf:t k) tx (x:Var.var tx), 
  Var.is_global (Var.mkV x) -> return_mem m mf (Var.mkV x) = mf (Var.mkV x).

 Definition eq k (m1 m2:t k) := forall x, m1 x = m2 x.
 
 Parameter eq_leibniz : forall k (m1 m2:t k), eq m1 m2 -> m1 = m2.
 
 Parameter eqb : forall k, t k -> t k -> bool.
 
 Parameter eqb_spec : forall k (m1 m2:t k), if eqb m1 m2 then m1 = m2 else m1 <> m2.
 
End MEM.

Declare Module MakeMem : MEM.
