Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.

Definition graph: UU := total2 (fun S: (dirprod hSet hSet) => dirprod ((pr2 S) -> (pr1 S)) ((pr2 S) -> (pr1 S))).

Definition make_graph (V E : hSet) (s t : E -> V) : graph := tpair (fun S : (dirprod hSet hSet) => dirprod ((pr2 S) -> (pr1 S)) ((pr2 S) -> (pr1 S))) (make_dirprod V E) (make_dirprod s t).

Definition vertices_of (g : graph) := dirprod_pr1 (pr1 g).
Definition edges_of (g : graph) := dirprod_pr2 (pr1 g).
Definition source_of (g : graph) := dirprod_pr1 (pr2 g).
Definition target_of (g : graph) := dirprod_pr2 (pr2 g).

Definition path_of_length (g : graph) : nat -> (vertices_of g) -> (vertices_of g) -> UU := nat_rect _ (fun (v1 v2 : (vertices_of g)) => paths v1 v2) (fun (m : nat) (pths_of_m : _) => (fun (v1 v2 : (vertices_of g)) => (total2 (fun u : (vertices_of g) => dirprod (pths_of_m v1 u) (total2 (fun (e : (edges_of g)) => dirprod (paths u ((source_of g) e)) (paths v2 ((target_of g) e)))))))).

Definition cycle (g : graph) : UU := (total2 (fun (v : vertices_of g) => total2 (fun (n : nat) => dirprod (n != 0) (path_of_length g n v v)))).

Definition acyclic (g : graph) : hProp := make_hProp (neg (ishinh (cycle g))) (isapropneg _).

Definition empty_isaset: (isaset empty) := empty_rect (fun (x: empty) => (∏ x': empty, isaprop (paths x x'))).
Definition emptyset: hSet := make_hSet empty empty_isaset.

Definition underlined : nat -> hSet := nat_rect _ emptyset (fun (_ : _) (prev : _) => setcoprod prev unitset).

Definition I_or_O (V : hSet) (f : V -> nat) := total2_hSet (fun v : V => underlined (f v)).

Definition tuple (m n : nat) : UU := total2 (fun V : hSet => total2 (fun in_out : dirprod (V -> nat) (V -> nat) => weq (setcoprod (underlined m) (I_or_O V (dirprod_pr2 in_out))) (setcoprod (underlined n) (I_or_O V (dirprod_pr1 in_out))))).

Definition vertices {m n : nat} (t : tuple m n) := pr1 t.
Definition in_func {m n : nat} (t : tuple m n) := dirprod_pr1 (pr1 (pr2 t)).
Definition out_func {m n : nat} (t : tuple m n) := dirprod_pr2 (pr1 (pr2 t)).
Definition i_func {m n : nat} (t : tuple m n) := pr1 (pr2 (pr2 t)).
Definition i_property {m n : nat} (t : tuple m n) := pr2 (pr2 (pr2 t)).

Definition internal_flow_graph_of {m n : nat} (t : tuple m n) : graph := make_graph (vertices t) (total2_hSet (fun uivj : dirprod_hSet (I_or_O (vertices t) (out_func t)) (I_or_O (vertices t) (in_func t)) => hProp_to_hSet (eqset ((i_func t) (inr (dirprod_pr1 uivj))) (inr (dirprod_pr2 uivj))))) (fun uivj : _ => pr1 (dirprod_pr2 (pr1 uivj))) (fun uivj : _ => pr1 (dirprod_pr1 (pr1 uivj))).

Definition port_graph (m n : nat) : UU := total2 (fun t : tuple m n => acyclic (internal_flow_graph_of t)).

Definition topological_order (g : graph) : UU := total2 (fun enumeration : (vertices_of g) -> nat => forall e : edges_of g, natlth (enumeration ((source_of g) e)) (enumeration ((target_of g) e))).

Lemma trivial_case (g : graph) (top_order : topological_order g) (v1 : vertices_of g) : forall u : vertices_of g, ((paths 0 0) -> empty) -> (path_of_length g 0 v1 u) -> natlth ((pr1 top_order) v1) ((pr1 top_order) u).
Proof.
  intros u prop.
  apply (fromempty (prop (idpath 0))).
Qed.

Lemma trivial_case_for_next_step (g : graph) (top_order : topological_order g) (v1 v : vertices_of g) (n : nat) (path : path_of_length g (S (S n)) v1 v) : natlth ((pr1 top_order) (pr1 path)) ((pr1 top_order) v).
Proof.
  rewrite (dirprod_pr2 (pr2 (dirprod_pr2 (pr2 path)))).
  apply (paths_rect _ (source_of g (pr1 (dirprod_pr2 (pr2 path)))) (fun (ver : vertices_of g) (_ : _) => natlth ((pr1 top_order) ver) ((pr1 top_order) (target_of g (pr1 (dirprod_pr2 (pr2 path)))))) ((pr2 top_order) (pr1 (dirprod_pr2 (pr2 path)))) (pr1 path) (pathsinv0 (dirprod_pr1 (pr2 (dirprod_pr2 (pr2 path)))))).
Qed.

Lemma next_step (g : graph) (top_order : topological_order g) (v1 : vertices_of g) (n : nat) (prev_step : forall u : vertices_of g, ((paths n 0) -> empty) -> (path_of_length g n v1 u) -> natlth ((pr1 top_order) v1) ((pr1 top_order) u)) : forall v : vertices_of g, ((paths (S n) 0) -> empty) -> (path_of_length g (S n) v1 v) -> natlth ((pr1 top_order) v1) ((pr1 top_order) v).
Proof.
  intros v prop path.
  unfold path_of_length in path.
  induction n.
  unfold nat_rect in path.
  rewrite (dirprod_pr1 (pr2 path)).
  unfold topological_order in top_order.
  rewrite (dirprod_pr2 (pr2 (dirprod_pr2 (pr2 path)))).
  apply (paths_rect _ (source_of g (pr1 (dirprod_pr2 (pr2 path)))) (fun (ver : vertices_of g) (_ : _) => natlth ((pr1 top_order) ver) ((pr1 top_order) (target_of g (pr1 (dirprod_pr2 (pr2 path)))))) ((pr2 top_order) (pr1 (dirprod_pr2 (pr2 path)))) (pr1 path) (pathsinv0 (dirprod_pr1 (pr2 (dirprod_pr2 (pr2 path)))))).
  apply (natlehlthtrans _ _ _ (natlthtoleh _ _ (prev_step (pr1 path) (negpathssx0 n) (dirprod_pr1 (pr2 path)))) (trivial_case_for_next_step g top_order v1 v n path)).
Qed.

Lemma extended_topological_order (g : graph) : (topological_order g) -> total2 (fun enumeration : (vertices_of g) -> nat => forall (v1 v2 : vertices_of g) (n : total2 (fun m : nat => (paths m 0) -> empty)), (path_of_length g (pr1 n) v1 v2) -> natlth (enumeration v1) (enumeration v2)).
Proof.
  intros top_order.
  unfold topological_order in top_order.
  exists (pr1 top_order).
  intros v1 v2 n.
  intros path.
  unfold path_of_length in path.
  induction n as [n prop].
  apply (nat_rect (fun (n : nat)  => forall u : vertices_of g, ((paths n 0) -> empty) -> (path_of_length g n v1 u) -> natlth ((pr1 top_order) v1) ((pr1 top_order) u)) (trivial_case g top_order v1) (next_step g top_order v1) n v2 prop path).
Qed.

Theorem topological_order_acyclic (g : graph) : (topological_order g) -> (acyclic g).
Proof.
  unfold acyclic.
  intros top_order cycle.
  unfold topological_order in top_order.
  (**unfold cycle in cycle.**)
  Print ishinh_UU.
  apply (cycle hfalse (fun cycle' => (isirreflnatlth _ ((pr2 (extended_topological_order g top_order)) (pr1 cycle') (pr1 cycle') (tpair (fun n : nat => n != 0) (pr1 (pr2 cycle')) (dirprod_pr1 (pr2 (pr2 cycle')))) (dirprod_pr2 (pr2 (pr2 cycle'))))))).
Qed.

Definition in_example : boolset -> nat := fun (b : boolset) => 1.
Definition out_example : boolset -> nat := fun (b : boolset) => 1.
Definition in_out_example := make_dirprod in_example out_example.

Definition i_func_example : (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr2 in_out_example))) -> (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr1 in_out_example))).
  intros out.
  induction out.
  unfold underlined in a.
  unfold nat_rect in a.
  induction a.
  induction a.
  apply (fromempty (a)).
  unfold I_or_O.
  unfold underlined.
  unfold dirprod_pr1.
  unfold in_out_example.
  unfold make_dirprod.
  unfold pr1.
  unfold in_example.
  unfold nat_rect.
  apply (inr (tpair _ true (inr tt))).
  apply (inr (tpair _ false (inr tt))).
  unfold in_out_example in b.
  unfold make_dirprod in b.
  unfold dirprod_pr2 in b.
  unfold pr2 in b.
  unfold I_or_O in b.
  induction b as [v i].
  induction v.
  unfold out_example in i.
  unfold underlined in i.
  unfold nat_rect in i.
  induction i.
  apply (fromempty (a)).
  apply (inl (inl (inr tt))).
  unfold out_example in i.
  unfold underlined in i.
  unfold nat_rect in i.
  induction i.
  apply (fromempty (a)).
  apply (inl (inr tt)).
Defined.

Definition i_func_example_reverse : (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr1 in_out_example))) -> (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr2 in_out_example))).
  intros in_.
  induction in_.
  unfold underlined in a.
  unfold nat_rect in a.
  induction a.
  induction a.
  apply (fromempty (a)).
  unfold I_or_O.
  unfold underlined.
  unfold dirprod_pr2.
  unfold in_out_example.
  unfold make_dirprod.
  unfold pr2.
  unfold out_example.
  unfold nat_rect.
  apply (inr (tpair _ true (inr tt))).
  apply (inr (tpair _ false (inr tt))).
  unfold in_out_example in b.
  unfold make_dirprod in b.
  unfold dirprod_pr1 in b.
  unfold pr1 in b.
  unfold I_or_O in b.
  induction b as [v i].
  induction v.
  unfold in_example in i.
  unfold underlined in i.
  unfold nat_rect in i.
  induction i.
  apply (fromempty (a)).
  apply (inl (inl (inr tt))).
  unfold in_example in i.
  unfold underlined in i.
  unfold nat_rect in i.
  induction i.
  apply (fromempty (a)).
  apply (inl (inr tt)).
Defined.

Theorem is_iso_i_example_1 : ∏ out_ : (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr2 in_out_example))), i_func_example_reverse (i_func_example out_) = out_.
  intros out_.
  induction out_.
  unfold underlined in a.
  unfold nat_rect in a.
  induction a.
  induction a.
  apply (fromempty a).
  unfold i_func_example.
  unfold coprod_rect.
  unfold i_func_example_reverse.
  unfold coprod_rect.
  unfold bool_rect.
  apply (maponpaths).
  apply (maponpaths).
  apply (maponpaths).
  apply isProofIrrelevantUnit.
  unfold i_func_example.
  unfold coprod_rect.
  unfold i_func_example_reverse.
  unfold coprod_rect.
  unfold bool_rect.
  apply maponpaths.
  apply maponpaths.
  apply isProofIrrelevantUnit.
  unfold in_out_example in b.
  unfold make_dirprod in b.
  unfold dirprod_pr2 in b.
  unfold pr2 in b.
  unfold I_or_O in b.
  induction b as [v i].
  induction v.
  unfold out_example in i.
  unfold underlined in i.
  unfold nat_rect in i.
  induction i.
  apply (fromempty a).
  unfold i_func_example.
  unfold coprod_rect.
  unfold bool_rect.
  unfold i_func_example_reverse.
  unfold coprod_rect.
  apply maponpaths.
  apply maponpaths.
  apply maponpaths.
  apply isProofIrrelevantUnit.
  unfold out_example in i.
  unfold underlined in i.
  unfold nat_rect in i.
  induction i.
  apply (fromempty a).
  unfold i_func_example.
  unfold coprod_rect.
  unfold bool_rect.
  unfold i_func_example_reverse.
  unfold coprod_rect.
  apply maponpaths.
  apply maponpaths.
  apply maponpaths.
  apply isProofIrrelevantUnit.
Qed.

Theorem is_iso_i_example_2 : ∏ in_ : (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr1 in_out_example))), i_func_example (i_func_example_reverse in_) = in_.
  intros in_.
  induction in_.
  unfold underlined in a.
  unfold nat_rect in a.
  induction a.
  induction a.
  apply (fromempty a).
  unfold i_func_example.
  unfold coprod_rect.
  unfold i_func_example_reverse.
  unfold coprod_rect.
  unfold bool_rect.
  apply (maponpaths).
  apply (maponpaths).
  apply (maponpaths).
  apply isProofIrrelevantUnit.
  unfold i_func_example.
  unfold coprod_rect.
  unfold i_func_example_reverse.
  unfold coprod_rect.
  unfold bool_rect.
  apply maponpaths.
  apply maponpaths.
  apply isProofIrrelevantUnit.
  unfold in_out_example in b.
  unfold make_dirprod in b.
  unfold dirprod_pr2 in b.
  unfold pr2 in b.
  unfold I_or_O in b.
  induction b as [v i].
  induction v.
  unfold out_example in i.
  unfold underlined in i.
  unfold nat_rect in i.
  induction i.
  apply (fromempty a).
  unfold i_func_example.
  unfold coprod_rect.
  unfold bool_rect.
  unfold i_func_example_reverse.
  unfold coprod_rect.
  apply maponpaths.
  apply maponpaths.
  apply maponpaths.
  apply isProofIrrelevantUnit.
  unfold out_example in i.
  unfold underlined in i.
  unfold nat_rect in i.
  induction i.
  apply (fromempty a).
  unfold i_func_example.
  unfold coprod_rect.
  unfold bool_rect.
  unfold i_func_example_reverse.
  unfold coprod_rect.
  apply maponpaths.
  apply maponpaths.
  apply maponpaths.
  apply isProofIrrelevantUnit.
Qed.

Definition i_example : weq (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr2 in_out_example))) (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr1 in_out_example))).
  unfold weq.
  exists i_func_example.
  apply (isweq_iso _ i_func_example_reverse is_iso_i_example_1 is_iso_i_example_2).
Defined.

Definition tuple_example : tuple 2 2.
  unfold tuple.
  exists boolset.
  exists in_out_example.
  apply i_example.
Defined.

Lemma setcoprod_injective: ∏ (A B: hSet), ∏ (a: A), ∏ (b: B), (paths (inl a) (inr b)) -> empty.
  intros.
  exact (transportf (coprod_rect (fun (_: setcoprod A B) => Type)  (fun _ => unit) (fun _ => empty)) X tt).
Qed.

Definition acyclicity_tuple_example_1 : acyclic (internal_flow_graph_of tuple_example).
apply topological_order_acyclic.
  unfold topological_order.
  exists (bool_rect _ 1 2).
  intros e.
  unfold internal_flow_graph_of in e.
  unfold tuple_example in e.
  unfold edges_of in e.
  unfold make_graph in e.
  unfold dirprod_pr2 in e.
  unfold make_dirprod in e.
  unfold pr2 in e.
  unfold pr1 in e.
  induction e as [uivj prop].
  unfold vertices in uivj.
  unfold pr1 in uivj.
  unfold out_func in uivj.
  unfold in_func in uivj.
  unfold dirprod_pr2 in uivj.
  unfold dirprod_pr1 in uivj.
  unfold pr1 in uivj.
  unfold pr2 in uivj.
  unfold in_out_example in uivj.
  unfold make_dirprod in uivj.
  unfold I_or_O in uivj.
  induction uivj as [ui vj].
  induction ui as [u i].
  induction vj as [v j].
  unfold i_func in prop.
  unfold in_out_example in prop.
  unfold make_dirprod in prop.
  unfold dirprod_pr1 in prop.
  unfold pr1 in prop.
  unfold pr2 in prop.
  induction u.
  unfold out_example in i.
  unfold underlined in i.
  unfold nat_rect in i.
  induction i.
  apply (fromempty a).
  induction v.
  unfold out_example in j.
  unfold underlined in j.
  unfold nat_rect in j.
  induction j.
  apply (fromempty a).
  apply (fromempty (setcoprod_injective _ _ _ _ prop)).
  unfold in_example in j.
  unfold underlined in j.
  unfold nat_rect in j.
  induction j.
  apply (fromempty a).
  apply (fromempty (setcoprod_injective _ _ _ _ prop)).
  unfold out_example in i.
  unfold underlined in i.
  unfold nat_rect in i.
  induction i.
  apply (fromempty a).
  induction v.
  unfold in_example in j.
  unfold underlined in j.
  unfold nat_rect in j.
  induction j.
  apply (fromempty a).
  apply (fromempty (setcoprod_injective _ _ _ _ prop)).
  unfold in_example in j.
  unfold underlined in j.
  unfold nat_rect in j.
  induction j.
  apply (fromempty a).
  apply (fromempty (setcoprod_injective _ _ _ _ prop)).
Defined.

Definition acyclicity_tuple_example_2 : acyclic (internal_flow_graph_of tuple_example).
apply topological_order_acyclic.
  unfold topological_order.
  exists (bool_rect _ 2 1).
  intros e.
  unfold internal_flow_graph_of in e.
  unfold tuple_example in e.
  unfold edges_of in e.
  unfold make_graph in e.
  unfold dirprod_pr2 in e.
  unfold make_dirprod in e.
  unfold pr2 in e.
  unfold pr1 in e.
  induction e as [uivj prop].
  unfold vertices in uivj.
  unfold pr1 in uivj.
  unfold out_func in uivj.
  unfold in_func in uivj.
  unfold dirprod_pr2 in uivj.
  unfold dirprod_pr1 in uivj.
  unfold pr1 in uivj.
  unfold pr2 in uivj.
  unfold in_out_example in uivj.
  unfold make_dirprod in uivj.
  unfold I_or_O in uivj.
  induction uivj as [ui vj].
  induction ui as [u i].
  induction vj as [v j].
  unfold i_func in prop.
  unfold in_out_example in prop.
  unfold make_dirprod in prop.
  unfold dirprod_pr1 in prop.
  unfold pr1 in prop.
  unfold pr2 in prop.
  induction u.
  unfold out_example in i.
  unfold underlined in i.
  unfold nat_rect in i.
  induction i.
  apply (fromempty a).
  induction v.
  unfold out_example in j.
  unfold underlined in j.
  unfold nat_rect in j.
  induction j.
  apply (fromempty a).
  apply (fromempty (setcoprod_injective _ _ _ _ prop)).
  unfold in_example in j.
  unfold underlined in j.
  unfold nat_rect in j.
  induction j.
  apply (fromempty a).
  apply (fromempty (setcoprod_injective _ _ _ _ prop)).
  unfold out_example in i.
  unfold underlined in i.
  unfold nat_rect in i.
  induction i.
  apply (fromempty a).
  induction v.
  unfold in_example in j.
  unfold underlined in j.
  unfold nat_rect in j.
  induction j.
  apply (fromempty a).
  apply (fromempty (setcoprod_injective _ _ _ _ prop)).
  unfold in_example in j.
  unfold underlined in j.
  unfold nat_rect in j.
  induction j.
  apply (fromempty a).
  apply (fromempty (setcoprod_injective _ _ _ _ prop)).
Defined.

Definition example_of_port_graph : port_graph 2 2.
  unfold port_graph.
  exists tuple_example.
  apply acyclicity_tuple_example_1.
Defined.

Definition example2_of_port_graph : port_graph 2 2.
  unfold port_graph.
  exists tuple_example.
  apply acyclicity_tuple_example_2.
Defined.

Lemma do_acyclisity_proofs_equal : paths acyclicity_tuple_example_1 acyclicity_tuple_example_2.
  apply (propproperty (acyclic (internal_flow_graph_of tuple_example))).
Qed.

Theorem do_examples_equal : paths example_of_port_graph example2_of_port_graph.
  unfold example_of_port_graph.
  unfold example2_of_port_graph.
  apply (maponpaths _ do_acyclisity_proofs_equal).
Qed.


Print example_of_port_graph.

Search natgth.


  (**apply (inr (tpair (fun vi : (boolset × natset)%set => dirprod_pr2 vi > 0 × dirprod_pr2 vi ≤ dirprod_pr1 in_out_example (dirprod_pr1 vi)) (make_dirprod true 1) (make_dirprod (natgthsnn 0) (isreflnatleh 1)))).
  apply (inr (tpair (fun vi : (boolset × natset)%set => dirprod_pr2 vi > 0 × dirprod_pr2 vi ≤ dirprod_pr1 in_out_example (dirprod_pr1 vi)) (make_dirprod false 1) (make_dirprod (natgthsnn 0) (isreflnatleh 1)))).
  induction b as [vi prop].
  induction vi as [v i].
  induction v.
  unfold in_out_example in prop.
  unfold dirprod_pr2 in prop.
  unfold pr2 in prop.
  unfold make_dirprod in prop.
  unfold out_example in prop.
  induction i.
  apply (fromempty (negnatgth0n 0 (pr1 prop))).
  induction i.
  unfold underlined.
  unfold nat_rect.
  apply (inl (inl (inr tt))).**)

(**Definition i_func_example :  (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr2 in_out_example))) -> (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr1 in_out_example))).
  intros out.
  induction out.
  induction a as [n prop].
  induction n.
  unfold hProp_to_hSet in prop.
  apply (fromempty (negnatgth0n 0 (pr1 prop))).
  induction n.
  unfold I_or_O.
  apply (inr (tpair (fun vi : (boolset × natset)%set => dirprod_pr2 vi > 0 × dirprod_pr2 vi ≤ dirprod_pr1 in_out_example (dirprod_pr1 vi)) (make_dirprod false 1) (make_dirprod (natgthsnn 0) (isreflnatleh 1)))).
  induction n.
  apply (inr (tpair (fun vi : (boolset × natset)%set => dirprod_pr2 vi > 0 × dirprod_pr2 vi ≤ dirprod_pr1 in_out_example (dirprod_pr1 vi)) (make_dirprod true 1) (make_dirprod (natgthsnn 0) (isreflnatleh 1)))).
  apply (fromempty (negnatlehsnn 0 ((natlehandplusrinv 1 0 2) (pr2 prop)))).
  induction b as [vi prop].
  induction vi as [v i].
  induction v.
  unfold in_out_example in prop.
  unfold dirprod_pr2 in prop.
  unfold pr2 in prop.
  unfold out_example in prop.
  unfold dirprod_pr1 in prop.
  unfold pr1 in prop.
  unfold make_dirprod in prop.
  induction i.
  apply (fromempty (negnatgth0n 0 (pr1 prop))).
  induction i.
  unfold underlined.
  apply (inl (tpair (fun n : nat => dirprod (natgth n 0) (natleh n 2)) 2 (make_dirprod (natgthsn0 0) (natlehnsn 1)))).
  apply (fromempty (negnatlehsnn 0 ((natlehandplusrinv 1 0 1) (pr2 prop)))).
  unfold in_out_example in prop.
  unfold dirprod_pr2 in prop.
  unfold pr2 in prop.
  unfold out_example in prop.
  unfold dirprod_pr1 in prop.
  unfold pr1 in prop.
  unfold make_dirprod in prop.
  induction i.
  apply (fromempty (negnatgth0n 0 (pr1 prop))).
  induction i.
  unfold underlined.
  apply (inl (tpair (fun n : nat => dirprod (natgth n 0) (natleh n 2)) 1 (make_dirprod (natgthsn0 0) (natlehnsn 1)))).
  apply (fromempty (negnatlehsnn 0 ((natlehandplusrinv 1 0 1) (pr2 prop)))).
Defined.

Definition i_func_example_reverse : (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr1 in_out_example))) -> (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr2 in_out_example))).
intros out.
  induction out.
  induction a as [n prop].
  induction n.
  unfold hProp_to_hSet in prop.
  apply (fromempty (negnatgth0n 0 (pr1 prop))).
  induction n.
  unfold I_or_O.
  apply (inr (tpair (fun vi : (boolset × natset)%set => dirprod_pr2 vi > 0 × dirprod_pr2 vi ≤ dirprod_pr1 in_out_example (dirprod_pr1 vi)) (make_dirprod true 1) (make_dirprod (natgthsnn 0) (isreflnatleh 1)))).
  induction n.
  apply (inr (tpair (fun vi : (boolset × natset)%set => dirprod_pr2 vi > 0 × dirprod_pr2 vi ≤ dirprod_pr1 in_out_example (dirprod_pr1 vi)) (make_dirprod false 1) (make_dirprod (natgthsnn 0) (isreflnatleh 1)))).
  apply (fromempty (negnatlehsnn 0 ((natlehandplusrinv 1 0 2) (pr2 prop)))).
  induction b as [vi prop].
  induction vi as [v i].
  induction v.
  unfold in_out_example in prop.
  unfold dirprod_pr2 in prop.
  unfold pr2 in prop.
  unfold out_example in prop.
  unfold dirprod_pr1 in prop.
  unfold pr1 in prop.
  unfold make_dirprod in prop.
  induction i.
  apply (fromempty (negnatgth0n 0 (pr1 prop))).
  induction i.
  unfold underlined.
  apply (inl (tpair (fun n : nat => dirprod (natgth n 0) (natleh n 2)) 2 (make_dirprod (natgthsn0 0) (natlehnsn 1)))).
  apply (fromempty (negnatlehsnn 0 ((natlehandplusrinv 1 0 1) (pr2 prop)))).
  unfold in_out_example in prop.
  unfold dirprod_pr2 in prop.
  unfold pr2 in prop.
  unfold out_example in prop.
  unfold dirprod_pr1 in prop.
  unfold pr1 in prop.
  unfold make_dirprod in prop.
  induction i.
  apply (fromempty (negnatgth0n 0 (pr1 prop))).
  induction i.
  unfold underlined.
  apply (inl (tpair (fun n : nat => dirprod (natgth n 0) (natleh n 2)) 1 (make_dirprod (natgthsn0 0) (natlehnsn 1)))).
  apply (fromempty (negnatlehsnn 0 ((natlehandplusrinv 1 0 1) (pr2 prop)))).
Defined.

Print i_func_example.

Theorem is_iso_i_example_1 : ∏ out_ : (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr2 in_out_example))), i_func_example_reverse (i_func_example out_) = out_.
  intros out_.
  induction out_.
  induction a as [n prop].
  induction n.
  apply (fromempty (negnatgth0n 0 (pr1 prop))).
  induction n.
  unfold i_func_example.
  unfold nat_rect.
  unfold coprod_rect.
  unfold i_func_example_reverse.
  unfold nat_rect.
  unfold coprod_rect.
  unfold bool_rect.
  unfold in_example.
  unfold out_example.
  unfold pr1.
  unfold pr2.
  unfold dirprod_pr1.
  unfold dirprod_pr2.
  auto.


Definition i_boolset : weq (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr2 in_out_boolset))) (setcoprod (underlined 2) (I_or_O boolset (dirprod_pr1 in_out_boolset))).
  unfold weq.
  unfold I_or_O.**)







  Check (fun (n : nat) => (fun (u : vertices_of g) => ((paths n 0) -> empty) -> (path_of_length g n v1 u) -> natlth ((pr1 top_order) v1) ((pr1 top_order) u))).
  Check nat_rect (fun (n : nat) => (fun (u : vertices_of g) => ((paths n 0) -> empty) -> (path_of_length g n v1 u) -> natlth ((pr1 top_order) v1) ((pr1 top_order) u))).
  Check nat_rect (fun (n : nat) (u : vertices_of g) => ((paths n 0) -> empty) -> (path_of_length g n v1 u) -> natlth ((pr1 top_order) v1) ((pr1 top_order) u)).
  Check (fun (n : nat) => ((path n 0) -> empty) -> (total2 (fun (u : vertices_of g) => path_of_length g n v1 u)) -> natlth ((pr1 top_order) v1) ((pr1 top_order) u)).
  Check (fun (n : nat) => ((paths n 0) -> empty)) -> (total2 (fun (u : vertices_of g) => path_of_length g n v1 u)) -> natlth ((pr1 top_order) v1) ((pr1 top_order) u).
  Check nat_rect (fun (n : nat) (u : vertices_of g) => ((paths n 0) -> empty) -> (path_of_length g n v1 u) -> natlth ((pr1 top_order) v1) ((pr1 top_order) v2)).




  Check nat_rect (fun (n : nat) => ((paths n 0) -> empty) -> nat_rect (fun (m : nat) (u : vertices_of g) => (path_of_length g m v1 u) -> (pr1 top_order) v1 < (pr1 top_order) u) )




  Check nat_rect.
  Check nat_rect (fun (n : nat) => ((paths n 0) -> empty) -> (path_of_length g n v1 v2) -> natlth ((pr1 top_order) v1) ((pr1 top_order) v2)) case1











Lemma case1 (g : graph) (top_order : topoligical_order g) (v1 v2 : vertices_of g) : ((paths 0 0) -> empty) -> (path_of_length g 0 v1 v2) -> natlth ((pr1 top_order) v1) ((pr1 top_order) v2).
Proof.
  intros prop.
  apply (fromempty (prop (idpath 0))).
Qed.

Check nat_rect.

Lemma case2 (g : graph) (top_order : topoligical_order g) (v1 v2 : vertices_of g) (n : nat) (Pn : ((paths n 0) -> empty) -> (path_of_length g n v1 v2) -> natlth ((pr1 top_order) v1) ((pr1 top_order) v2)) : ((paths (S n) 0) -> empty) -> (path_of_length g (S n) v1 v2) -> natlth






  induction n.
  apply (fromempty (prop (idpath 0))).
  unfold pr1 in path.
  induction n.
  unfold nat_rect in path.
  rewrite (dirprod_pr1 (pr2 path)).
  rewrite (dirprod_pr1 (pr2 (dirprod_pr2 (pr2 path)))).
  rewrite (dirprod_pr2 (pr2 (dirprod_pr2 (pr2 path)))).

   ((pr2 top_order) (pr1 (dirprod_pr2 (pr2 path)))).
  unfold nat_rect in path.




  g : graph
  top_order : ∑ enumeration : vertices_of g → nat,
              ∏ e : edges_of g, enumeration (source_of g e) < enumeration (target_of g e)
  v1, v2 : vertices_of g
  n : ∑ m : nat, m = 0 → ∅
  path : nat_rect (λ _ : nat, vertices_of g → vertices_of g → UU)
           (λ v1 v2 : vertices_of g, v1 = v2)
           (λ (_ : nat) (pths_of_m : vertices_of g → vertices_of g → UU)
            (v1 _ : vertices_of g),
            ∑ u : vertices_of g,
            pths_of_m v1 u × (∑ e : edges_of g, u = source_of g e × u = target_of g e))
           (pr1 n) v1 v2
  ============================
  pr1 top_order v1 < pr1 top_order v2










Print port_graph.

Definition internal_flow_graph_of {m n : nat} (t : tuple m n) : graph := make_graph (vertices t) (total2_hSet (fun ui : I_or_O (vertices t) (out_func t) => hProp_to_hSet (eqset (coprodtobool ((i_func t) (inr ui))) false))).









Record graph (V : UU) := mk_graph {A : UU; s : A -> V; t : A -> V}.

Arguments A {_} _.
Arguments s {_} _.
Arguments t {_} _.

Definition graph_mul {V : UU} := fun (g1 : graph V) (g2 : graph V) => mk_graph V (total2 (fun a1a2 : (dirprod (A g1) (A g2)) => paths ((t g1) (dirprod_pr1 a1a2)) ((s g2) (dirprod_pr2 a1a2)))) (fun a : _ => (s g1) (dirprod_pr1 (pr1 a))) (fun a : _ => (t g2) (dirprod_pr2 (pr1 a))).

Definition power {V : UU} (g : graph V) : nat -> graph V := nat_rect _ g (fun (n : _) (gn : _) => graph_mul g gn).

Definition func_union {A B C : UU} (f1 : A -> C) (f2 : B -> C) : (coprod A B) -> C := coprod_rect _  f1 f2.

Definition graph_union {V : UU} := fun (g1 : graph V) (g2 : graph V) => mk_graph V (coprod (A g1) (A g2)) (func_union (s g1) (s g2)) (func_union (t g1) (t g2)).

Definition transitive_closure {V : UU} (g : graph V) := g. (* to do: should be union of all natural powers of g *)

Definition acyclisity {V : UU} (g : graph V) := forall a : (A g), ((s g) a) <> ((t g) a).

Record port_graph (m n : nat) := mk_port_graph {V : UU; in : V -> nat; out : V -> nat; }


Definition something {S : hSet} {s s' : S} (x x' : paths s s') (prop : isaprop (pr1 (s = s')%set)) : iscontr (paths x x').
Proof.
  unfold isaprop in prop.
  unfold isofhlevel in prop.
  Check prop x x'.
  apply (prop x x').
Defined.


Definition something2 {S : hSet} {s s' : S} {x x' : paths s s'} (contr : iscontr (paths x x')) (e e' : paths x x') : paths e e'.
  unfold iscontr in contr.
  rewrite (pr2 contr e).
  rewrite (pr2 contr e').
  apply (idpath (pr1 contr)).
Defined.



Theorem help (S : hSet) (s s' : S) : isaset (paths s s').
Proof.
  unfold isaset.
  intros x x'.
  unfold isaprop.
  unfold isofhlevel.
  intros e e'.
  unfold iscontr.
  exists (something2 (something x x' (propproperty (eqset s s'))) e e').
  intros t0.
  unfold propproperty.
  unfold eqset.
  unfold pr2.
  unfold make_hProp.
  unfold something.
  unfold something2.
  unfold internal_paths_rew_r.
  Check something x x' (propproperty (eqset s s')).
  Check (propproperty (eqset s s')).



  Definition graph_union {V : UU} := fun (g1 : graph V) (g2 : graph V) => mk_graph V (coprod)

Definition graph (V : UU) {A : UU} := dirprod UU (dirprod UU (dirprod (A -> V) (A -> V))).
Definition make_graph (V A : UU) (s t : A -> V) : graph V := make_dirprod V (make_dirprod A (make_dirprod s t)).

Definition not_set_graph_mul {V : UU} := fun (g1 : graph V) (g2 : graph V) => make_graph V (total2 (fun a1a2 : (dirprod A1 A2) => paths (t1 (dirprod_pr1 a1a2)) (s2 (dirprod_pr2 a1a2)))) (fun x : _ => s1 (dirprod_pr1 (pr1 x))) (fun x : _ => t2 (dirprod_pr2 (pr1 x))) where "A1" := (dirprod_pr1 (dirprod_pr2 g1)).

Fixpoint power (n : nat) {V A1 A2 : UU} {s1 t1 : A1 -> V} {s2 t2 : A2 -> V} (g : not_set_graph V A1 s1 t1) : not_set_graph V A2 s2 t2 :=
  match n with
    | 0 => g
    | S p => (not_set_graph_mul g (power p g))
  end.


Definition graph (V A : hSet) (s t : A -> V) := UU.

Variable (V A1 A2 : hSet) (s1 t1 : A1 -> V) (s2 t2 : A2 -> V) (a1a2 : dirprod_hSet A1 A2).
Check dirprod_hSet A1 A2.
Check paths (t1 (pr1 a1a2)) (s2 (pr2 a1a2)).
Check isaset (paths (t1 (pr1 a1a2)) (s2 (pr2 a1a2))).
Check forall a1a2 : (dirprod_hSet A1 A2), paths (t1 (pr1 a1a2)) (s2 (pr2 a1a2)).
Check total2 (fun a1a2 : (dirprod_hSet A1 A2) => paths (t1 (pr1 a1a2)) (s2 (pr2 a1a2))).
Check paths (t1 (pr1 a1a2)) (s2 (pr2 a1a2)).

Theorem h (e e' : paths (t1 (pr1 a1a2)) (s2 (pr2 a1a2))) (x x' : paths e e') : paths x x'.
  Check setproperty V.
  Print isaset.
  Print isaprop.

Theorem help : isaset (paths (t1 (pr1 a1a2)) (s2 (pr2 a1a2))).
  unfold isaset.
  intros e e'.
  unfold isaprop.
  unfold isofhlevel.
  intros x x'.
  unfold iscontr.
  Check total2_rect.
  Check tpair.
  Check tpair (fun cntr : (paths x x') => forall t : _, paths t cntr).
Check forall_hSet (fun x : (total2 (fun a1a2 : (dirprod_hSet A1 A2) => paths (t1 (pr1 a1a2)) (s2 (pr2 a1a2)))) => pr1 x).
Check pr1.
Check pr1 (total2 (fun a1a2 : (dirprod_hSet A1 A2) => paths (t1 (pr1 a1a2)) (s2 (pr2 a1a2)))).


Definition graph_mul (V : hSet) {A1 A2 : hSet} {s1 t1 : A1 -> V} {s2 t2 : A2 -> V} := fun (g1 : graph V A1 s1 t1) (g2 : graph V A2 s2 t2) => graph V
