Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From ListLib Require Import Basics.
From GraphLib Require Import graph_basic reachable_basic path vpath.
From MaxMinLib Require Import MaxMin.

Import SetsNotation.
Local Open Scope sets.

Record OriginalGraphType {V: Type} := {
  original_vlist : list V;
  original_weight: (V * V) -> option nat;
}.

Arguments OriginalGraphType _: clear implicits.

Record OriginalGraphProp {V: Type} (origin: OriginalGraphType V): Prop := {
  vlist_nodup: NoDup origin.(original_vlist);
  vlist_in1: forall u v w, original_weight origin (u, v) = Some w -> In u origin.(original_vlist);
  vlist_in2: forall u v w, original_weight origin (u, v) = Some w -> In v origin.(original_vlist);
  dist_refl: forall u, original_weight origin (u, u) = Some 0;
}.

Arguments OriginalGraphProp _: clear implicits.

Definition original_vvalid {V: Type} (g: OriginalGraphType V) (v: V) := 
  In v g.(original_vlist).

Definition original_evalid {V: Type} (g: OriginalGraphType V) (e: (V * V)) := 
  exists w, original_weight g e = Some w.

Record original_step_aux {V: Type} (g: OriginalGraphType V) (e: (V * V)) (x y: V): Prop:=
{ 
  original_vx: original_vvalid g x;
  original_vy: original_vvalid g y;
  original_ve: original_evalid g e;
  original_fst: fst e = x;
  original_snd: snd e = y;
}.

#[export]Instance OriginalGraph_graph {V: Type} : 
  Graph (OriginalGraphType V) V (V * V) := {|
  graph_basic.vvalid := original_vvalid;
  graph_basic.evalid := original_evalid;
  graph_basic.step_aux := original_step_aux;
|}.

#[export]Instance OriginalGraph_gvalid {V: Type} : 
  GValid (OriginalGraphType V) :=
  @OriginalGraphProp V.

#[export]Instance OriginalGraph_stepvalid {V: Type}: 
  StepValid (OriginalGraphType V) V (V * V).
Proof.
  split; intros;
  destruct H; auto.
Qed.

#[export]Instance OriginalGraph_noemptyedge {V: Type}: 
  NoEmptyEdge (OriginalGraphType V) V (V * V).
Proof.
  split; intros.
  exists (fst e), (snd e).
  split; auto;
  destruct e; simpl in *; 
  destruct H0; 
  destruct H. 
  apply vlist_in3 in H0; auto.
  apply vlist_in4 in H0; auto.
Qed.

#[export]Instance OriginalGraph_stepuniquedirected {V: Type}: 
  StepUniqueDirected (OriginalGraphType V) V (V * V).
Proof.
  split. intros. 
  destruct H0.
  destruct H1.
  split; subst; reflexivity.
Qed. 

#[export]Instance Original_finitegraph {V: Type}:
  FiniteGraph (OriginalGraphType V) V (V * V). 
Proof.
  refine {|graph_basic.listV := original_vlist; |}.
  auto.
Defined.


Section floyd.

Context {V: Type}
        (g: OriginalGraphType V)
        (origin_gvalid: OriginalGraph_gvalid g)
        {P: Type}
        {path: path.Path (OriginalGraphType V) V (V * V) P}.

Notation step := (step g).
Notation reachable := (reachable g).

Definition weight (g: OriginalGraphType V) (u v: V) := (original_weight g) (u, v).

Lemma no_multiple_edge: forall x y e1 e2,
  step_aux g e1 x y -> step_aux g e2 x y -> e1 = e2.
Proof.
  intros.
  destruct H.
  destruct H0.
  destruct e1, e2.
  subst; simpl in *; subst.
  reflexivity.
Qed.

Lemma path_slice_trans: forall (i j k: V) (p1 p2: list V), 
  valid_vpath g i p1 j -> 
  valid_vpath g j p2 k -> 
  valid_vpath g i (p1 ++ p2) k.
Admitted.

Lemma path_slice_length: forall (k: V) (p1 p2: list V), 
  vpath_weight weight g (p1 ++ k :: p2) = option_plus (vpath_weight weight g (p1 ++ k :: nil)) (vpath_weight weight g (k :: p2)).
Admitted. 

Lemma shortest_path_prefix_shortest: forall (i j k: V) (p p1: list V), 
  p1 is_a_prefix_of p -> 
  nth_error p1 (length p1 - 1)  = Some k ->
  min_weight_vpath weight g i p j -> 
  min_weight_vpath weight g i p1 k.
Admitted.

Lemma shortest_path_suffix_shortest: forall (i j k: V) (p p2: list V), 
  p2 is_a_suffix_of p ->
  hd_error p2 = Some k ->
  min_weight_vpath weight g i p j -> 
  min_weight_vpath weight g k p2 j.
Admitted.

Lemma shortest_path_all_shortest: forall (i j k l: V) (p p1 p2: list V), 
  p1 is_a_prefix_of p -> 
  p2 is_a_suffix_of p1 -> 
  hd_error p2 = Some k -> 
  nth_error p2 (length p2 - 1) = Some l -> 
  min_weight_vpath weight g i p j ->
  min_weight_vpath weight g k p2 l.
Admitted.

Lemma shortest_path_is_simple: forall (i j: V) (p: list V), 
  min_weight_vpath weight g i p j ->
  NoDup p.
Admitted.

Lemma shortest_path_segment: forall (i j k: V) (p: list V) (cur: V -> Prop),
  ~ k ∈ cur ->
  min_weight_vpath_in_vset weight g i p j (cur ∪ [k]) -> 
  In k p -> 
  exists p1 p2, p = p1 ++ k :: p2 /\
  min_weight_vpath_in_vset weight g i p1 k cur /\
  min_weight_vpath_in_vset weight g k p2 j cur.
Admitted.

Lemma path_in_vset_mono: forall (i j k: V) (p: list V) (cur: V -> Prop),
  min_weight_vpath_in_vset weight g i p j cur ->
  min_weight_vpath_in_vset weight g i p k (cur ∪ [k]).
Admitted.
  
Lemma shortest_path_triangle_inequality: forall (i j k: V) (n n1 n2: nat), 
  min_weight_distance weight g i j n ->
  min_weight_distance weight g i k n1 ->
  min_weight_distance weight g k j n2 ->
  option_le (Some n) (option_plus (Some n1) (Some n2)).
Admitted.

End floyd.