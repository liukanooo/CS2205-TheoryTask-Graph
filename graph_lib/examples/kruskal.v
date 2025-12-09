Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.

From GraphLib Require Import graph_basic reachable_basic path_basic vpath.


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
  weight_sym: forall u v, original_weight origin (u, v) = original_weight origin (v, u);
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
  original_vH: (fst e = x /\ snd e = y) \/ (fst e = y /\ snd e = x);
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

#[export]Instance OriginalGraph_stepuniqueundirected {V: Type}: 
  StepUniqueUndirected (OriginalGraphType V) V (V * V).
Proof.
  split. intros. 
  destruct H0.
  destruct H1.
  destruct original_vH0 as [[]|[]]; destruct original_vH1 as [[]|[]]; subst; auto.
Qed. 

#[export]Instance OriginalGraph_undirected {V: Type}: 
  UndirectedGraph (OriginalGraphType V) V (V * V).
Proof.
  split; intros.
  destruct H.
  destruct original_vH0 as [[]|[]]; split; auto.
Qed.

#[export]Instance Original_finitegraph {V: Type}:
  FiniteGraph (OriginalGraphType V) V (V * V). 
Proof.
  refine {|graph_basic.listV := original_vlist; |}.
  auto.
Defined.


Section kruskal.

Context {V: Type}
        (g: OriginalGraphType V)
        (origin_gvalid: OriginalGraph_gvalid g)
        (defaultV: V).

Notation step := (step g).
Notation reachable := (reachable g).


End kruskal.