
Require Import SetsClass.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Logic.Classical.
Require Import Coq.Arith.Arith.
From GraphLib Require Import graph_basic reachable_basic Syntax.

Local Open Scope list.

Import ListNotations.

Section path.
  
Context {G: Type}
        {V: Type}
        {E: Type}
        {g: G}
        {pg: Graph G V E}
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {g_valid: gvalid g}.

Definition epath: Type := list E.
Definition vpath: Type := list V.

Fixpoint valid_epath (g: G) (p: epath) (u v: V): Prop :=
  match p with
  | nil => u = v
  | e :: l => exists w, step_aux g e u w /\ valid_epath g l w v
  end.

Context (defaultV: V).
Context (defaultE: E).

Record epath_to_vpath (g: G) (pe: epath) (u v: V) (pv: vpath): Prop := {
    epath_to_vpath_length: length pv = length pe + 1;
    epath_to_vpath_step: 
        forall n, 0 <= n < length pe -> 
            step_aux g (nth n pe defaultE) (nth n pv defaultV) (nth (S n) pv defaultV);
    epath_to_vpath_start: nth 0 pv defaultV = u;
    epath_to_vpath_end: nth (length pe) pv defaultV = v;
}.

Definition valid_epath' (g: G) (p: epath) (u v: V): Prop :=
  exists l: vpath, epath_to_vpath g p u v l.



Lemma valid_epath_valid_epath': forall p u v,
  valid_epath g p u v <-> valid_epath' g p u v.
Proof.
    intros; split; intros.
    * revert u v H; induction p; intros. 
      ** simpl in *; subst. 
         exists [v]; split; simpl; auto.
         intros; lia.
      ** simpl in *; destruct H as [w [H1 H2]].
         apply IHp in H2 as [l []]; auto.
         exists (u :: l); split; simpl; auto.
         intros. 
         destruct n; simpl.
         erewrite epath_to_vpath_start0; eauto.
         apply epath_to_vpath_step0; lia.
    * revert u v H; induction p; intros.
      ** simpl in *; destruct H as [l []]; simpl in *. 
         rewrite <- epath_to_vpath_end0; rewrite epath_to_vpath_start0; reflexivity.
      ** simpl in *; destruct H as [l []]; simpl in *.
         pose proof (epath_to_vpath_step0 0 ltac:(lia)); simpl in H.
         rewrite epath_to_vpath_start0 in H.
         remember (nth 1 l defaultV) as w.
         exists w; split; auto.
         apply IHp.
         destruct l; simpl in *; try congruence.
         exists l; split; auto.
         intros. pose proof (epath_to_vpath_step0 (S n) ltac:(lia)); auto.
Qed.

Definition simple_path (g: G) (p: epath) (u v: V): Prop :=
    NoDup p /\ valid_epath g p u v.

Lemma In_three_parts {X: Type}: forall (x: X) l,
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros.
  revert x H.
  induction l; intros.
  * simpl in *; subst; exfalso; auto.
  * destruct (classic (x = a)) as [Heq | Hneq].
    ** subst.
       exists []; exists l; split; auto.
    ** destruct H; subst; try congruence. 
       apply IHl in H as [l1 [l2]].
       exists (a :: l1), l2; subst; auto.
Qed.

Lemma path_simplfier 
  {stepuniqueundirected: StepUniqueUndirected G V E}: 
  forall p u v,
  valid_epath g p u v ->
  exists q, simple_path g q u v.
Proof.
  intros.
  revert u v H.
  induction p; intros.
  * simpl in *; subst.
    exists []; split; [apply NoDup_nil|reflexivity].
  * simpl in *; destruct H as [w [Hstep Hpath]].
    apply IHp in Hpath as [q [HNoDup Hpath]]; auto.
    destruct (classic (In a q)) as [Hin | Hnin].
    {
      apply In_three_parts in Hin as [q1 [q2]].
      apply valid_epath_valid_epath' in Hpath. 
      destruct Hpath as [l []]. 
      pose proof (epath_to_vpath_step0 (length q1) ltac:(subst; rewrite length_app; simpl; lia)).
      remember (nth (length q1) q defaultE) as e.
      (* remember (nth (length q1) l defaultV) as x.
      remember (nth (length q1 + 1) l defaultV) as y. *)
      assert (e = a) by (subst; rewrite app_nth2; try lia; rewrite Nat.sub_diag; simpl; reflexivity). 
      subst a; subst.
      eapply step_aux_unique_undirected in Hstep as [[]|[]]; eauto; subst.
      ** exists (e :: q2); split. 
        - subst; apply NoDup_app_remove_l in HNoDup; auto.
        - simpl; exists (nth (S (length q1)) l defaultV); split; auto. 
          assert (length q1 < length l) by (subst; rewrite length_app in *; simpl; lia).
          eapply nth_split with (d:=defaultV) in H as [l1 [l2 []]].
          assert (length l2 = length q2 + 1). {
            subst; try rewrite length_app in *.
            rewrite H in epath_to_vpath_length0; rewrite length_app in epath_to_vpath_length0; simpl in epath_to_vpath_length0. lia. }
          apply valid_epath_valid_epath'.
          exists l2; split; auto. 
          { 
              intros. 
              pose proof (epath_to_vpath_step0 (n + length q1 + 1) ltac:(rewrite length_app; simpl; lia)) as Hp.
              rewrite H in Hp. 
              repeat (rewrite app_nth2 in Hp; try lia).
              replace (n + length q1 + 1 - length q1) with (1 + n) in Hp by lia.
              replace (n + length q1 + 1 - length l1) with (1 + n) in Hp by lia.
              replace (S (n + length q1 + 1) - length l1) with (1 + S n) in Hp by lia. 
              simpl in Hp; auto. 
          }
          {
            rewrite H.
            rewrite app_nth2; try lia.
            replace (S (length q1) - length l1) with 1 by lia.
            simpl; auto.
          }
          {
            rewrite H.
            rewrite app_nth2; try (rewrite length_app; lia).
            replace (length (q1 ++ e :: q2) - length l1) with (1 + length q2) by (rewrite length_app; simpl; lia).
            simpl; auto.
          }
      ** exists q2; split.
        - apply NoDup_app_remove_l in HNoDup; auto.
          inversion HNoDup; auto.
        - apply valid_epath_valid_epath'.
          assert ( length q1 < length l) by (subst; try rewrite length_app in *; simpl in *; lia).
          eapply nth_split with (d:=defaultV) in H1 as [l1 [l2 []]]. 
          assert (length l2 = length q2 + 1). {
            subst; try rewrite length_app in *.
            rewrite H1 in epath_to_vpath_length0; rewrite length_app in epath_to_vpath_length0; simpl in epath_to_vpath_length0. lia. }
          exists l2; split; try lia.
          {
            intros. 
            pose proof (epath_to_vpath_step0 (n + length q1 + 1) ltac:(rewrite length_app; simpl; lia)) as Hp.
            rewrite H1 in Hp.
            repeat (rewrite app_nth2 in Hp; try lia).
            replace (n + length q1 + 1 - length q1) with (1 + n) in Hp by lia.
            replace (n + length q1 + 1 - length l1) with (1 + n) in Hp by lia.
            replace (S (n + length q1 + 1) - length l1) with (1 + S n) in Hp by lia. 
            simpl in Hp; auto.
          }
          {
            rewrite H1.
            rewrite app_nth2; try lia.
            replace (S (length q1) - length l1) with 1 by lia.
            simpl; auto.
          }
          {
            rewrite H1.
            rewrite app_nth2; try (rewrite length_app; lia).
            replace (length (q1 ++ e :: q2) - length l1) with (1 + length q2) by (rewrite length_app; simpl; lia).
            simpl; auto.
          }
    } 
    {
      exists ( a :: q) ; split; simpl; auto.
      * apply NoDup_cons; auto.
      * eexists; split; eauto.
    }
Qed.
    


Definition simple_circuit (g: G) (e: epath) (u: V): Prop :=
    simple_path g e u u.

Definition have_simple_circuit (g: G) : Prop :=
  exists p u, simple_circuit g p u.


Lemma valid_path_evalid: forall g p u v,
  valid_epath' g p u v ->
  forall e, In e p -> evalid g e.
Proof.
  intros. eapply In_nth with (d:=defaultE) in H0 ; auto.
  destruct H as [l []].
  destruct H0 as [n []].
  pose proof (epath_to_vpath_step0 n ltac:(lia)).
  apply step_evalid in H1.
  rewrite <- H0; auto.
Qed.

End path.