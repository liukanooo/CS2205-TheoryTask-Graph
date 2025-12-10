Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic path.

Import SetsNotation.

Local Open Scope sets.

Section EPATH.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {A: Type}
        {path: @Path G V E pg gv A}
        {emptypath: @EmptyPath G V E pg gv A path}
        {singlepath: @SinglePath G V E pg gv A path}
        {concatpath: @ConcatPath G V E pg gv A path}.

Definition valid_epath: 
    G -> V -> list E -> V -> Prop := 
    fun g u p v => exists P: A, path_valid g P /\ edge_in_path P = p /\ hd_error (vertex_in_path P) = Some u /\ nth_error (vertex_in_path P) (length (vertex_in_path P) - 1) = Some v.

Definition simple_epath (g: G) (u: V) (p: list E) (v: V): Prop :=
    NoDup p /\ valid_epath g u p v.

Definition simple_circuit (g: G) (e: list E) (u: V): Prop :=
    simple_epath g u e u.

Definition have_simple_circuit (g: G) : Prop :=
  exists u p, simple_epath g u p u.

Lemma valid_path_evalid: forall g p u v,
  valid_epath g u p v ->
  forall e, In e p -> evalid g e.
Proof.
Admitted.

Lemma path_simplfier 
  {stepuniqueundirected: StepUniqueUndirected G V E}: 
  forall g p u v,
  valid_epath g u p v ->
  exists q, simple_epath g u q v.
Proof.
  (* intros.
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
    } *)
Admitted.

End EPATH.