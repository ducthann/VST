(** * Lemmas about the Dry Machine*)
Require Export Lia.
Require Import compcert.lib.Axioms.

Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.common.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
(* Require Import compcert.common.Events. *)
Require Import compcert.lib.Integers.
Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.dry_context.
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.common.tactics.

Set Bullet Behavior "Strict Subproofs".

Global Notation "a # b" := (Maps.PMap.get b a) (at level 1).

(** This file holds various results about the dry machine*)
(* Find other lemmas in dry_machine_step_lemmas.v        *)

Module ThreadPoolWF.
  Import HybridMachine ThreadPool DryHybridMachine HybridMachineSig.
  Section ThreadPoolWF.
    Context {Sem : Semantics}.

    Existing Instance DryHybridMachine.dryResources.
    Existing Instance OrdinalPool.OrdinalThreadPool.
    (** Take an instance of the Dry Machine *)
    Existing Instance DryHybridMachine.DryHybridMachineSig.


  Lemma unlift_m_inv :
    forall tp tid (Htid : tid < (OrdinalPool.num_threads tp).+1) ord
      (Hunlift: unlift (ordinal_pos_incr (OrdinalPool.num_threads tp))
                       (Ordinal (n:=(OrdinalPool.num_threads tp).+1)
                                (m:=tid) Htid)=Some ord),
      nat_of_ord ord = tid.
  Proof.
    intros.
    assert (Hcontra: unlift_spec (ordinal_pos_incr (OrdinalPool.num_threads tp))
                                 (Ordinal (n:=(OrdinalPool.num_threads tp).+1)
                                          (m:=tid) Htid) (Some ord)).
    rewrite <- Hunlift.
    apply/unliftP.
    inversion Hcontra; subst.
    inversion H0.
    unfold bump.
    assert (pf: ord < (OrdinalPool.num_threads tp))
      by (by rewrite ltn_ord).
    assert (H: (OrdinalPool.num_threads tp) <= ord = false).
    rewrite ltnNge in pf.
    rewrite <- Bool.negb_true_iff. auto.
    rewrite H. simpl. rewrite add0n. reflexivity.
  Defined.

  (* TODO: seems to be deprecated. Delete if so*)
  (*
  (** Well-formed predicate on new permission map*)
  Definition newPermMap_wf tp pmap :=
    forall k,
      permMapsDisjoint (Resources.get k (allDataRes tp)) pmap.1 /\
      permMapsDisjoint (Resources.get k (allLockRes tp)) pmap.2.

  Definition permMap_wf tp pmap i :=
    forall j (cntj : containsThread tp j) (Hneq: i <> j),
      permMapsDisjoint (getThreadR cntj) pmap.


 Opaque pos_incr.
  Lemma addThread_racefree :
    forall tp vf arg p (Hwf: newPermMap_wf tp p) (Hrace: race_free tp),
      race_free (addThread tp vf arg p).
  Proof.
    unfold race_free in *. intros.
    simpl.
    match goal with
    | [ |- context[ match ?Expr with _ => _ end]] =>
      destruct Expr as [ordi|] eqn:Hgeti
    end;
      match goal with
      | [ |- context[ match ?Expr with _ => _ end]] =>
        destruct Expr as [ordj|] eqn:Hgetj
      end.
    unfold containsThread in *; simpl in *.
    - unfold getThreadR in Hrace.
      apply unlift_m_inv in Hgeti.
      apply unlift_m_inv in Hgetj.
      destruct ordi as [i' pfi], ordj as [j' pfj]; subst.
      simpl in *.
      eapply Hrace; eauto.
    - apply unlift_m_inv in Hgeti.
      subst. unfold newPermMap_wf in Hwf.
      destruct ordi. eapply Hwf; eauto.
    - apply unlift_m_inv in Hgetj.
      subst. unfold newPermMap_wf in Hwf.
      destruct ordj. apply permMapsDisjoint_comm. eapply Hwf; eauto.
    - destruct (i == (num_threads tp)) eqn:Heqi.
      + move/eqP:Heqi=>Heqi. subst.
        assert (Hcontra: (ordinal_pos_incr (num_threads tp))
                           != (Ordinal (n:=(num_threads tp).+1) (m:=j) cntj)).
        { apply/eqP. intros Hcontra.
          unfold ordinal_pos_incr in Hcontra.
          inversion Hcontra; auto.
        }
        exfalso. apply unlift_some in Hcontra. rewrite Hgetj in Hcontra.
        destruct Hcontra. discriminate.
      + move/eqP:Heqi=>Heqi.
        assert (
            Hcontra: (ordinal_pos_incr (num_threads tp))
                       !=
                       (Ordinal (n:=(num_threads tp).+1) (m:=i) cnti)).
        { apply/eqP. intros Hcontra.
          unfold ordinal_pos_incr in Hcontra. inversion Hcontra. subst. auto. }
        exfalso. apply unlift_some in Hcontra.
        rewrite Hgeti in Hcontra. destruct Hcontra.
        discriminate.
  Defined. *)

  Lemma initial_invariant0: forall pmap c,
      DryHybridMachine.invariant (mkPool c pmap) (* (empty_map, empty_map) *).
  Proof.
    intros pmap c.
    pose (IM:=mkPool c pmap (* (empty_map, empty_map) *)); fold IM.
    assert (isZ: forall i, OrdinalPool.containsThread IM i -> (i = 0)%N).
    { rewrite /containsThread /IM /=.
      move => i; destruct i; first[reflexivity | intros HH; inversion HH].
    }
    assert (noLock: forall l rm,
               OrdinalPool.lockRes IM l = Some rm -> False).
    { rewrite /OrdinalPool.lockRes /IM /=.
      move => l rm.
      rewrite /lockRes
              /OrdinalPool.mkPool
              /OrdinalPool.empty_lset /= OrdinalPool.find_empty => HH.
      inversion HH.
    }

    constructor.
    + move => i j0 cnti cntj HH.
      exfalso; apply HH.
      move: cnti cntj => /isZ -> /isZ ->; reflexivity.
    + move=> l1 l2 rm1 rm2 neq /noLock contra; exfalso; now eauto.
    + move => i l cnt rm /noLock contra; exfalso; now eauto.
    + move=> i cnti; split.
      * move => j0 cntj.
        exfalso.
        apply (noLock i cnti Hres).
      * move => l rm /noLock contra; exfalso; now eauto.
    + unfold lr_valid; simpl; unfold OrdinalPool.lr_valid; intros.
      case Hres: (OrdinalPool.lockRes IM (b, ofs)) => [rm |]; last done.
      by case: (noLock (b, ofs) rm Hres).
  Qed.

  Lemma initial_mem_compatible: forall c m,
      mem_compatible (mkPool c (getCurPerm m) (* (empty_map, empty_map) *)) m.
  Proof.
    intros c m.
    pose (IM:=mkPool c (getCurPerm m) (* (empty_map, empty_map) *)); fold IM.
    assert (isZ: forall i, OrdinalPool.containsThread IM i -> (i = 0)%N).
    { rewrite /containsThread /IM /=.
      move => i; destruct i; first[reflexivity | intros HH; inversion HH].
    }
    assert (noLock: forall l rm,
               OrdinalPool.lockRes IM l = Some rm -> False).
    { rewrite /OrdinalPool.lockRes /IM /=.
      move => l rm.
      rewrite /lockRes
              /OrdinalPool.mkPool
              /OrdinalPool.empty_lset /= OrdinalPool.find_empty => HH.
      inversion HH.
    }

    constructor; try done.
    intros ??.
    pose proof (isZ _ cnt); subst.
    subst IM; simpl; apply cur_lt_max.
  Qed.

  Check permMapsDisjoint.

  Lemma updThread_inv :
  forall ds i (cnt : containsThread ds i) c (pmap : res),
    invariant ds ->
    (forall j (cntj : containsThread ds j),
        i <> j ->
        permMapsDisjoint pmap (getThreadR cntj)) ->
    (forall l rmap,
        lockRes ds l = Some rmap ->
        permMapsDisjoint pmap rmap) ->
    (forall l rmap,
        lockRes ds l = Some rmap ->
        Mem.perm_order''
          (Some Nonempty)
          (pmap # (l.1) l.2)) ->

    invariant (updThread cnt c pmap).
  Proof.
    intros ds x cnt c pmap INV Hthr Hlock Hlock_perm.
    destruct INV as [Htt Hll Htl Hlocks Hvalid].
    constructor.
    
    (* Threads remain pairwise disjoint. *)
    - intros i j cnti cntj Hneq.
      destruct (scheduler.NatTID.eq_tid_dec x i) as [Hxi | Hxi].
      + subst i.
        assert (cntj_old : containsThread ds j).
        { eapply cntUpdate'; eauto. }
        
        rewrite gssThreadRes.
        erewrite @gsoThreadRes with (cntj := cntj_old); auto.
      + destruct (scheduler.NatTID.eq_tid_dec x j) as [Hxj | Hxj].
        * subst j.
          assert (cnti_old : containsThread ds i).
          { eapply cntUpdate'; eauto. }
          apply permMapsDisjoint_comm.
          rewrite gssThreadRes.
          erewrite @gsoThreadRes with (cntj := cnti_old); auto.
        * assert (cnti_old : containsThread ds i).
          { eapply cntUpdate'; eauto. }
          assert (cntj_old : containsThread ds j).
          { eapply cntUpdate'; eauto. }
          erewrite @gsoThreadRes with (cntj := cnti_old); auto.
          erewrite @gsoThreadRes with (cntj := cntj_old); auto.
    (* Lock resources do not change. *)
    - intros laddr1 laddr2 rmap1 rmap2 Hneq Hres1 Hres2.
      rewrite gsoThreadLPool in Hres1.
      rewrite gsoThreadLPool in Hres2.
      eapply Hll; eauto.
    (* Threads remain disjoint from lock resources. *)
    - intros i laddr cnti rmap Hres.
      rewrite gsoThreadLPool in Hres.
      destruct (scheduler.NatTID.eq_tid_dec x i) as [Hxi | Hxi].
      + subst i.
        rewrite gssThreadRes.
        eapply Hlock; eauto.
      + assert (cnti_old : containsThread ds i).
        { eapply cntUpdate'; eauto. }
        
        erewrite @gsoThreadRes with (cntj := cnti_old); auto.
        eapply Htl; eauto.        
    (* Every thread and lock has Nonempty permission at lock addresses. *)
    - intros laddr rmap Hres.
      rewrite gsoThreadLPool in Hres.
      split.
      + intros j cntj.
        destruct (scheduler.NatTID.eq_tid_dec x j) as [Hxj | Hxj].
        * subst j.
          rewrite gssThreadRes.
          eapply Hlock_perm; eauto.
        * assert (cntj_old : containsThread ds j).
          { eapply cntUpdate'; eauto. }
          erewrite @gsoThreadRes with (cntj := cntj_old); auto.
          exact ((proj1 (Hlocks laddr rmap Hres)) j cntj_old).
      + intros laddr' rmap' Hres'.
        rewrite gsoThreadLPool in Hres'.
        exact ((proj2 (Hlocks laddr rmap Hres)) laddr' rmap' Hres').
    (* The lock map itself is unchanged. *)
    - move=> b ofs.
      rewrite gsoThreadLPool.
      exact (Hvalid b ofs).
  Qed.

  Lemma invariant_decr :
  forall tp c pmap i (cnti : containsThread tp i)
    (Hinv : invariant tp)
    (Hdecr : forall b ofs,
        Mem.perm_order''
          ((getThreadR cnti) # b ofs)
          (pmap # b ofs)),
    invariant (updThread cnti c pmap).
  Proof.
    intros tp c pmap i cnti Hinv Hdecr.
    eapply updThread_inv.
    - exact Hinv.
    (* The decreased map remains disjoint from other threads. *)
    - intros j cntj Hneq.
      pose proof (no_race_thr tp Hinv i j cnti cntj Hneq) as Hdisj.
      unfold permMapsDisjoint in *.
      intros b ofs.
      specialize (Hdisj b ofs).
      specialize (Hdecr b ofs).
      rewrite perm_union_comm.
      rewrite perm_union_comm in Hdisj.
      eapply perm_union_lower; eauto.
    (* The decreased map remains disjoint from lock resources. *)
    - intros laddr rmap Hres.
      pose proof (no_race tp Hinv i laddr cnti rmap Hres) as Hdisj.
      unfold permMapsDisjoint in *.
      intros b ofs.
      specialize (Hdisj b ofs).
      specialize (Hdecr b ofs).
      rewrite perm_union_comm.
      rewrite perm_union_comm in Hdisj.
      eapply perm_union_lower; eauto.
    (* Permission at a lock address remains at most Nonempty. *)
    - intros laddr rmap Hres.
      pose proof ((proj1 (locks_data_lock_coh tp Hinv laddr rmap Hres)) i cnti) as Hnonempty.
      eapply mem_lemmas.po_trans.
      + exact Hnonempty.
      + apply Hdecr.
  Qed.

  (** [invariant] is preserved by [updThreadC]*)
  Lemma updThreadC_invariant:
    forall (tp : t) i c
      (ctn : containsThread tp i)
      (Hinv : invariant tp),
      invariant (updThreadC ctn c).
  Proof.
    intros.
    inversion Hinv;
      constructor;
      simpl in *;
        by auto.
  Qed.

  Lemma updLock_inv :
  forall tp b ofs rmap (Hinv : invariant tp)
    (Hdisjoint_res :
       forall laddr rmap',
         laddr <> (b, ofs) -> lockRes tp laddr = Some rmap' -> permMapsDisjoint rmap rmap')
    (Hdisjoint_thr :
       forall i (cnti : containsThread tp i), permMapsDisjoint (getThreadR cnti) rmap)
    (* Old lock resources are bounded at the new lock address,
       and the new resource is bounded at old lock addresses. *)
    (Hbound_res :
       forall laddr rmap',
         laddr <> (b, ofs) -> lockRes tp laddr = Some rmap' ->
         Mem.perm_order'' (Some Nonempty) (rmap' # b ofs) /\
         Mem.perm_order'' (Some Nonempty) (rmap # (laddr.1) laddr.2))
    (* The new resource is bounded at its own lock address. *)
    (Hbound_rmap : Mem.perm_order'' (Some Nonempty) (rmap # b ofs))
    (* Every thread is bounded at the new lock address. *)
    (Hbound_thr : forall i (cnti : containsThread tp i),
         Mem.perm_order'' (Some Nonempty) ((getThreadR cnti) # b ofs))
    (Hvalid1 :
       forall ofs0, (ofs < ofs0 < ofs + lksize.LKSIZE)%Z -> lockRes tp (b, ofs0) = None)
    (Hvalid2 :
       forall ofs0, (ofs0 < ofs < ofs0 + lksize.LKSIZE)%Z -> lockRes tp (b, ofs0) = None),
    invariant (updLockSet tp (b, ofs) rmap).
  Proof.
    intros.
    destruct Hinv as [no_race_thr0 no_race_lr0 no_race0 locks_data_lock_coh0 lockRes_valid0].
    constructor.
    (* Updating locks does not modify thread resources. *)
    - intros.
      rewrite !gLockSetRes.
      eapply no_race_thr0; eauto.
    (* Lock resources remain pairwise disjoint. *)
    - intros.
      destruct (EqDec_address (b, ofs) laddr1) as [Heq1 | Hneq1].
      + subst laddr1.
        rewrite gssLockRes in Hres1.
        inversion Hres1; subst rmap1.
        rewrite gsoLockRes in Hres2.
        eapply Hdisjoint_res; eauto. done.
      + rewrite gsoLockRes in Hres1; auto.
        destruct (EqDec_address (b, ofs) laddr2) as [Heq2 | Hneq2].
        * subst laddr2.
          rewrite gssLockRes in Hres2.
          inversion Hres2; subst rmap2.
          apply permMapsDisjoint_comm.
          eapply Hdisjoint_res; eauto.
        * rewrite gsoLockRes in Hres2; auto.
          exact (no_race_lr0 laddr1 laddr2 rmap1 rmap2 Hneq Hres1 Hres2).
    (* Threads remain disjoint from lock resources. *)
    - intros i laddr cnti rmap' Hres.
      destruct (EqDec_address (b, ofs) laddr) as [Heq | Hneq].
      + subst laddr.
        rewrite gssLockRes in Hres.
        inversion Hres; subst rmap'.
        eapply Hdisjoint_thr.
      + rewrite gsoLockRes in Hres; auto.
        assert (cnti_old : containsThread tp i). by eapply cntUpdateL'; eauto.
        rewrite gLockSetRes.
        exact (no_race0 i laddr cnti_old rmap' Hres).
    (* Permissions at every lock address are at most Nonempty. *)
    - intros laddr rmap' Hres.
      destruct (EqDec_address (b, ofs) laddr) as [Heq | Hneq].
      (* The newly installed lock. *)
      + subst laddr.
        rewrite gssLockRes in Hres.
        inversion Hres; subst rmap'.
        split.
        * intros i cnti.
          rewrite gLockSetRes.
          eapply Hbound_thr.
        * intros laddr' rmap' Hres'.
          destruct (EqDec_address (b, ofs) laddr') as [Heq' | Hneq'].
          -- subst laddr'.
             rewrite gssLockRes in Hres'.
             inversion Hres'; subst rmap'.
             exact Hbound_rmap.
          -- rewrite gsoLockRes in Hres'; auto.
             assert (Hlneq : laddr' <> (b, ofs)) by congruence.
             exact (proj1 (Hbound_res laddr' rmap' Hlneq Hres')).
      (* An existing lock. *)
      + rewrite gsoLockRes in Hres; auto.
        split.
        * intros i cnti.
          apply ((proj1 (locks_data_lock_coh0 laddr rmap' Hres)) i cnti).
        * intros laddr' rmap'' Hres'.
          destruct (EqDec_address (b, ofs) laddr') as [Heq' | Hneq'].
          -- subst laddr'.
             rewrite gssLockRes in Hres'.
             inversion Hres'; subst rmap''.
             assert (Hlneq : laddr <> (b, ofs)) by congruence.
             exact (proj2 (Hbound_res laddr rmap' Hlneq Hres)).
          -- rewrite gsoLockRes in Hres'; auto.
             exact ((proj2 (locks_data_lock_coh0 laddr rmap' Hres)) laddr' rmap'' Hres').
    (* Preserve lock-range validity. *)
    - intros b' ofs'.
      destruct (EqDec_address (b, ofs) (b', ofs')) as [Heq | Hneq].
      + inversion Heq; subst b' ofs'.
        rewrite gsslockResUpdLock.
        intros ofs0 Hrange.
        rewrite gsolockResUpdLock.
        * apply Hvalid1 || apply Hvalid2; auto.
        * intros Hcontra.
          inversion Hcontra; subst.
          lia.
      + rewrite gsolockResUpdLock; auto.
        specialize (lockRes_valid0 b' ofs').
        destruct (lockRes tp (b', ofs')) eqn:Hres; auto.
        intros ofs0 Hrange.
        destruct (EqDec_address (b, ofs) (b', ofs0)) as [Heq' | Hneq'].
        * inversion Heq'; subst b' ofs0.
          apply Hvalid1 in Hrange || apply Hvalid2 in Hrange.
          rewrite Hrange in Hres.
          discriminate.
        * rewrite gsolockResUpdLock; auto.
  Qed.

 (** [mem_compatible] is preserved by [addThread]*)
  (* NOTE: Strange statement, updThread doesn't need to be here probably*)
  Lemma mem_compatible_add:
    forall tp i (cnti: containsThread tp i) c pmap vf arg pmap2 m
      (Hcomp: mem_compatible
                (addThread
                   (updThread cnti c pmap) vf arg pmap2) m),
      mem_compatible (updThread cnti c pmap) m.
  Proof.
    intros.
    split.
    - intros j cntj.
      assert (cntj' := cntAdd vf arg pmap2 cntj).
      specialize (compat_th _ _ Hcomp cntj').
      erewrite gsoAddRes;
        by eauto.
    - intros l pmap' Hres.
      erewrite <- @gsoAddLPool
      with (vf := vf) (arg := arg) (p := pmap2) in Hres;
        by pose proof ((compat_lp _ _ Hcomp _ _ Hres)).
    - intros l rmap Hres.
      erewrite <- @gsoAddLPool
      with (vf := vf) (arg := arg) (p := pmap2) in Hres;
        by pose proof ((lockRes_blocks _ _ Hcomp _ _ Hres)).
  Qed.

  (** [mem_compatible] is preserved by [remLockSet] *)
  Lemma mem_compatible_remlock:
    forall tp m addr
      (Hinv: lr_valid (lockRes tp))
      (Hcomp: mem_compatible tp m),
      mem_compatible (remLockSet tp addr) m.
  Proof.
    intros.
    constructor.
    - eapply Hcomp.
    - intros.
      destruct (EqDec_address addr l).
      subst. rewrite gsslockResRemLock in H. discriminate.
      rewrite gsolockResRemLock in H; auto.
      eapply Hcomp; eauto.
    - intros l rmap Hres.
      destruct (EqDec_address addr l).
      subst. rewrite gsslockResRemLock in Hres. discriminate.
      rewrite gsolockResRemLock in Hres; auto.
      eapply Hcomp; eauto.
  Qed.

  (** [invariant] is preserved by [remLockSet]*)
  Lemma remLock_inv: forall ds a, invariant ds -> invariant (remLockSet ds a).
  Proof.
    intros.
    inversion H as [no_race_thr0 no_race_lr0 no_race0 locks_data_lock_coh0 lockRes_valid0].
    constructor.
    (* Removing a lock does not change thread resources. *)
    - intros i j cnti cntj Hneq.
    pose proof (cntRemoveL' _ cnti) as cnti_old.
    pose proof (cntRemoveL' _ cntj) as cntj_old.
    erewrite @gRemLockSetRes with (cnti := cnti_old).
    erewrite @gRemLockSetRes with (cnti := cntj_old).
    exact (no_race_thr0 i j cnti_old cntj_old Hneq).
    (* Remaining lock resources are still disjoint. *)
    - intros laddr1 laddr2 rmap1 rmap2 Hneq Hres1 Hres2.
      destruct (EqDec_address a laddr1) as [Heq1 | Hneq1].
      + subst laddr1.
        rewrite gsslockResRemLock in Hres1.
        discriminate.
      + rewrite gsolockResRemLock in Hres1; auto.
        destruct (EqDec_address a laddr2) as [Heq2 | Hneq2].
        * subst laddr2.
          rewrite gsslockResRemLock in Hres2.
          discriminate.
        * rewrite gsolockResRemLock in Hres2; auto.
          exact (no_race_lr0 laddr1 laddr2 rmap1 rmap2 Hneq Hres1 Hres2).

    (* Threads remain disjoint from remaining lock resources. *)
    - intros i laddr cnti rmap Hres.
      destruct (EqDec_address a laddr) as [Heq | Hneq].
      + subst laddr.
        rewrite gsslockResRemLock in Hres.
        discriminate.
      + rewrite gsolockResRemLock in Hres; auto.
        pose proof (cntRemoveL' _ cnti) as cnti_old.
        erewrite @gRemLockSetRes with (cnti := cnti_old).
        exact (no_race0 i laddr cnti_old rmap Hres).
    (* Permission bounds at remaining lock addresses are preserved. *)
    - intros laddr rmap Hres.
      destruct (EqDec_address a laddr) as [Heq | Hneq].
      + subst laddr.
        rewrite gsslockResRemLock in Hres.
        discriminate.
      + rewrite gsolockResRemLock in Hres; auto.
        destruct (locks_data_lock_coh0 laddr rmap Hres) as [Hthreads Hlocks].
        split.
        * intros j cntj.
          pose proof (cntRemoveL' _ cntj) as cntj_old.
          erewrite @gRemLockSetRes with (cnti := cntj_old).
          exact (Hthreads j cntj_old).
        * intros laddr' rmap' Hres'.
          destruct (EqDec_address a laddr') as [Heq' | Hneq'].
          -- subst laddr'.
             rewrite gsslockResRemLock in Hres'.
             discriminate.
          -- rewrite gsolockResRemLock in Hres'; auto.
             exact (Hlocks laddr' rmap' Hres').
    (* Removing a lock preserves non-overlapping lock ranges. *)
    - intros b ofs.
      specialize (lockRes_valid0 b ofs).
      destruct (lockRes (remLockSet ds a) (b, ofs)) eqn:Hres; auto.
      destruct (EqDec_address a (b, ofs)) as [Heq | Hneq].
      + subst a.
        rewrite gsslockResRemLock in Hres.
        discriminate.
      + rewrite gsolockResRemLock in Hres; auto.
        rewrite Hres in lockRes_valid0.
        intros ofs0 Hrange.
        specialize (lockRes_valid0 ofs0 Hrange).
        destruct (EqDec_address a (b, ofs0)) as [Heq' | Hneq'].
        * subst a.
          rewrite gsslockResRemLock.
          reflexivity.
        * rewrite gsolockResRemLock; auto.
  Qed.


  Lemma invariant_add : forall tp i (cnti : containsThread tp i) c pmap1 pmap2 vf arg
    (Hinv : invariant (addThread (updThread cnti c pmap1) vf arg pmap2)),
    invariant (updThread cnti c pmap1).
  Proof.
    intros tp i cnti c pmap1 pmap2 vf arg Hinv.
    constructor.
    (* Existing threads remain disjoint. *)
    - intros k j cntk cntj Hneq.
      assert (cntk' := cntAdd vf arg pmap2 cntk).
      assert (cntj' := cntAdd vf arg pmap2 cntj).
      pose proof ((no_race_thr _ Hinv) k j cntk' cntj' Hneq) as Hdisj.
      erewrite @gsoAddRes with (cntj := cntk) in Hdisj; eauto.
      erewrite @gsoAddRes with (cntj := cntj) in Hdisj; eauto.
    (* Lock resources are unchanged by addThread. *)
    - intros laddr1 laddr2 rmap1 rmap2 Hneq Hres1 Hres2.
      erewrite <- @gsoAddLPool with (vf := vf) (arg := arg) (p := pmap2) in Hres1.
      erewrite <- @gsoAddLPool with (vf := vf) (arg := arg) (p := pmap2) in Hres2.
      exact ((no_race_lr _ Hinv) laddr1 laddr2 rmap1 rmap2 Hneq Hres1 Hres2).
    (* Existing threads remain disjoint from lock resources. *)
    - intros j laddr cntj rmap Hres.
      assert (cntj' := cntAdd vf arg pmap2 cntj).
      erewrite <- @gsoAddRes with (cntj' := cntj').
      erewrite <- @gsoAddLPool with (vf := vf) (arg := arg) (p := pmap2) in Hres.
      exact ((no_race _ Hinv) j laddr cntj' rmap Hres).
    (* Permission bounds at lock addresses are preserved. *)
    - intros laddr rmap Hres.
      erewrite <- @gsoAddLPool with (vf := vf) (arg := arg) (p := pmap2) in Hres.
      pose proof (locks_data_lock_coh _ Hinv laddr rmap Hres) as Hcoh.
      split.
      + intros j cntj.
        assert (cntj' := cntAdd vf arg pmap2 cntj).
        erewrite <- @gsoAddRes with (cntj' := cntj').
        exact ((proj1 Hcoh) j cntj').
      + intros laddr' rmap' Hres'.
        erewrite <- @gsoAddLPool with (vf := vf) (arg := arg) (p := pmap2) in Hres'.
        exact ((proj2 Hcoh) laddr' rmap' Hres').
    (* Lock-range validity is unchanged by addThread. *)
    - intros b0 ofs0.
      pose proof ((lockRes_valid _ Hinv) b0 ofs0) as Hvalid.
      rewrite gsoAddLPool in Hvalid.
      exact Hvalid.
  Qed.

  Lemma invariant_not_freeable :
    forall tp (Hinv : invariant tp) b ofs rmap0 (Hlock : lockRes tp (b, ofs) = Some rmap0),
      (forall i (cnti : containsThread tp i), (getThreadR cnti) # b ofs <> Some Freeable) /\
        (forall laddr rmap (Hres : lockRes tp laddr = Some rmap), rmap # b ofs <> Some Freeable).
  Proof.
    intros tp Hinv b ofs rmap0 Hlock.
    pose proof (locks_data_lock_coh tp Hinv (b, ofs) rmap0 Hlock) as Hcoh.
    destruct Hcoh as [Hthreads Hlocks].
    split.
    - intros i cnti Hfreeable.
      specialize (Hthreads i cnti).
      simpl in Hthreads.
      rewrite Hfreeable in Hthreads.
      inversion Hthreads.
    - intros laddr rmap Hres Hfreeable.
      specialize (Hlocks laddr rmap Hres).
      simpl in Hlocks.
      rewrite Hfreeable in Hlocks.
      inversion Hlocks.
  Qed.

  Lemma invariant_freeable_empty_locks :
    forall tp i (cnti : containsThread tp i) b ofs (Hinv : invariant tp)
           (Hfreeable : (getThreadR cnti) # b ofs = Some Freeable),
    forall laddr rmap, lockRes tp laddr = Some rmap -> rmap # b ofs = None.
  Proof.
    intros tp i cnti b ofs Hinv Hfreeable laddr rmap Hres.
    pose proof ((no_race tp Hinv i laddr cnti rmap Hres) b ofs) as Hdisjoint.
    rewrite Hfreeable in Hdisjoint.
    apply no_race_racy in Hdisjoint;
      eauto using racy.
    inversion Hdisjoint; auto.
  Qed.

  Lemma mem_compatible_invalid_block :
    forall tp m b ofs (Hcomp : mem_compatible tp m) (Hinvalid : ~ Mem.valid_block m b),
      (forall i (cnti : containsThread tp i), (getThreadR cnti) # b ofs = None) /\
        (forall laddr rmap, lockRes tp laddr = Some rmap -> rmap # b ofs = None).
  Proof.
    intros tp m b ofs Hcomp Hinvalid.
    destruct Hcomp as [Hthreads Hlocks Hlock_blocks].
    split.
    - intros i cnti.
      eapply permMapLt_invalid_block; eauto.
    - intros laddr rmap Hres.
      eapply permMapLt_invalid_block; eauto.
  Qed.

  (** ** Lemmas about initial state*)

  (** The initial thread is thread 0*)
  Lemma init_thread:
    forall m m' pmap f arg tp i
      (Hinit: init_mach pmap m tp m' f arg),
      containsThread tp i ->
      i = 0.
  Proof.
    intros.
    simpl in Hinit.
    unfold DryHybridMachine.init_mach in *.
    destruct Hinit as (? & Hinit & Hpmap).
    simpl in H. subst.
    unfold OrdinalPool.mkPool in *. simpl in *.
    unfold OrdinalPool.containsThread in *. simpl in *.
    clear - H.
    ssrlia.
  Qed.

  (** [getThreadR] on the initial thread returns the [access_map] that was used
  in [init_mach] and the [empty_map]*)
  Lemma getThreadR_init:
    forall pmap m m' f arg tp
      (Hinit: init_mach pmap m tp m' f arg)
      (cnt: containsThread tp 0),
      getThreadR cnt = getCurPerm m'.
  Proof.
    intros.
    simpl in *.
    unfold DryHybridMachine.init_mach in *.
    destruct Hinit as (? & Hinit & ?); subst.
    reflexivity.
  Qed.

  (** There are no locks in the initial machine *)
  Lemma init_lockRes_empty:
    forall m m' pmap f arg tp laddr
      (Hinit: init_mach pmap m tp m' f arg),
      lockRes tp laddr = None.
  Proof.
    intros.
    simpl in *.
    unfold DryHybridMachine.init_mach in Hinit.
    destruct Hinit as (? & Hinit & ?).
    subst.
    simpl.
    unfold OrdinalPool.mkPool.
    unfold OrdinalPool.lockRes.
    rewrite OrdinalPool.find_empty.
    reflexivity.
  Qed.

  (** The [invariant] holds for the initial state*)
  Lemma initial_invariant:
    forall m m' pmap f arg tp
      (Hinit: init_mach pmap m tp m' f arg),
      invariant tp.
  Proof.
    intros.
    constructor.
    - intros.
      pose proof (init_thread Hinit cnti); subst.
      pose proof (init_thread Hinit cntj); subst.
      exfalso. auto.
    - intros.
      erewrite init_lockRes_empty in Hres1 by eauto.
      discriminate.
    - intros.
      erewrite init_lockRes_empty in Hres by eauto.
      discriminate.
    - intros laddr rmap Hres.
      erewrite init_lockRes_empty in Hres by eauto.
      discriminate.
    - intros b ofs.
      destruct (lockRes tp (b, ofs)) eqn:Hres; auto.
      erewrite init_lockRes_empty in Hres by eauto.
      discriminate.
  Qed.

End ThreadPoolWF.
End ThreadPoolWF.


(** Assumptions on the threadwise semantics of the machine *)

(** ** Lemmas about threadwise semantics*)
Module CoreLanguage.
  Import event_semantics.
    Section CoreLanguage.
      Context {Sem : Semantics}.

      Class SemAxioms :=
        { (** If the [Cur] permission is below [Writable] on some location then
              a thread step cannot change the contents at this location *)
          corestep_unchanged_on:
            forall  c m c' m' b ofs
              (Hstep: corestep (msem semSem) c m c' m')
              (Hvalid: Mem.valid_block m b)
              (Hstable: ~ Mem.perm m b ofs Cur Writable),
              Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
              Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m'));
          (** Memories between thread steps are related by [decay] of permissions*)
          corestep_decay:
            forall c c' m m',
              corestep semSem c m c' m' ->
              decay m m';
          (** [Mem.nextblock] is monotonic with respect to thread steps*)
          corestep_nextblock:
            forall c m c' m',
              corestep semSem c m c' m' ->
              (Mem.nextblock m <= Mem.nextblock m')%positive;
          (** A core cannot be both at external and halted *)
          at_external_halted_excl:
            forall q m, at_external semSem q m = None \/ forall i, ~ halted semSem q i;
          (** If the [Cur] permission is below [Writable] on some location then
              [initial_core] cannot change the contents at this location *)
          initial_core_unchanged_on:
            forall  i v args c m m' b ofs
               (Hstep: initial_core semSem i m c m' v args)
               (Hvalid: Mem.valid_block m b)
               (Hstable: ~ Mem.perm m b ofs Cur Writable),
              Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
              Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m'));
          (** Memories after [initial_core] are related by [decay] of permissions*)
          initial_core_decay:
            forall i v args c m m',
              initial_core semSem i m c m' v args ->
              strong_decay m m';
          (** [Mem.nextblock] is monotonic with respect to [initial_core]*)
          initial_core_nextblock:
            forall i v args c m m',
              initial_core semSem i m c m' v args ->
              (Mem.nextblock m <= Mem.nextblock m')%positive;
        }.
      Class SemDet :=
        { (** The thread semantics are deterministic*)
          corestep_det: corestep_fun semSem;
          (** [initial_core] is deterministic *)
          initial_core_det:
            forall i m v args c c' m' m'',
              initial_core semSem i m c m' v args ->
              initial_core semSem i m c' m'' v args ->
              c = c' /\ m' = m''
        }.

      Context {SemAx : SemAxioms} {SemD : SemDet}.

      Lemma corestep_validblock:
        forall c m c' m',
          corestep semSem c m c' m' ->
          forall b, Mem.valid_block m b ->
               Mem.valid_block m' b.
      Proof.
        intros.
        eapply corestep_nextblock in H.
        unfold Mem.valid_block, Coqlib.Plt in *.
        lia.
      Qed.

      Lemma initial_core_validblock:
        forall i c m m' v args,
          initial_core semSem i m c m' v args ->
          forall b, Mem.valid_block m b ->
               Mem.valid_block m' b.
      Proof.
        intros.
        eapply initial_core_nextblock in H.
        unfold Mem.valid_block, Coqlib.Plt in *.
        lia.
      Qed.

      Definition ev_step_det:
        ev_step_fun semSem ->
        forall (m m' m'' : mem) (c c' c'' : semC) ev ev',
          ev_step semSem c m ev c' m' ->
          ev_step semSem c m ev' c'' m'' -> c' = c'' /\ m' = m'' /\ ev = ev'.
      Proof.
        intro Hfun; intros.
        assert (Hcore := ev_step_ax1 _ _ _ _ _ _ H).
        assert (Hcore' := ev_step_ax1 _ _ _ _ _ _ H0).
        assert (Heq := corestep_det _ _  _ _ _ _ Hcore Hcore').
        destruct Heq; repeat split; auto.
        eapply Hfun; eauto.
      Qed.

      Lemma ev_unchanged_on:
        forall c m c' m' b ofs ev
          (Hstep: ev_step semSem c m ev c' m')
          (Hvalid: Mem.valid_block m b)
          (Hstable: ~ Mem.perm m b ofs Cur Writable),
          Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
          Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m')).
      Proof.
        intros.
        apply ev_step_ax1 in Hstep.
        eapply corestep_unchanged_on;
          now eauto.
      Qed.

      Lemma ev_step_decay:
        forall c c' m m' ev,
          ev_step semSem c m ev c' m' ->
          decay m m'.
      Proof.
        intros.
        apply ev_step_ax1 in H.
        eapply corestep_decay;
          now eauto.
      Qed.

      Lemma ev_step_nextblock:
        forall  c m ev c' m',
          ev_step semSem c m ev c' m' ->
          (Mem.nextblock m <= Mem.nextblock m')%positive.
      Proof.
        intros.
        apply ev_step_ax1 in H.
        eapply corestep_nextblock;
          now eauto.
      Qed.

      Lemma ev_step_validblock:
        forall  c m ev c' m',
          ev_step semSem c m ev c' m' ->
          forall b, Mem.valid_block m b ->
               Mem.valid_block m' b.
      Proof.
        intros.
        eapply ev_step_ax1 in H.
        eapply corestep_nextblock in H.
        unfold Mem.valid_block, Coqlib.Plt in *.
        lia.
      Qed.

    End CoreLanguage.
End CoreLanguage.


(** ** Lemmas about the threadwise semantics with respect to a (dry) concurrent machine*)
Module CoreLanguageDry.
  Import CoreLanguage.
  Import HybridMachine ThreadPool event_semantics HybridMachineSig.

  Section CoreLanguageDry.
    Context {Sem : Semantics}
            {SemAx : SemAxioms}.

    Existing Instance OrdinalPool.OrdinalThreadPool.
    Existing Instance DryHybridMachine.dryResources.
    
    (** Take an instance of the Dry Machine *)
    Existing Instance DryHybridMachine.DryHybridMachineSig.

  (** Lemmas about containsThread and coresteps *)

  Lemma corestep_containsThread:
    forall (tp : t)  c c' m m' p i j ev
      (Hcnti : containsThread tp i)
      (Hcntj: containsThread tp j)
      (Hcorestep: ev_step semSem c m ev c' m')
      (Hcode: getThreadC Hcnti = Krun c),
      containsThread (updThread Hcnti (Krun c') p) j.
  Proof.
    intros.
      by eapply cntUpdate.
  Qed.

  Lemma corestep_containsThread':
    forall (tp : t)  c c' m m' p i j ev
      (Hcnti : containsThread tp i)
      (Hcntj : containsThread (updThread Hcnti (Krun c') p) j)
      (Hcorestep: ev_step semSem c m ev c' m')
      (Hcode: getThreadC Hcnti = Krun c),
      containsThread tp j.
  Proof.
    intros.
      by eapply cntUpdate'; eauto.
  Qed.

  (** *** Lemmas about invariants preserved by coresteps*)

   (** [mem_compatible] is preserved by coresteps*)
  Lemma decay_compatible:
    forall (tp : t)  (m m' : mem) i
      (pf : containsThread tp i) (c': semC)
      (Hinv: invariant tp)
      (Hcompatible : mem_compatible tp m)
      (Hdecay: decay (restrPermMap (DryHybridMachine.compat_th _ _ Hcompatible pf)) m')
      (Hvalid_blocks: forall b, Mem.valid_block m b -> Mem.valid_block m' b), 
      mem_compatible (updThread pf (Krun c') (getCurPerm m')) m'.
  Proof.
    intros.
    constructor.
    (* Thread resources are below the new maximum permissions. *)
    - intros tid cnt.
      assert (cnt0 : containsThread tp tid). by eapply cntUpdate' in cnt; eauto.
      pose proof (DryHybridMachine.compat_th _ _ Hcompatible cnt0) as Hlt.
      intros b ofs.
      destruct (valid_block_dec (restrPermMap (DryHybridMachine.compat_th _ _ Hcompatible pf)) b)
        as [Hvalid | Hinvalid].
      + destruct (Hdecay b ofs) as [_ Hdecay_valid].
        destruct (Hdecay_valid Hvalid) as [Hfreed | Heq].
        (* The block was freed. *)
        * destruct (Hfreed Cur) as [Hfree _].
          destruct (i == tid) eqn:Htid;
            move/eqP:Htid => Htid; subst.
          -- rewrite gssThreadRes.
             apply getCur_Max.
          -- assert (Hp := restrPermMap_Cur (DryHybridMachine.compat_th _ _ Hcompatible pf) b ofs).
             unfold permission_at in Hp.
             rewrite Hp in Hfree.
             pose proof (DryHybridMachine.no_race_thr _ Hinv _ _ pf cnt0 Htid) as Hdisjoint.
             pose proof (Hdisjoint b ofs) as Hunion.
             assert (Hempty : (getThreadR cnt0) # b ofs = None).
             { assert (Hnot_racy : not_racy ((getThreadR cnt0) # b ofs)).
               { eapply no_race_racy with (p1 := (getThreadR pf) # b ofs); eauto.
                 rewrite Hfree.
                 constructor.
               }
               inversion Hnot_racy; auto.
             }
             erewrite gsoThreadRes with (cntj := cnt0) by eauto.
             rewrite Hempty.
             apply po_None.
        (* The relevant permissions did not change. *)
        * destruct (i == tid) eqn:Htid;
            move/eqP:Htid => Htid; subst.
          -- rewrite gssThreadRes.
             apply getCur_Max.
          -- erewrite gsoThreadRes with (cntj := cnt0) by eauto.
             pose proof (Heq Max) as HeqMax.
             pose proof (restrPermMap_Max (DryHybridMachine.compat_th _ _ Hcompatible pf) b ofs)
               as Hrestr_max.
             rewrite getMaxPerm_correct.
             unfold permission_at.
             rewrite <- HeqMax.
             unfold permission_at in Hrestr_max.
             rewrite Hrestr_max.
             exact (Hlt b ofs).
      (* The block was invalid in the old restricted memory. *)
      + apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
        pose proof (restrPermMap_Max (DryHybridMachine.compat_th _ _ Hcompatible pf) b ofs)
          as Hrestr_max.
        unfold permission_at in Hrestr_max.
        rewrite Hrestr_max in Hinvalid.
        destruct (i == tid) eqn:Htid;
          move/eqP:Htid => Htid; subst.
        * rewrite gssThreadRes.
          apply getCur_Max.
        * specialize (Hlt b ofs).
          rewrite Hinvalid in Hlt.
          destruct ((getThreadR cnt0) # b ofs) eqn:Hthread; simpl in Hlt; try contradiction.
          erewrite gsoThreadRes with (cntj := cnt0) by eauto.
          rewrite Hthread.
          apply po_None.
   (* Lock resources are below the new maximum permissions. *)
    - intros laddr rmap Hres.
      change (lockRes tp laddr = Some rmap) in Hres.
      pose proof (DryHybridMachine.compat_lp _ _ Hcompatible laddr rmap Hres) as Hlt.
      intros b ofs.
      destruct (valid_block_dec (restrPermMap (DryHybridMachine.compat_th _ _ Hcompatible pf)) b)
        as [Hvalid | Hinvalid].
      + destruct (Hdecay b ofs) as [_ Hdecay_valid].
        destruct (Hdecay_valid Hvalid) as [Hfreed | Heq].
        (* The block was freed. *)
        * destruct (Hfreed Cur) as [Hfree _].
          assert (Hp := restrPermMap_Cur (DryHybridMachine.compat_th _ _ Hcompatible pf) b ofs).
          unfold permission_at in Hp.
          rewrite Hp in Hfree.
          pose proof (DryHybridMachine.no_race _ Hinv _ _ pf rmap Hres) as Hdisjoint.
          pose proof (Hdisjoint b ofs) as Hunion.
          assert (Hempty : rmap # b ofs = None).
          { assert (Hnot_racy : not_racy (rmap # b ofs)).
            { eapply no_race_racy with (p1 := (getThreadR pf) # b ofs); eauto.
              rewrite Hfree.
              constructor.
            }
            inversion Hnot_racy; auto.
          }
          rewrite Hempty.
          apply po_None.
        (* The relevant permissions did not change. *)
        * pose proof (Heq Max) as HeqMax.
          pose proof (restrPermMap_Max (DryHybridMachine.compat_th _ _ Hcompatible pf) b ofs)
            as Hrestr_max.
          rewrite getMaxPerm_correct.
          unfold permission_at.
          rewrite <- HeqMax.
          unfold permission_at in Hrestr_max.
          rewrite Hrestr_max.
          exact (Hlt b ofs).
      (* The block was invalid in the old restricted memory. *)
      + apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
        pose proof (restrPermMap_Max (DryHybridMachine.compat_th _ _ Hcompatible pf) b ofs)
          as Hrestr_max.
        unfold permission_at in Hrestr_max.
        rewrite Hrestr_max in Hinvalid.
        specialize (Hlt b ofs).
        rewrite Hinvalid in Hlt.
        destruct (rmap # b ofs) eqn:Hrmap; simpl in Hlt; try contradiction.
        apply po_None.
    (* Lock addresses that were valid remain valid. *)
    - intros laddr rmap Hres.
      change (lockRes tp laddr = Some rmap) in Hres.
      apply Hvalid_blocks.
      eapply (DryHybridMachine.lockRes_blocks _ _ Hcompatible); eauto.
  Qed.

  (** [mem_compatible] is preserved by coresteps*)
  Lemma corestep_compatible:
    forall (tp : t)  (m m' : mem) i ev
      (pf : containsThread tp i) (c c': semC)
      (Hinv: invariant tp)
      (Hcode: getThreadC pf = Krun c)
      (Hcompatible : mem_compatible tp m)
      (Hcorestep: ev_step semSem c (restrPermMap (DryHybridMachine.compat_th _ _ Hcompatible pf)) ev c' m'),
      mem_compatible (updThread pf (Krun c') (getCurPerm m')) m'.
  Proof.
    intros.
    assert (Hdecay := ev_step_decay _ _ _ _ _ Hcorestep).
    eapply decay_compatible; eauto.
    intros.
    eapply ev_step_validblock;
      now eauto.
  Qed.

  (** [mem_compatible] is preserved by [initial_core]*)
  Lemma initial_core_compatible:
    forall (tp : t)  (m m' : mem) i n vf arg
      (pf : containsThread tp i) (c: semC)
      (Hinv: invariant tp)
      (Hcompatible : mem_compatible tp m)
      (Hinitial: initial_core semSem n (restrPermMap (DryHybridMachine.compat_th _ _ Hcompatible pf)) c m' vf arg),
      mem_compatible (updThread pf (Krun c) (getCurPerm m')) m'.
  Proof.
    intros.
    assert (Hdecay := initial_core_decay _ _ _ _ _ _ Hinitial).
    eapply strong_decay_implies_decay in Hdecay; eauto.
    eapply decay_compatible; eauto.
    intros.
    eapply initial_core_validblock;
      now eauto.
  Qed.

  (** Permission [decay] preserves disjointness*)
  Lemma decay_disjoint:
    forall m m' p
      (Hdecay: decay m m')
      (Hlt: permMapLt p (getMaxPerm m))
      (Hdisjoint: permMapsDisjoint (getCurPerm m) p),
      permMapsDisjoint (getCurPerm m') p.
  Proof.
    intros.
    unfold permMapsDisjoint in *.
    intros.
    destruct (Hdecay b ofs) as [_ Hold].
    clear Hdecay.
    specialize (Hdisjoint b ofs).
    destruct (valid_block_dec m b) as [Hvalid | Hinvalid].
    - destruct (Hold Hvalid) as [Hfree | Heq].
      + destruct (Hfree Cur) as [_ Hm']. rewrite getCurPerm_correct.
        assert (not_racy (permission_at m' b ofs Cur))
          by (unfold permission_at; rewrite Hm'; constructor).
          by eapply not_racy_union.
      + rewrite getCurPerm_correct. unfold permission_at.
        rewrite <- Heq. rewrite getCurPerm_correct in Hdisjoint.
        unfold permission_at in Hdisjoint. assumption.
    - assert (Hnone: (p # b ofs) = None).
      { apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
        unfold permMapLt in Hlt.
        specialize (Hlt b ofs).
        rewrite getMaxPerm_correct in Hlt.
        unfold permission_at in Hlt.
        rewrite Hinvalid in Hlt. simpl in Hlt.
        destruct (p # b ofs); tauto.
      }
      rewrite Hnone.
      rewrite perm_union_comm.
      eapply not_racy_union;
        by constructor.
  Qed.

  (** [permMapCoherence] is preserved by decay *)
  Lemma decay_coherence :
    forall (m m' : mem) (pmap : access_map)
      (Hdecay: decay m m')
      (Hlt: permMapLt pmap (getMaxPerm m))
      (Hcoh: permMapCoherence (getCurPerm m) pmap),
      permMapCoherence (getCurPerm m') pmap.
  Proof.
    intros.
    intros b ofs.
    destruct (Hdecay b ofs) as [_ Hold]; clear Hdecay.
    (* by case analysis on whether b was a valid block in m*)
    destruct (valid_block_dec m b) as [Hvalid | Hinvalid].
    - (* if b was a valid block*)
      rewrite getCurPerm_correct. unfold permission_at.
      destruct (Hold Hvalid) as [Hfreed | Heq].
      + (* if b was freed*)
        destruct (Hfreed Cur) as [Hfree Hnone].
        rewrite Hnone. simpl.
        specialize (Hcoh b ofs).
        rewrite getCurPerm_correct in Hcoh.
        unfold permission_at in Hcoh.
        rewrite Hfree in Hcoh.
        simpl in Hcoh.
        destruct (pmap # b ofs); [by exfalso | auto].
      + (* if permission on (b,ofs) remained the same*)
        specialize (Heq Cur).
        rewrite <- Heq.
        specialize (Hcoh b ofs).
        rewrite getCurPerm_correct in Hcoh; unfold permission_at in *;
          assumption.
    - (*if b was an invalid block *)
      apply Mem.nextblock_noaccess with (k := Max) (ofs := ofs) in Hinvalid.
      specialize (Hlt b ofs).
      rewrite getMaxPerm_correct in Hlt.
      unfold permission_at in Hlt.
      rewrite Hinvalid in Hlt.
      simpl in Hlt.
      destruct (pmap # b ofs); first by exfalso.
      destruct ((getCurPerm m') # b ofs) as [p|]; auto;
        destruct p; auto.
  Qed.

  Lemma decay_invariant:
    forall tp m m1 m1' i (pf: containsThread tp i) c
      (Hinv : invariant tp)
      (Hcompatible : mem_compatible tp m)
      (Hrestrict_pmap : restrPermMap (Hcompatible i pf) = m1)
      (Hdecay: decay m1 m1'),
      invariant (updThread pf (Krun c) (getCurPerm m1')).
  Proof.
    intros tp m m1 m1' i pf c Hinv Hcompatible Hrestrict_pmap Hdecay.
    subst m1.
    eapply ThreadPoolWF.updThread_inv; eauto.
    (* The new map remains disjoint from other threads. *)
    - intros j cntj Hneq.
      pose proof (DryHybridMachine.no_race_thr _ Hinv i j pf cntj Hneq) as Hdisjoint.
      pose proof (DryHybridMachine.compat_th _ _ Hcompatible cntj) as Hlt.
      eapply decay_disjoint; eauto.
      + unfold permMapLt in *.
        intros b ofs.
        rewrite getMaxPerm_correct.
        rewrite restrPermMap_Max.
        exact (Hlt b ofs).
      + intros b ofs.
        rewrite getCurPerm_correct.
        rewrite restrPermMap_Cur.
        exact (Hdisjoint b ofs).
    (* The new map remains disjoint from lock resources. *)
    - intros laddr rmap Hres.
      pose proof (DryHybridMachine.no_race _ Hinv i laddr pf rmap Hres) as Hdisjoint.
      pose proof (DryHybridMachine.compat_lp _ _ Hcompatible laddr rmap Hres) as Hlt.
      eapply decay_disjoint; eauto.
      + unfold permMapLt in *.
        intros b ofs.
        rewrite getMaxPerm_correct.
        rewrite restrPermMap_Max.
        exact (Hlt b ofs).
      + intros b ofs.
        rewrite getCurPerm_correct.
        rewrite restrPermMap_Cur.
        exact (Hdisjoint b ofs).
    (* The new map remains at most Nonempty at lock addresses. *)
    - intros laddr rmap Hres.
      pose proof (DryHybridMachine.lockRes_blocks _ _ Hcompatible laddr rmap Hres) as Hvalid_block.
      assert (Hvalid_restr : Mem.valid_block (restrPermMap (Hcompatible i pf)) laddr.1).
      {
        eapply restrPermMap_valid; eauto.
      }
      pose proof ((proj1 (DryHybridMachine.locks_data_lock_coh _ Hinv laddr rmap Hres)) i pf)
        as Hold_bound.
      destruct (Hdecay laddr.1 laddr.2) as [_ Hdecay_valid].
      destruct (Hdecay_valid Hvalid_restr) as [Hfreed | Heq].
      + destruct (Hfreed Cur) as [_ Hdrop].
        rewrite getCurPerm_correct.
        unfold permission_at.
        rewrite Hdrop.
        apply po_None.
      + pose proof (Heq Cur) as HeqCur.
        rewrite getCurPerm_correct.
        unfold permission_at.
        rewrite <- HeqCur.
        pose proof (restrPermMap_Cur (Hcompatible i pf) (laddr#1) laddr#2) as HrestrCur.
        unfold permission_at in HrestrCur.
        rewrite HrestrCur.
        exact Hold_bound.
  Qed.
  
 (** [invariant] is preserved by initial_core *)
  Lemma initial_core_invariant:
    forall (tp : t)  (m : mem) (i : nat) n
      (pf : containsThread tp i) c m1 m' vf arg
      (Hinv: invariant tp)
      (Hcompatible: mem_compatible tp m)
      (Hrestrict_pmap: restrPermMap (DryHybridMachine.compat_th _ _ Hcompatible pf) = m1)
      (Hcorestep: initial_core semSem n m1 c m' vf arg),
      invariant (updThread pf (Krun c) (getCurPerm m')).
  Proof.
    intros.
    subst.
    apply initial_core_decay in Hcorestep.
    apply strong_decay_implies_decay in Hcorestep.
    eapply decay_invariant;
      eauto.
  Qed.
  
  (** [invariant] is preserved by a corestep *)
  Lemma corestep_invariant:
    forall (tp : t)  (m : mem) (i : nat)
      (pf : containsThread tp i) c m1 m1' c'
      (Hinv: invariant tp)
      (Hcompatible: mem_compatible tp m)
      (Hrestrict_pmap: restrPermMap (DryHybridMachine.compat_th _ _ Hcompatible pf) = m1)
      (Hcorestep: corestep semSem c m1 c' m1')
      (Hcore: getThreadC pf = Krun c),
      invariant (updThread pf (Krun c') (getCurPerm m1')).
  Proof.
    intros.
    apply corestep_decay in Hcorestep.
    eapply decay_invariant;
      eauto.
  Qed.

  (** A corestep cannot change the contents of memory locations where permission is not above [Readable]*)
  Lemma corestep_stable_val:
    forall  c c' m m' pmap1 pmap2
      (Hlt1: permMapLt pmap1 (getMaxPerm m))
      (Hlt2: permMapLt pmap2 (getMaxPerm m))
      (Hdisjoint: permMapsDisjoint pmap1 pmap2 \/ permMapCoherence pmap1 pmap2)
      (Hstep: corestep semSem c (restrPermMap Hlt1) c' m'),
    forall b ofs (Hreadable: Mem.perm (restrPermMap Hlt2) b ofs Cur Readable),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    (** By disjoitness/coherence it must be that pmap1 has at most [Readable]
      permission on [(b,ofs)]*)
    assert (Hstable: ~ Mem.perm (restrPermMap Hlt1) b ofs Cur Writable).
    { intros Hcontra.
      assert (Hperm1 := restrPermMap_Cur Hlt1 b ofs).
      assert (Hperm2 := restrPermMap_Cur Hlt2 b ofs).
      unfold permission_at, Mem.perm in *.
      rewrite Hperm1 in Hcontra.
      rewrite Hperm2 in Hreadable.
      unfold Mem.perm_order' in *.
      (** Either [pmap1] is disjoint from [pmap2] or there is
        [permMapCoherence] relation between them*)
      destruct Hdisjoint as [Hdisjoint | Hdisjoint];
        specialize (Hdisjoint b ofs);
        destruct (pmap1 # b ofs) as [p1 |];
        destruct (pmap2 # b ofs) as [p2 |]; try (by exfalso);
          destruct p1; (try by inversion Hcontra); destruct p2;
            try (by inversion Hreadable);
            simpl in Hdisjoint; destruct Hdisjoint as [? ?];
              by discriminate.
    }
    apply @corestep_unchanged_on with (b := b) (ofs := ofs) in Hstep; auto.
    erewrite restrPermMap_valid.
    destruct (valid_block_dec m b); auto.
    apply invalid_block_empty with (pmap := pmap2) (ofs := ofs) in n; auto.
    unfold Mem.perm in Hreadable.
    pose proof (restrPermMap_Cur Hlt2 b ofs) as Heq.
    unfold permission_at in Heq.
    rewrite Heq in Hreadable.
    rewrite n in Hreadable.
    simpl; by exfalso.
  Qed.

  (** If some thread has permission above readable on some address then
    stepping another thread cannot change the value of that location*)
  Corollary corestep_disjoint_locks :
    forall (tp : t) (m m' : mem) i (c c' : semC) (pfi : containsThread tp i) (Hcomp : mem_compatible tp m) laddr rmap (Hres : lockRes tp laddr = Some rmap) (b : block) (ofs : Z)
           (Hreadable : Mem.perm (restrPermMap (DryHybridMachine.compat_lp _ _ Hcomp laddr rmap Hres)) b ofs Cur Readable)
           (Hcorestep : corestep semSem c (restrPermMap(DryHybridMachine.compat_th _ _ Hcomp pfi)) c' m') (Hinv : invariant tp),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    eapply corestep_stable_val; eauto.
    left.
    exact
      (DryHybridMachine.no_race
         tp Hinv i laddr pfi rmap Hres).
  Qed.

  (** If some lock has permission above [Readable] on some address then
    stepping a thread cannot change the value of that location*)
  Lemma corestep_disjoint_val_lockpool :
    forall (tp : t)  (m m' : mem) i (c c' : semC)
      (pfi : containsThread tp i) (Hcomp : mem_compatible tp m) addr pmap
      (Hlock: lockRes tp addr = Some pmap)
      (b : block) (ofs : Z)
      (Hreadable: Mem.perm (restrPermMap (DryHybridMachine.compat_lp _ _ Hcomp _ _ Hlock))
                           b ofs Cur Readable)
      (Hcorestep: corestep semSem c (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfi)) c' m')
      (Hinv: invariant tp),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    eapply corestep_stable_val; eauto.
    left.
    exact (DryHybridMachine.no_race tp Hinv i addr pfi pmap Hlock).
  Qed.

  Lemma initial_core_stable_val:
    forall  n c m m' pmap1 pmap2 v arg
      (Hlt1: permMapLt pmap1 (getMaxPerm m))
      (Hlt2: permMapLt pmap2 (getMaxPerm m))
      (Hdisjoint: permMapsDisjoint pmap1 pmap2 \/ permMapCoherence pmap1 pmap2)
      (Hstep: initial_core semSem n (restrPermMap Hlt1) c m' v arg),
    forall b ofs (Hreadable: Mem.perm (restrPermMap Hlt2) b ofs Cur Readable),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    (** By disjoitness/coherence it must be that pmap1 has at most [Readable]
      permission on [(b,ofs)]*)
    assert (Hstable: ~ Mem.perm (restrPermMap Hlt1) b ofs Cur Writable).
    { intros Hcontra.
      assert (Hperm1 := restrPermMap_Cur Hlt1 b ofs).
      assert (Hperm2 := restrPermMap_Cur Hlt2 b ofs).
      unfold permission_at, Mem.perm in *.
      rewrite Hperm1 in Hcontra.
      rewrite Hperm2 in Hreadable.
      unfold Mem.perm_order' in *.
      (** Either [pmap1] is disjoint from [pmap2] or there is
        [permMapCoherence] relation between them*)
      destruct Hdisjoint as [Hdisjoint | Hdisjoint];
        specialize (Hdisjoint b ofs);
        destruct (pmap1 # b ofs) as [p1 |];
        destruct (pmap2 # b ofs) as [p2 |]; try (by exfalso);
          destruct p1; (try by inversion Hcontra); destruct p2;
            try (by inversion Hreadable);
            simpl in Hdisjoint; destruct Hdisjoint as [? ?];
              by discriminate.
    }
    apply @initial_core_unchanged_on with (b := b) (ofs := ofs) in Hstep; auto.
    erewrite restrPermMap_valid.
    destruct (valid_block_dec m b); auto.
    apply invalid_block_empty with (pmap := pmap2) (ofs := ofs) in n0; auto.
    unfold Mem.perm in Hreadable.
    pose proof (restrPermMap_Cur Hlt2 b ofs) as Heq.
    unfold permission_at in Heq.
    rewrite Heq in Hreadable.
    rewrite n0 in Hreadable.
    simpl; by exfalso.
  Qed.

    Corollary initial_core_disjoint_val:
    forall (tp : t)  (m m' : mem) i j (Hneq: i <> j) n v arg
      (c c' : semC)
      (pfi : containsThread tp i) (pfj : containsThread tp j)
      (Hcomp : mem_compatible tp m) (b : block) (ofs : Z)
      (Hreadable: Mem.perm (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfj)) b ofs Cur Readable)
      (Hcorestep: initial_core semSem n (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfi)) c m' v arg)
      (Hinv: invariant tp),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    eapply initial_core_stable_val; eauto.
    left.
    exact
      (DryHybridMachine.no_race_thr
         tp Hinv i j pfi pfj Hneq).
  Qed.

  Corollary initial_core_disjoint_locks :
    forall (tp : t) (m m' : mem) i (c : semC) n v arg (pfi : containsThread tp i)
      (Hcomp : mem_compatible tp m) addr pmap (Hlock : lockRes tp addr = Some pmap) (b : block) (ofs : Z)
      (Hreadable : Mem.perm (restrPermMap (DryHybridMachine.compat_lp _ _ Hcomp addr pmap Hlock))
               b ofs Cur Readable)
      (Hcorestep :initial_core semSem n (restrPermMap (DryHybridMachine.compat_th
                                                         _ _ Hcomp pfi)) c m' v arg)
           (Hinv : invariant tp),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    eapply initial_core_stable_val; eauto.
    left.
    exact
      (DryHybridMachine.no_race
         tp Hinv i addr pfi pmap Hlock).
  Qed.

  (** If some lock has permission above [Readable] on some address then
    stepping a thread cannot change the value of that location*)
  Lemma initial_core_disjoint_val_lockpool :
    forall (tp : t)  (m m' : mem) i (c c' : semC) n v arg
      (pfi : containsThread tp i) (Hcomp : mem_compatible tp m) addr pmap
      (Hlock: lockRes tp addr = Some pmap)
      (b : block) (ofs : Z)
      (Hreadable: Mem.perm (restrPermMap (DryHybridMachine.compat_lp _ _ Hcomp _ _ Hlock))
                           b ofs Cur Readable)
      (Hcorestep: initial_core semSem n (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfi)) c m' v arg)
      (Hinv: invariant tp),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    eapply initial_core_stable_val; eauto.
    left.
    exact (DryHybridMachine.no_race tp Hinv i addr pfi pmap Hlock).
  Qed.

  Lemma permMapLt_decay:
    forall pmap m m'
      (Hdecay: strong_decay m m')
      (Hlt: permMapLt pmap (getMaxPerm m)),
      permMapLt pmap (getMaxPerm m').
  Proof.
    intros.
    intros b ofs.
    destruct (Hdecay b ofs) as [Hfresh Hold].
    specialize (Hlt b ofs).
    erewrite getMaxPerm_correct in *.
    unfold permission_at in *. 
    destruct (valid_block_dec m b).
    - specialize (Hold v).
      erewrite <- Hold.
      assumption.
    - eapply Mem.nextblock_noaccess with (k := Max) (b:= b) (ofs := ofs) in n.
      rewrite n in Hlt.
      simpl in Hlt.
      destruct (pmap # b ofs); [now exfalso|].
      destruct ((Mem.mem_access m') # b ofs Max); simpl;
        now auto.
  Qed.
    
  End CoreLanguageDry.
End CoreLanguageDry.
