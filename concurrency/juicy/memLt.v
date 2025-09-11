(* Instead of deriving a juicy-machine execution from the CSL proof, we derive a dry-machine execution
   directly, along the lines of the sequential adequacy proof (veric/SequentialClight). *)
Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.veric.external_state.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax_prog.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.SequentialClight.
Require Import VST.veric.Clight_evsem.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.canon.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.extspec.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.concurrency.juicy.semax_conc.
(*Require Import VST.concurrency.juicy.juicy_machine.*)
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.ClightSemanticsForMachines.
(*Require Import VST.concurrency.juicy.JuicyMachineModule.
Require Import VST.concurrency.juicy.sync_preds_defs.
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.juicy.join_lemmas.
Require Import VST.concurrency.juicy.semax_invariant.
Require Import VST.concurrency.juicy.semax_initial.
Require Import VST.concurrency.juicy.semax_progress.
Require Import VST.concurrency.juicy.semax_preservation_jspec.
Require Import VST.concurrency.juicy.semax_safety_makelock.
Require Import VST.concurrency.juicy.semax_safety_spawn.
Require Import VST.concurrency.juicy.semax_safety_release.
Require Import VST.concurrency.juicy.semax_safety_freelock.
Require Import VST.concurrency.juicy.semax_preservation.
Require Import VST.concurrency.juicy.semax_simlemmas.*)
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.dry_machine_step_lemmas.
Import ThreadPool.

Set Bullet Behavior "Strict Subproofs".

  (*
    Hlt : permMapLt max (getMaxPerm m)

    m1 = (getCurPerm m) 
    m2 = (getCurPerm (restrPermMap Hlt))

   *)
  Definition memLt m1 m2 := permMapLt (getCurPerm m1) (getCurPerm m2) /\
                              Mem.mem_contents m1 = Mem.mem_contents m2 /\
                              Mem.nextblock m1 = Mem.nextblock m2.

  Lemma memPerm_order_permMapLt m1 m2:
    permMapLt (getCurPerm m1) (getCurPerm m2) ->
    ∀ (b : block) (ofs : Z) (p : permission),
      Mem.perm_order' ((Mem.mem_access m1) # b ofs Cur) p →
      Mem.perm_order' ((Mem.mem_access m2) # b ofs Cur) p.
  Proof.
    rewrite /Mem.perm_order' /getCurPerm.
    intros HpermLt b???.
    specialize (HpermLt b ofs).
    rewrite ! Maps.PMap.gmap in HpermLt.
    destruct ((Mem.mem_access m2) # b ofs Cur);
      destruct ((Mem.mem_access m1) # b ofs Cur); try contradiction.
    eapply perm_order_trans; eauto.
  Qed.

  Lemma memPerm_permMapLt m1 m2:
    permMapLt (getCurPerm m1) (getCurPerm m2) ->
    ∀ (b : block) (ofs : Z) (p : permission),
      Mem.perm m1 b ofs Cur p → Mem.perm m2 b ofs Cur p.
  Proof. eapply memPerm_order_permMapLt. Qed.

  Lemma range_perm_memLt m1 m2 (Hp : permMapLt (getCurPerm m1) (getCurPerm m2)):
    ∀ (b : block) (ofs : Z) (p : permission) len,
    Mem.range_perm m1 b ofs (ofs + len) Cur p ->
      Mem.range_perm m2 b ofs (ofs + len) Cur p.
  Proof.
    unfold Mem.range_perm, Mem.perm in *.
    intros ?????Hperm??Hofs.
    specialize ((Hperm ofs0) Hofs).
    eapply memPerm_order_permMapLt; eauto.
  Qed.
  
  Lemma memLt_valid_pointer:
    forall m1 m2 b z, 
      memLt m1 m2 ->
      Mem.valid_pointer m1 b z = true ->
      Mem.valid_pointer m2 b z = true.
  Proof.
    intros.
    destruct H as [? [? ?]].
    unfold Mem.valid_pointer in *.
    destruct (Mem.perm_dec m1 b z Cur Nonempty); inv H0.
    destruct (Mem.perm_dec m2 b z Cur Nonempty); try reflexivity.
    contradiction n. clear n.
    eapply memPerm_permMapLt; eauto.
  Qed.

  Lemma memLt_weak_valid_pointer:
    forall m1 m2 b z,
      memLt m1 m2 -> Mem.weak_valid_pointer m1 b z = true -> Mem.weak_valid_pointer m2 b z = true.
  Proof.
    intros; unfold Mem.weak_valid_pointer in *.
    rewrite -> orb_true_iff in *.
    destruct H0; [left|right]; eapply memLt_valid_pointer; eauto.
  Qed.

  Lemma mem_sub_loadbytes :
    forall m1 m2 b ofs len v,
      memLt m1 m2 -> Mem.loadbytes m1 b ofs len = Some v -> Mem.loadbytes m2 b ofs len = Some v.
  Proof.
    Transparent Mem.loadbytes.
    unfold Mem.loadbytes; intros.
    destruct H as [? [? ?]].
    if_tac in H0; inv H0.
    rewrite if_true; auto.
    rewrite H1; auto.
    eapply range_perm_memLt; eauto.
  Qed.
  
  (*
  Lemma unaryop_mem_lessdef {op u t m v m2}
    (V: Cop.sem_unary_operation op u t m = Some v)
    (M : memLt m m2):
    Cop.sem_unary_operation op u t m2 = Some v.
  Proof. destruct op; simpl; inv V; try econstructor.
         unfold sem_notbool, bool_val in *.
         remember (classify_bool t) as c.
         destruct c; trivial.
         destruct u; trivial.
         simple_if_tac; trivial.
         destruct (Mem.weak_valid_pointer m _ _) eqn: Hm; inv H0.
         rewrite (mem_lessdef_weak_valid_pointer _ _ _ _ M); trivial.
  Qed.
*)

  Lemma unaryop_memLt {op u t m v m2}
    (V : Cop.sem_unary_operation op u t m = Some v)
    (M : memLt m m2):
    Cop.sem_unary_operation op u t m2 = Some v.
  Proof.
    rewrite /Cop.sem_unary_operation in V |-*.
    destruct op; simpl; inv V; try econstructor.
    rewrite /Cop.sem_notbool /Cop.bool_val in H0 |-*.
    remember (Cop.classify_bool t) as c.
    destruct c; auto.
    destruct u; auto.
    simple_if_tac; auto.
    destruct (Mem.weak_valid_pointer m _ _) eqn: Hm; inv H0.
    rewrite (memLt_weak_valid_pointer _ _ _ _ M); auto.
  Qed.
  
  Lemma sem_cast_memLt {v t d m m2 v'} (M : memLt m m2):
    Cop.sem_cast v t d m = Some v' -> Cop.sem_cast v t d m2 = Some v'.
  Proof.
    unfold Cop.sem_cast; intros.
    destruct (Cop.classify_cast t d); trivial.
    destruct v; trivial.
    simple_if_tac; trivial.
    destruct (Mem.weak_valid_pointer m _ _) eqn: Hm; inv H.
    rewrite (memLt_weak_valid_pointer _ _ _ _ M); trivial.
  Qed.
  
  Lemma sem_binarith_memLt {f1 f2 f3 f4 v1 t1 v2 t2 v' m m2} (M : memLt m m2):
    Cop.sem_binarith f1 f2 f3 f4 v1 t1 v2 t2 m = Some v' ->
    Cop.sem_binarith f1 f2 f3 f4 v1 t1 v2 t2 m2 = Some v'.
  Proof.
    unfold Cop.sem_binarith; intros.
    destruct (Cop.sem_cast v1 t1 _ m) eqn: Hcast1; inv H.
    destruct (Cop.sem_cast v2 t2 _ m) eqn: Hcast2; inv H1.
    erewrite !(sem_cast_memLt  M); eauto.
  Qed.

  Lemma cmplu_bool_memLt {v1 v2 f b m m2} (M : memLt m m2):
    Val.cmplu_bool (Mem.valid_pointer m) f v1 v2 = Some b ->
    Val.cmplu_bool (Mem.valid_pointer m2) f v1 v2 = Some b.
  Proof.
    unfold Val.cmplu_bool; intros. forget Archi.ptr64 as ptr64.
    destruct v1, v2; trivial; simple_if_tac; inv H;
    repeat match goal with H:
        context[if ?b then _ else _] |- _ =>
            destruct b eqn: ?Hb; inv H;
            try apply andb_true_iff in Hb as [-> Hp];
            try (rewrite orb_true_iff in Hp; destruct Hp as [Hp | Hp];
                 rewrite (memLt_valid_pointer _ _ _ _ M Hp); rewrite ?orb_true_r; auto) end.
    * apply andb_true_iff in Hb0 as [Hp1 Hp2].
      apply orb_true_iff in Hp1 as [Hp1 | Hp1]; apply orb_true_iff in Hp2 as [Hp2 | Hp2];
        rewrite (memLt_valid_pointer _ _ _ _ M Hp1);
        rewrite (memLt_valid_pointer _ _ _ _ M Hp2);
        rewrite ?orb_true_r; auto.
    * apply andb_true_iff in Hb0 as [Hp1 Hp2].
      rewrite (memLt_valid_pointer _ _ _ _ M Hp1);
      rewrite (memLt_valid_pointer _ _ _ _ M Hp2); auto.
   Qed.
  
  Lemma cmp_ptr_memLt {v1 v2 f b m m2} (M : memLt m m2):
    Cop.cmp_ptr m f v1 v2 = Some b -> Cop.cmp_ptr m2 f v1 v2 = Some b.
  Proof.
    unfold Cop.cmp_ptr; simple_if_tac;
      destruct (Val.cmplu_bool (Mem.valid_pointer m) f v1 v2) eqn: Hcmp;
      intros H; inv H; try rewrite (cmplu_bool_memLt M Hcmp); auto.
  Qed.
  
  Lemma sem_cmp_memLt {f v1 t1 v2 t2 b m m2} (M : memLt m m2):
    Cop.sem_cmp f v1 t1 v2 t2 m = Some b -> Cop.sem_cmp f v1 t1 v2 t2 m2 = Some b.
  Proof.
    unfold Cop.sem_cmp; intros.
    destruct (Cop.classify_cmp t1 t2);
      try match goal with H : match v1 with _ => _ end = Some _ |- _ => destruct v1; inv H end;
      try match goal with H : context[match v2 with _ => _ end] |- _ => destruct v2; inv H end;
      try (simple_if_tac; trivial);
      try match goal with H : Cop.cmp_ptr _ _ _ _ = _ |- _ => rewrite ?H;
                                                        rewrite ?(cmp_ptr_memLt M H); trivial end.
    eapply sem_binarith_memLt; eauto.
  Qed.

  Lemma binaryop_memLt {ge op v1 t1 v2 t2 m v m2}
    (V: Cop.sem_binary_operation ge op v1 t1 v2 t2 m = Some v)
    (M: memLt m m2):
    Cop.sem_binary_operation ge op v1 t1 v2 t2 m2 = Some v.
  Proof.
    destruct op; simpl; inv V; try econstructor.
    + rewrite /Cop.sem_add in H0 |-*.
      remember (Cop.classify_add t1 t2) as c.
      destruct c.
      destruct v1; auto. destruct v1; auto. destruct v1; auto. destruct v1; auto.
      simpl.
      erewrite sem_binarith_memLt; eauto.
    + unfold Cop.sem_sub in *.
      remember (Cop.classify_sub t1 t2) as c.
      destruct c.
      destruct v1; trivial. destruct v1; trivial. destruct v1; trivial.
      erewrite sem_binarith_memLt; eauto.
    + unfold Cop.sem_mul in *. erewrite sem_binarith_memLt; eauto.
    + unfold Cop.sem_div in *. erewrite sem_binarith_memLt; eauto.
    + unfold Cop.sem_mod in *. erewrite sem_binarith_memLt; eauto.
    + unfold Cop.sem_and in *. erewrite sem_binarith_memLt; eauto.
    + unfold Cop.sem_or  in *. erewrite sem_binarith_memLt; eauto.
    + unfold Cop.sem_xor in *. erewrite sem_binarith_memLt; eauto.
    + erewrite sem_cmp_memLt; eauto.
    + erewrite sem_cmp_memLt; eauto.
    + erewrite sem_cmp_memLt; eauto.
    + erewrite sem_cmp_memLt; eauto.
    + erewrite sem_cmp_memLt; eauto.
    + erewrite sem_cmp_memLt; eauto.
  Qed.

  Lemma memLt_loadbytes : forall m1 m2 b ofs len v,
      memLt m1 m2 ->
      Mem.loadbytes m1 b ofs len = Some v -> Mem.loadbytes m2 b ofs len = Some v.
  Proof.
    Transparent Mem.loadbytes.
    rewrite /Mem.loadbytes; intros.
    if_tac in H0; inv H0.
    destruct H as (HpermLt & ? & ?).
    assert ( ∀ (b0 : block) (ofs : Z) (p : permission),
               Mem.perm m1 b0 ofs Cur p → Mem.perm m2 b0 ofs Cur p) as Hmem.
    { eapply memPerm_permMapLt; auto. }
    rewrite if_true; auto.
    2 :{ intros ??; auto. }
    do 2 f_equal.
    rewrite H; auto.
  Qed.

  Lemma eval_expr_eval_lvalue_memLt ge ve te m:
     (forall (e : expr) (v : val),
        eval_expr ge ve te m e v ->
        forall m2 : mem, memLt m m2 -> eval_expr ge ve te m2 e v) /\
     (forall (e : expr) (b : block) (i : ptrofs) (bf: bitfield),
        eval_lvalue ge ve te m e b i bf ->
        forall m2 : mem, memLt m m2 -> eval_lvalue ge ve te m2 e b i bf).
Proof.
  apply eval_expr_lvalue_ind; intros; try solve [econstructor; eauto].
  + econstructor; eauto.
    eapply unaryop_memLt; eauto.
  + econstructor; eauto. eapply binaryop_memLt; eauto.
  + econstructor; eauto. rewrite <- H1. symmetry.
    rewrite H1. symmetry. eapply sem_cast_memLt; eauto.
  + econstructor; eauto.
    destruct H2 as [M1 [M2 M3]].
    inv H1; simpl in *.
  - eapply deref_loc_value; eauto.
    simpl.
    destruct (Mem.load_loadbytes _ _ _ _ _ H3) as [vals [X Y]]; subst.
    apply Mem.load_valid_access in H3.
    destruct H3.
    eapply Mem.loadbytes_load; trivial.
    eapply memLt_loadbytes; eauto.
    repeat split; auto.
  - apply deref_loc_reference; trivial.
  - apply deref_loc_copy; trivial.
  - apply deref_loc_bitfield; auto.
     inv H2. econstructor; eauto.
    destruct (Mem.load_loadbytes _ _ _ _ _ H7) as [vals [X Y]]; subst.
    apply Mem.load_valid_access in H7. destruct H7.
    unfold Mem.loadv.
    rewrite Y.
    eapply Mem.loadbytes_load; trivial.
    eapply memLt_loadbytes; eauto.
    repeat split; auto.
  Qed.

(* veric.Clight_evsem *)
Transparent Mem.storebytes.

Lemma storebytes_sub:
  forall m1 m2 b ofs bytes m1',
    memLt m1 m2 ->
    Mem.storebytes m1 b ofs bytes = Some m1' ->
    exists m2',
      Mem.storebytes m2 b ofs bytes = Some m2'
      /\ memLt m1' m2'.
Proof.
  unfold Mem.storebytes; intros.
  destruct H as (? & ? & ?).
  if_tac in H0; inv H0.
  eexists.
  rewrite -> if_true; last first.
  { unfold Mem.range_perm, Mem.perm in *.
    intros; specialize ((H3 ofs0) H0).
    eapply memPerm_order_permMapLt; eauto.
  }
  split; auto.
  rewrite /memLt /=.
  do 2 (split; auto).
  rewrite H1; auto.
Qed.


Lemma assign_locT_sub_memLt:
  forall ce ty m b ofs bf v m' T m1,
    assign_locT ce ty m b ofs bf v m' T ->
    memLt m m1 -> exists m1', memLt m' m1' /\ assign_locT ce ty m1 b ofs bf v m1' T.
Proof.
  inversion 1; subst; intros.
  - exploit Mem.store_valid_access_3; eauto; intros [].
    eapply Mem.store_storebytes, storebytes_sub in H1 as (? & ? & ?); eauto.
    do 2 eexists; eauto; constructor; auto.
    apply Mem.storebytes_store; auto.
  - eapply mem_sub_loadbytes in H4; eauto.
    eapply storebytes_sub in H5 as (? & ? & ?); eauto.
    do 2 eexists; eauto; constructor; auto.
  - inv H0.
    eapply mem_sub_loadbytes in H7; eauto.
    eapply Mem.store_storebytes, storebytes_sub in H9 as (? & ? & ?); eauto.
    do 2 eexists; eauto; econstructor; constructor; eauto.
    apply Mem.storebytes_store; eauto.
Qed.
