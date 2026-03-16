theory Stack
  imports Failure
begin

text \<open>
  This is Bornat, Calcagno, and Yang's [BCY2005] "Variables as a Resouce" model.

  This is related, but not quite the same, as Iris' "authoratative" model.
\<close>

section \<open> Store \<close>

typedef ('x, 'v) store = \<open>UNIV :: ('x set \<times> ('x \<Rightarrow> 'v)) set\<close> ..

setup_lifting type_definition_store

lift_definition owned_vars_store :: \<open>('x, 'v) store \<Rightarrow> 'x set\<close> is \<open>fst\<close> .
lift_definition lookup_store :: \<open>('x, 'v) store \<Rightarrow> 'x \<Rightarrow> 'v\<close> is \<open>snd\<close> .

text \<open>
  The store is updated only if the variables changed in the update are from the mutable-variable
  set.
\<close>
lift_definition update_store :: \<open>(('x \<Rightarrow> 'v) \<Rightarrow> ('x \<Rightarrow> 'v)) \<Rightarrow> ('x, 'v) store \<Rightarrow> ('x, 'v) store\<close> is
  \<open>\<lambda>f (X, s). if \<forall>x\<in>-X. s x = f s x then (X, f s) else (X, s)\<close> .


lift_definition SVars :: \<open>'x set \<Rightarrow> (('x, 'v) store \<Rightarrow> bool)\<close> is
  \<open>\<lambda>X (Xa, sa). X = Xa\<close> .


subsection \<open> Instances \<close>

instantiation store :: (type, type) disjoint
begin
lift_definition disjoint_store :: \<open>('x, 'v) store \<Rightarrow> ('x, 'v) store \<Rightarrow> bool\<close> is
  \<open>\<lambda>(Xa, sa) (Xb, sb).  Xa \<inter> Xb = {} \<and> sa = sb\<close> .
instance by standard
end

instantiation store :: (type, type) plus
begin
lift_definition plus_store :: \<open>('x, 'v) store \<Rightarrow> ('x, 'v) store \<Rightarrow> ('x, 'v) store\<close> is
  \<open>\<lambda>(Xa, s) (Xb, _).  (Xa \<union> Xb, s)\<close> .
instance by standard
end

instance store :: (type, type) pre_perm_alg
  by standard (transfer, force)+

instantiation store :: (type, type) unitof
begin
lift_definition unitof_store :: \<open>('x, 'v) store \<Rightarrow> ('x, 'v) store\<close> is
  \<open>\<lambda>(_, s). ({}, s)\<close> .
instance by standard
end

instance store :: (type, type) pre_multiunit_sep_alg
  by standard (transfer, clarsimp)+

(* not a sep_alg *)

instance store :: (type, type) positivity_law
  by standard (transfer, force)+

instance store :: (type, type) cancel_pre_perm_alg
  by standard (transfer, force)+

(* not allcompatible_perm_alg *)

instance store :: (type, type) strong_sep_pre_perm_alg
  by standard
    (clarsimp simp add: sepadd_unit_def, transfer, clarsimp)+

instance store :: (type, type) disjoint_parts_pre_perm_alg
  by standard (transfer, force)

instance store :: (type, type) trivial_selfdisjoint_pre_perm_alg
  by standard (transfer, force)

instance store :: (type, type) crosssplit_pre_perm_alg
  apply standard
  apply transfer
  apply (clarsimp simp add: ex_simps(1-4)[symmetric] simp del: ex_simps(1-4))
  apply (frule sup_crosssplit)
  apply (clarsimp simp add: ex_simps(1-4)[symmetric] simp del: ex_simps(1-4))
  apply (rename_tac ax bx ay "by")
  apply (metis (mono_tags, lifting) Un_empty inf_sup_distrib1 inf_sup_distrib2)
  done

(* As stores are cancel and positive, this is obviously true. *)
instance store :: (type, type) dupcl_perm_alg
  by standard (transfer, force)


section \<open> Commands & Proof Rules \<close>

subsection \<open> Read \<close>

text \<open> x := e \<close>
definition store_read_rel
  :: \<open>'x \<Rightarrow> (('x \<Rightarrow> 'v) \<times> 's \<Rightarrow> 'v) \<Rightarrow> (('x, 'v) store \<times> fail_st) \<times> 's \<Rightarrow> _ \<Rightarrow> bool\<close>
  where
    \<open>store_read_rel x e \<equiv>
      \<lambda>((st,fl),ss) ((st',fl'), ss').
        ss' = ss \<and>
          (fl = Running \<and> x \<in> owned_vars_store st \<and> fl' = Running \<and>
            st' = update_store (\<lambda>m. m(x := e (m, ss))) st \<or>
            (fl = Failed \<or> x \<notin> owned_vars_store st) \<and> st' = st \<and> fl' = Failed)\<close>

abbreviation
  \<open>StoreRead x e \<equiv> \<langle> store_read_rel x e \<rangle>\<close>

lemma rgsat_store_read:
  fixes x p xx
  defines \<open>precond \<equiv> \<L> (SVars {x}) \<^emph>\<and> \<S> p\<close>
  defines \<open>postcond \<equiv> \<L> (SVars {x}) \<^emph>\<and> \<lceil> \<lambda>ss. \<L> xx \<rceil>\<^sub>\<S> \<^emph>\<and> \<S> p\<close>
  assumes
    \<open>(=) \<le> G\<close>
    \<open>wssa R precond \<le> I\<close>
    \<open>sswa R postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
    and frame_cond:
    \<open>F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> undefined\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { wssa R precond } StoreRead x e { sswa R postcond }\<close>
  using assms
proof (intro rgsat_atom[where p=\<open>nofailure_pred precond\<close> and q=\<open>nofailure_pred postcond\<close>])
  let ?ra = \<open>(\<lambda>(ls, ss) (ls', ss'). ls' = ls \<and> (\<exists>v. ls pt = Some v \<and> ss' = ss(x := u2v v)))\<close>

  have nofailure_helper:
    \<open>\<And>f. sp (heap_read_rel u2v x pt) (nofailure_pred (wssa R precond \<^emph>\<and> f)) \<le> nofailure_pred \<top>\<close>
    apply (clarsimp simp add: heap_read_rel_def sp_def)
    apply (elim disjE, force)
    apply (force simp add: precond_def wlp_def val_at_def points_to_def sepconj_conj_def
        plus_option_iff)
    done
  have rel_helper:
    \<open>(heap_read_rel u2v x pt \<circ>\<^sub>2 (\<lambda>(x, y). ((x, Running), y))) = ?ra\<close>
    by (force simp add: heap_read_rel_def fun_eq_iff)

  let ?frame2 = \<open>\<forall>f\<le>F. sp ?ra (wssa R precond \<^emph>\<and> f) \<le> postcond \<^emph>\<and> any_shared f\<close>
  let ?frame1 =
    \<open>\<forall>f\<le>nofailure_pred F. sp (heap_read_rel u2v x pt) (wssa R (nofailure_pred precond) \<^emph>\<and> f) \<le>
      nofailure_pred postcond \<^emph>\<and> any_shared f\<close>

  have \<open>\<top> = (F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> frame_post)\<close>
    using frame_cond
    by simp
  also have \<open>... = ?frame2\<close>
    apply (clarsimp simp add: le_fun_def sp_def imp_ex_conjL imp_conjL sepconj_conj_def
        septract_conj_def)
    apply (intro iffI impI allI)
      (* \<Rightarrow> *)
     apply (rename_tac f lfs v ss ls fs)
     apply (drule spec2, drule mp, fast)
     apply (drule spec, drule mp, rule disjoint_sym, assumption, drule mp, assumption)
     apply (clarsimp simp add: precond_def postcond_def)
     apply (simp add: wlp_def val_at_def points_to_def frame_post_def
        plus_option_iff disjoint_option_iff)
     apply (subgoal_tac \<open>ls pt = Some (e ss) \<and> (\<forall>pt'. pt' \<noteq> pt \<longrightarrow> ls pt' = None)\<close>)
      prefer 2
      apply (metis fun_upd_other fun_upd_same rtranclp.rtrancl_refl)
     apply clarsimp
     apply (elim disjE conjE exE)
      (* ls:Some/fs:None *)
      apply fastforce
      (* h:Some/f:Some *)
     apply (rule_tac x=fs in exI)
     apply (rule conjI, force)
     apply (rule conjI, force)
     apply (rule conjI[rotated], force)
     apply (force simp add: val_at_heap_def)
      (* \<Leftarrow> *)
    apply (rename_tac fs ss ls)
    apply (drule_tac x=\<open>(=) (fs, ss)\<close> in spec, drule mp, fast)
    apply (subgoal_tac \<open>ls = [pt \<mapsto> e ss]\<close>)
     prefer 2
     apply (fastforce simp add: precond_def wlp_def points_to_def)
    apply (case_tac \<open>fs pt\<close>)
      (** \<open>fs pt = None\<close> *)
     apply (simp add: frame_post_def val_at_heap_def; fail)
      (** \<open>fs pt = Some ...\<close> *)
    apply (rename_tac vf)
    apply (drule_tac x=\<open>ls + fs\<close> and y=\<open>e ss + vf\<close> in spec2, drule mp, force)
    apply clarsimp
    apply (drule_tac x=\<open>[pt \<mapsto> e ss]\<close> in spec)
    apply (simp add: postcond_def frame_post_def)
    apply (clarsimp simp add: disjoint_sym_iff val_at_heap_def points_to_def fun_eq_iff
        plus_option_iff if_distrib[of \<open>\<lambda>x. x = _\<close>] if_distrib[of \<open>\<lambda>x. x + _ = _\<close>] if_bool_eq_conj
        all_conj_distrib eq_commute[of _ \<open>_ pt\<close>])
    done
  also have \<open>... = ?frame1\<close>
    apply (simp add: wssa_comp_ppABC_to_ppACB_distrib)
    apply (simp add: all_subpred_pred_times_eq_res_ppABC_to_ppACB_internalise
        nofailure_pred_sepconj_conj_distrib[symmetric]
        any_shared_pred_times_eq_res_ppABC_to_ppACB_distrib pred_times_le_iff)
    apply (subst sp_nofailure_pred_in_out_iff)
    apply (simp add: nofailure_helper rel_helper)
    done
  finally show
    \<open>\<forall>f\<le>nofailure_pred F. sp (heap_read_rel u2v x pt) (wssa R (nofailure_pred precond) \<^emph>\<and> f) \<le>
      nofailure_pred postcond \<^emph>\<and> any_shared f\<close>
    unfolding any_shared_def precond_def postcond_def
    by simp

  show \<open>rel_image snd (rel_liftL (wssa R (nofailure_pred precond) \<^emph>\<and>
          nofailure_pred F) \<sqinter> heap_read_rel u2v x pt) \<le> G\<close>
    using assms(5)
    unfolding heap_read_G_def precond_def
    apply (fastforce simp add: wssa_comp_ppABC_to_ppACB_distrib heap_read_rel_def sepconj_conj_def
        plus_option_iff ex_disj_distrib conj_disj_distribR wlp_def points_to_def val_at_def)
    done
qed (simp add: sswa_comp_ppABC_to_ppACB_distrib wssa_comp_ppABC_to_ppACB_distrib pred_times_le_iff)+


subsection \<open> Update \<close>

definition heap_upd_rel
  :: \<open>'pt \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'a) \<Rightarrow> ((('pt \<rightharpoonup> 'a) \<times> fail_st) \<times> 's) \<Rightarrow> _ \<Rightarrow> bool\<close>
  where
    \<open>heap_upd_rel pt e \<equiv>
      \<lambda>((l,fl),s) ((l',fl'),s').
        s' = s \<and> (
          (\<exists>v. l pt = Some v \<and> fl = Running \<and> l' = l(pt \<mapsto> e v s) \<and> fl' = Running) \<or>
          (l pt = None \<or> fl = Failed) \<and> l' = l \<and> fl' = Failed)\<close>

abbreviation \<open>HeapUpd pt e \<equiv> \<langle> heap_upd_rel pt e \<rangle>\<close>

lemma rgsat_heap_update:
  fixes e :: \<open>'s \<Rightarrow> 'v::pre_perm_alg\<close>
    and e' :: \<open>'v \<Rightarrow> 's \<Rightarrow> 'v\<close>
    and pt \<pi> p R
  defines \<open>precond \<equiv> \<lceil> \<lambda>ss. \<L> (pt \<^bold>\<mapsto> e ss) \<rceil>\<^sub>\<S> \<sqinter> \<S> p\<close>
    and \<open>postcond \<equiv> \<lceil> \<lambda>ss. \<L> (pt \<^bold>\<mapsto> e' (e ss) ss) \<rceil>\<^sub>\<S> \<sqinter> \<S> p\<close>
    and \<open>frame_post \<equiv>
          \<lceil> \<lambda>ss. \<L> (\<^bold>@\<^sub>\<H> pt (\<lambda>vf. e' (e ss) ss ## vf \<and> e' (e ss + vf) ss = e' (e ss) ss + vf)) \<rceil>\<^sub>\<S>\<close>
  assumes
    \<open>F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> frame_post\<close>
    \<open>(=) \<le> G\<close>
    \<open>wssa R precond \<le> I\<close>
    \<open>sswa R postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { wssa R precond } HeapUpd pt e' { sswa R postcond }\<close>
  using assms
proof (intro rgsat_atom[where p=\<open>nofailure_pred precond\<close> and q=\<open>nofailure_pred postcond\<close>])

  have helper:
    \<open>\<And>f. (\<lambda>(l', s'). l' pt = None) \<sqinter> (wssa R precond \<^emph>\<and> f) \<le> \<bottom>\<close>
    apply (clarsimp simp add: precond_def points_to_def fun_eq_iff sp_def sepconj_conj_def wlp_def
        plus_option_iff split: prod.splits)
    apply (metis not_None_eq rtranclp.rtrancl_refl)
    done

  let ?ra = \<open>\<lambda>(l, s) (l', s'). s' = s \<and> (\<exists>v. l pt = Some v \<and> l' = l(pt \<mapsto> e' v s))\<close>

  let ?frame2 = \<open>\<forall>f\<le>F. sp ?ra (wssa R precond \<^emph>\<and> f) \<le> postcond \<^emph>\<and> any_shared f\<close>
  let ?frame1 =
    \<open>\<forall>f\<le>nofailure_pred F.
      sp (heap_upd_rel pt e') (wssa R (nofailure_pred precond) \<^emph>\<and> f) \<le>
        nofailure_pred postcond \<^emph>\<and> any_shared f\<close>

  have helper1: \<open>(heap_upd_rel pt e' \<circ>\<^sub>2 (\<lambda>(x, y). ((x, Running), y))) = ?ra\<close>
    by (clarsimp simp add: heap_upd_rel_def fun_eq_iff)
  have helper2:
    \<open>\<And>f. sp (heap_upd_rel pt e') (nofailure_pred (wssa R precond \<^emph>\<and> f)) \<le> nofailure_pred \<top>\<close>
    unfolding heap_upd_rel_def precond_def
    by (force simp add: sepconj_conj_apply sp_def plus_option_iff wlp_def points_to_def)

  have \<open>\<top> = (F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> frame_post)\<close>
    using assms(4) by simp
  also have \<open>(F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> frame_post) = ?frame2\<close>
    apply (clarsimp simp add: sp_def le_fun_def sepconj_conj_def)
    apply (rule iffI)
      (* \<Rightarrow> *)
     apply (clarsimp simp add: imp_conjL plus_option_iff)
     apply (rename_tac f ss v ls fs)
     apply (drule spec2, drule mp, blast)
     apply (drule mp, simp add: septract_conj_def, metis disjoint_sym)
     apply (clarsimp simp add: precond_def postcond_def frame_post_def wlp_def points_to_def
        disjoint_option_iff)
     apply (case_tac \<open>ls pt = None\<close>)
      (** \<open>ls pt = None\<close> *)
      apply force
      (** \<open>ls pt = Some ...\<close> *)
     apply (clarsimp simp add:  plus_option_iff wlp_def)
     apply (rename_tac v)
     apply (subgoal_tac \<open>ls pt = Some (e ss) \<and> (\<forall>pt'. pt' \<noteq> pt \<longrightarrow> ls pt' = None)\<close>)
      prefer 2
      apply fastforce
     apply (clarsimp simp add: plus_option_def wlp_def disjoint_option_iff split: option.splits)
      (* as there is only one source of a frame that passes predicate \<open>f\<close>, there is only one
          frame that will work here. *)
     apply (rule_tac x=fs in exI)
     apply (rule conjI, force simp add: val_at_heap_def)
     apply (elim disjE; simp?)
      (*** \<open> fs pt = None \<close> *)
      apply (force simp add: fun_eq_iff)
      (*** \<open> fs pt = Some ... \<close> *)
     apply (clarsimp simp add: fun_eq_iff if_bool_eq_disj if_distrib[of \<open>\<lambda>x. x = _\<close>] val_at_heap_def)
     apply metis
      (* \<Leftarrow> *)
    apply (clarsimp simp add: septract_conj_def imp_ex_conjL imp_conjL)
    apply (rename_tac fs ss ls)
    apply (drule_tac x=\<open>(=) (fs, ss)\<close> in spec, drule mp, blast)
    apply (drule_tac x=ss in spec)
    apply (drule_tac x=\<open>ls + fs\<close> in spec)
    apply (subgoal_tac \<open>ls pt = Some (e ss)\<close>)
     prefer 2
     apply (force simp add: precond_def wlp_def points_to_def)
    apply (case_tac \<open>fs pt\<close>)
      (*** \<open> fs pt = None \<close> *)
     apply (drule_tac x=\<open>e ss\<close> in spec)
     apply (drule mp, force simp add: precond_def points_to_def)
     apply clarsimp
     apply (drule spec, drule mp, rule disjoint_sym, assumption)
     apply (simp add: postcond_def frame_post_def val_at_heap_def; fail)
      (*** \<open> fs pt = Some ... \<close> *)
    apply (clarsimp simp add: plus_option_iff imp_conjL)
    apply (drule spec, drule mp, rule disjoint_sym, assumption)
    apply clarsimp
    apply (simp add: precond_def postcond_def frame_post_def val_at_heap_def points_to_def
        heap_upd_eq_singleton_plus_heap_iff; fail)
    done
  also have \<open>... = ?frame1\<close>
    apply (simp add: wssa_comp_ppABC_to_ppACB_distrib)
    apply (simp add: all_subpred_pred_times_eq_res_ppABC_to_ppACB_internalise
        nofailure_pred_sepconj_conj_distrib[symmetric]
        any_shared_pred_times_eq_res_ppABC_to_ppACB_distrib pred_times_le_iff)
    apply (subst sp_nofailure_pred_in_out_iff)
    apply (simp add: helper1 helper2)
    done
  finally show ?frame1
    using assms(3)
    by clarsimp

  show
    \<open>rel_image snd (rel_liftL (wssa R (nofailure_pred precond) \<^emph>\<and> nofailure_pred F) \<sqinter>
      heap_upd_rel pt e') \<le> G\<close>
    using assms(5)
    unfolding precond_def  heap_upd_rel_def
    by fastforce
qed (simp add: sswa_comp_ppABC_to_ppACB_distrib wssa_comp_ppABC_to_ppACB_distrib pred_times_le_iff)+


text \<open>
  [BCY2005]
\<close>

end