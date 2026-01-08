theory FailureExCont
  imports "../ex/FailureEx"
begin



lemma rgsat_pointer_write2:
  fixes e pt p R \<pi> v
  defines \<open>precond \<equiv> (pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> (\<lambda>_. v)) \<sqinter> wssa R (\<S> p)\<close>
    and \<open>postcond \<equiv> sswa R (pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> e \<sqinter> \<S> p)\<close>
  assumes
    \<comment> \<open> this is the side condition that constrains permissions to be exclusive \<close>
    \<open>F \<le> - \<L> (\<Squnion>x'\<in>Collect ((##) (Discr v, \<pi>)). pt \<^bold>\<mapsto>\<^sup>\<Up> x')\<close>
    \<open>(=) \<le> G\<close>
    \<open>precond \<le> I\<close>
    \<open>postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { precond } HeapWrite pt e { postcond }\<close>
  using assms
proof (intro rgsat_atom[where p=\<open>nofailure_pred precond\<close> and q=\<open>nofailure_pred postcond\<close>])
  show \<open>nofailure_pred precond \<le> wssa R (nofailure_pred precond)\<close>
    unfolding precond_def
    by (clarsimp simp add: points_to_perm_def wlp_def, meson rtranclp_trans)
  then show \<open>sswa R (nofailure_pred precond) \<le> nofailure_pred I\<close>
    by (meson assms(5) nofailure_pred_strong_mono order_trans wlp_weaker_iff_sp_stronger)

  show \<open>sswa R (nofailure_pred postcond) \<le> nofailure_pred postcond\<close>
    unfolding postcond_def
    by (clarsimp simp add: points_to_perm_def sp_def, metis rtranclp_trans)
  then show \<open>sswa R (nofailure_pred postcond) \<le> nofailure_pred I\<close>
    using assms(6) by fastforce

  have failure_helper: \<open>\<And>f. failure_pred ((\<lambda>(l', s'). l' pt = None) \<sqinter> (precond \<^emph>\<and> f)) = \<bottom>\<close>
    by (clarsimp simp add: fun_eq_iff precond_def points_to_perm_def sepconj_conj_def
        plus_option_iff)


  \<comment> \<open> The exact condition is a bit nasty... \<close>
  let ?frame6 =
    \<open>(\<forall>f\<le>F. \<forall>lf s'.
      f (lf, s') \<longrightarrow>
      [pt \<mapsto> (Discr v, \<pi>)] ## lf \<longrightarrow>
      R\<^sup>*\<^sup>* s' \<le> p \<longrightarrow>
      (\<exists>s. R\<^sup>*\<^sup>* s s' \<and> p s \<and>
        [pt \<mapsto> (Discr (e s), \<pi>)] ## lf \<and>
        Some (Discr (e s'), \<pi>) + lf pt = Some (Discr (e s), \<pi>) + lf pt))\<close>
  let ?frame5 =
    \<open>(\<forall>f\<le>F. \<forall>lf s'.
      f (lf, s') \<longrightarrow>
      [pt \<mapsto> (Discr v, \<pi>)] ## lf \<longrightarrow>
      R\<^sup>*\<^sup>* s' \<le> p \<longrightarrow>
      (\<exists>s. R\<^sup>*\<^sup>* s s' \<and> p s \<and>
        [pt \<mapsto> (Discr (e s), \<pi>)] ## lf \<and>
        [pt \<mapsto> (Discr (e s'), \<pi>)] + lf = [pt \<mapsto> (Discr (e s), \<pi>)] + lf))\<close>
  let ?frame4 =
    \<open>(\<forall>f\<le>F. \<forall>l' s'.
       (\<exists>lx.
          [pt \<mapsto> (Discr v, \<pi>)] ## lx \<and>
          l' = [pt \<mapsto> (Discr (e s'), \<pi>)] + lx \<and>
          (\<forall>b. R\<^sup>*\<^sup>* s' b \<longrightarrow> p b) \<and>
          f (lx, s')) \<longrightarrow>
       (\<exists>lx s.
          [pt \<mapsto> (Discr (e s), \<pi>)] ## lx \<and>
          l' = [pt \<mapsto> (Discr (e s), \<pi>)] + lx \<and>
          R\<^sup>*\<^sup>* s s' \<and>
          p s \<and>
          (\<exists>ss. f (lx, ss))))\<close>
  let ?frame3 =
    \<open>(\<forall>f\<le>F. \<forall>l \<pi> s.
      l pt = None \<longrightarrow>
      (precond \<^emph>\<and> f) (l(pt \<mapsto> (Discr v, \<pi>)), s) \<longrightarrow>
      (postcond \<^emph>\<and> any_shared f) (l(pt \<mapsto> (Discr (e s), \<pi>)), s))\<close>

  let ?ra = \<open>(\<lambda>(l, s) (l', s'). s' = s \<and> (\<exists>v perm. l pt = Some (v, perm) \<and> l' = l(pt \<mapsto> (Discr (e s), perm))))\<close>
  let ?frame2 =
    \<open>\<forall>f\<le>F. sp ?ra (precond \<^emph>\<and> f) \<le> postcond \<^emph>\<and> any_shared f\<close>
  let ?frame1 =
    \<open>\<forall>f\<le>nofailure_pred F.
      sp (heap_write_rel pt e) (nofailure_pred precond \<^emph>\<and> f) \<le>
        nofailure_pred postcond \<^emph>\<and> any_shared f\<close>

  note internalise = all_subpred_pred_times_eq_res_ppABC_to_ppACB_internalise

  have \<open>?frame5 = ?frame4\<close>
    apply (clarsimp simp add: le_fun_def points_to_upcl_def)
    sorry

  have \<open>\<top> = ?frame5\<close>
    using assms(4)
    apply (clarsimp simp add: le_fun_def points_to_upcl_def)
    sorry
  also have \<open>... = ?frame4\<close>
    apply (rule iffI)
     apply (metis predicate1I)
    apply clarsimp
    apply (drule_tac x=\<open>(=) (lf, s')\<close> in spec)
    apply blast
    done
  also have \<open>... = ?frame3\<close>
    unfolding precond_def postcond_def points_to_perm_def
    apply (clarsimp simp add: fun_eq_iff sepconj_conj_def plus_option_iff all_conj_distrib
        any_shared_def sp_def wlp_def split: if_splits)
    apply (intro iff_allI imp_cong[OF refl])
    sorry
  also have \<open>... = ?frame2\<close>
    unfolding precond_def postcond_def
    apply (clarsimp simp add: sp_def le_fun_def)
    apply (rule all_cong)
    apply (rule iffI)
      (* \<Rightarrow> *)
     apply (clarsimp simp add: sepconj_conj_apply points_to_perm_def plus_option_iff
        imp_conjR all_conj_distrib imp_ex_conjL)
     apply (rename_tac sx' va perm la lb)
     apply (subgoal_tac \<open>la = [pt \<mapsto> (Discr v, \<pi>)]\<close>)
      prefer 2
      apply force
     apply clarsimp
     apply (case_tac \<open>lb pt = None\<close>, force)
     apply clarsimp
     apply (rename_tac v' \<pi>')
     apply (subgoal_tac \<open>v' = Discr v\<close>)
      prefer 2
      apply (simp add: disjoint_fun_def split: if_splits; fail)
     apply clarsimp
     apply (drule_tac x=\<open>lb(pt := None)\<close> in spec, drule mp, force)
     apply (drule_tac x=\<open>\<pi> + \<pi>'\<close> and y=sx' in spec2, drule_tac x=\<open>[pt \<mapsto> (Discr v, \<pi>)]\<close> and y=lb in spec2)
     apply clarsimp
     apply (drule mp)
      apply (clarsimp simp add: fun_eq_iff; fail)
     apply clarsimp
     apply (rename_tac lc ld sx s')
     apply (subgoal_tac \<open>lc = [pt \<mapsto> (Discr (e sx), \<pi>)]\<close>)
      prefer 2
      apply force
     apply clarsimp
     apply (rule_tac x=\<open>[pt \<mapsto> (Discr (e sx), \<pi>)]\<close> in exI)
     apply (rule_tac x=ld in exI)
     apply (clarsimp simp add: heap_upd_eq_singleton_plus_heap_iff plus_option_iff)
     apply blast
  (* \<Leftarrow> *)
    apply clarsimp
    apply (clarsimp simp add: sepconj_conj_apply points_to_perm_def plus_option_iff
        imp_conjR all_conj_distrib imp_ex_conjL)
    apply (subgoal_tac \<open>la = [pt \<mapsto> (Discr v, \<pi>)]\<close>)
     prefer 2
     apply force
    apply clarsimp
    apply (case_tac \<open>lb pt = None\<close>)
     apply (clarsimp simp add: heap_upd_eq_iff)
     apply (subgoal_tac \<open>lb = l(pt := None)\<close>)
      prefer 2
      apply fastforce
     apply clarsimp
     apply (drule_tac x=s and y=\<open>l(pt \<mapsto> (Discr v, \<pi>))\<close> in spec2,
        drule_tac x=\<open>Discr v\<close> and y=\<pi> in spec2)
     apply clarsimp
     apply (drule_tac x=\<open>[pt \<mapsto> (Discr v, \<pi>)]\<close> and y=l in spec2, drule mp, force)
     apply clarsimp
     apply (metis fun_upd_triv)
    apply (clarsimp simp add: heap_upd_eq_singleton_plus_heap_iff)
    apply (rename_tac ly sy)
    sorry
  also have \<open>... = ?frame1\<close>
    by (simp add: internalise  nofailure_pred_sepconj_conj_distrib[symmetric]
        heap_write_rel_nofailure_rel_eq failure_helper)
  finally show ?frame1
    by simp

  show
    \<open>rel_image snd (rel_liftL (nofailure_pred precond \<^emph>\<and> nofailure_pred F) \<sqinter> heap_write_rel pt e) \<le>
      G\<close>
    using assms(4)
    by (clarsimp simp add: heap_write_rel_def nofailure_pred_sepconj_conj_distrib[symmetric]
        le_fun_def)
qed simp+


end