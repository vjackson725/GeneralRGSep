theory FailureEx
  imports "../Soundness"
begin

(* TODO: move *)
lemma option_ex_split:
  \<open>(case mx of Some x \<Rightarrow> p x | None \<Rightarrow> q) \<longleftrightarrow> (\<exists>x. mx = Some x \<and> p x) \<or> mx = None \<and> q\<close>
  by (metis case_option_disj_iff)

lemma singleton_plus_heap_eq_iff:
  \<open>[x \<mapsto> va] + h = [x \<mapsto> vb] + h \<longleftrightarrow> Some va + h x = Some vb + h x\<close>
  by (simp add: plus_fun_def plus_option_def fun_eq_iff split: option.splits if_splits)



subsection \<open> Heap predicate \<close>

definition points_to :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool\<close> (infix \<open>\<^bold>\<mapsto>\<close> 90) where
  \<open>p \<^bold>\<mapsto> x \<equiv> \<lambda>h. h p = Some x \<and> (\<forall>p'. p' \<noteq> p \<longrightarrow> h p' = None)\<close>

definition points_to_upcl :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool\<close> (infix \<open>\<^bold>\<mapsto>\<^sup>\<Up>\<close> 90) where
  \<open>p \<^bold>\<mapsto>\<^sup>\<Up> x \<equiv> \<lambda>h. h p = Some x\<close>

abbreviation points_to_perm
  :: \<open>'a \<Rightarrow> 'perm \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b discr \<times> 'perm) \<Rightarrow> bool\<close>
  (\<open>_ \<^bold>\<mapsto>\<^bsub>_\<^esub> _\<close> [90,0,90] 90)
  where
  \<open>p \<^bold>\<mapsto>\<^bsub>perm\<^esub> v \<equiv> p \<^bold>\<mapsto> (Discr v, perm)\<close>

lemma points_to_upcl_eq:
  fixes x :: \<open>'a :: perm_alg\<close>
  assumes maxsep_x: \<open>\<forall>x'. \<not> x ## x'\<close>
  shows \<open>pt \<^bold>\<mapsto>\<^sup>\<Up> x = \<top> \<^emph> pt \<^bold>\<mapsto> x\<close>
  unfolding sepconj_def points_to_def points_to_upcl_def
  apply (clarsimp simp add: fun_eq_iff)
  apply (rename_tac h)
  apply (intro iffI)
   apply (rule_tac x=\<open>h(pt := None)\<close> in exI)
   apply (rule_tac x=\<open>[pt \<mapsto> x]\<close> in exI)
   apply force
  apply (clarsimp simp add: disjoint_option_def split: option.splits)
  apply (clarsimp simp add: plus_option_iff)
  apply (metis disjoint_fun_def disjoint_option_iff(1) disjoint_sym_iff maxsep_x)
  done


subsection \<open> Failure and Programs \<close>

text \<open> Failure should not be resolvable. \<close>
definition
  \<open>step_fail_lift ra \<equiv>
    (\<lambda>(ls, (ss, fl)) s'.
        fl = Running \<and> ra (ls, ss) s' \<or>
        fl = Failed \<and> s' = (ls, ss, fl))\<close>

lemma failure_healthy_rel_apply[simp]:
  \<open>step_fail_lift ra s s' =
    (snd (snd s) = Running \<and> ra (fst s, fst (snd s)) s' \<or>
     snd (snd s) = Failed \<and> s' = s)\<close>
  by (simp add: step_fail_lift_def prod_eq_iff split: prod.splits)


subsection \<open> Failure definitions \<close>

definition pred_Times_third
  :: \<open>('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> ('a \<times> ('b \<times> 'c) \<Rightarrow> bool)\<close>
  (infix \<open>\<times>\<^sub>P\<^sub>3\<close> 80)
  where
  \<open>p \<times>\<^sub>P\<^sub>3 q \<equiv> \<lambda>(a,(b,c)). p (a,b) \<and> q c\<close>

lemma pred_Times_third_apply[simp]:
  \<open>(p \<times>\<^sub>P\<^sub>3 q) x = (p (fst x, fst (snd x)) \<and> q (snd (snd x)))\<close>
  by (simp add: pred_Times_third_def split: prod.splits)


abbreviation
  \<open>nofailure_pred p \<equiv> p \<times>\<^sub>P\<^sub>3 (=) Running\<close>

lemmas nofailure_pred_def =
  pred_Times_third_def[of _ \<open>(=) Running\<close>]

abbreviation
  \<open>failure_pred p \<equiv> p \<times>\<^sub>P\<^sub>3 (=) Failed\<close>

lemmas failure_pred_def =
  pred_Times_third_def[of _ \<open>(=) Running\<close>]

abbreviation failure_rgsat_pretty
  (\<open>_, _, _, _, _ \<turnstile>\<^sub>f { _ } _ { _ }\<close> [55, 0, 0, 0, 0, 55, 55, 55] 56) where
  \<open>R, G, I, F, T \<turnstile>\<^sub>f { p } c { q } \<equiv>
    rgsat c
      (R \<times>\<^sub>R (=)) (G \<times>\<^sub>R (=))
      (nofailure_pred p) (nofailure_pred q)
      (nofailure_pred I) (nofailure_pred F)
      T\<close>


lemma predTimes3_sepconj_conj_distrib:
  \<open>(p \<^emph>\<and> f) \<times>\<^sub>P\<^sub>3 q = p \<times>\<^sub>P\<^sub>3 q \<^emph>\<and> f \<times>\<^sub>P\<^sub>3 q\<close>
  by (force simp add: pred_Times_third_def sepconj_conj_apply fun_eq_iff)

lemma predTimes3_inf_distrib:
  \<open>(p \<sqinter> f) \<times>\<^sub>P\<^sub>3 q = p \<times>\<^sub>P\<^sub>3 q \<sqinter> f \<times>\<^sub>P\<^sub>3 q\<close>
  by (force simp add: pred_Times_third_def sepconj_conj_apply fun_eq_iff)

lemma predTimes3_sup_distrib:
  \<open>(p \<squnion> f) \<times>\<^sub>P\<^sub>3 q = p \<times>\<^sub>P\<^sub>3 q \<squnion> f \<times>\<^sub>P\<^sub>3 q\<close>
  by (force simp add: pred_Times_third_def sepconj_conj_apply fun_eq_iff)


lemma sp_triple_relTimes_predTimes3_eq[simp]:
  \<open>sp (ra \<times>\<^sub>R (rb \<times>\<^sub>R rc)) (p \<times>\<^sub>P\<^sub>3 q) = sp (ra \<times>\<^sub>R rb) p \<times>\<^sub>P\<^sub>3 sp rc q\<close>
  by (force simp add: sp_def pred_Times_third_def)

lemma reflp_wlp_equals_predTimes3_eq[simp]:
  \<open>reflp ra \<Longrightarrow> reflp rb \<Longrightarrow>
    wlp (ra \<times>\<^sub>R rb \<times>\<^sub>R (=)) (p \<times>\<^sub>P\<^sub>3 q) = wlp (ra \<times>\<^sub>R rb) p \<times>\<^sub>P\<^sub>3 q\<close>
  by (force simp add: wlp_def pred_Times_third_def fun_eq_iff reflp_def)

lemma predTimes3_eqVal_le_iff[simp]:
  \<open>pa \<times>\<^sub>P\<^sub>3 (=) v \<le> pb \<times>\<^sub>P\<^sub>3 (=) v \<longleftrightarrow> pa \<le> pb\<close>
  by (force simp add: pred_Times_third_def)

lemma subset_nofailure_pred_iff:
  \<open>f \<le> nofailure_pred F \<longleftrightarrow> (\<exists>f'. f' \<le> F \<and> f = nofailure_pred f')\<close>
  apply (clarsimp simp add: nofailure_pred_def le_fun_def fun_eq_iff)
  apply (rule iffI)
   apply (rule_tac x=\<open>\<lambda>(ls, ss). f (ls, ss, Running)\<close> in exI, force)
  apply force
  done

lemma all_impl_nofailure_pred_internalise:
  \<open>(\<forall>p\<le>nofailure_pred P. q p) \<longleftrightarrow> (\<forall>p\<le>P. q (nofailure_pred p))\<close>
  by (simp add: subset_nofailure_pred_iff, metis)

lemma sp_step_fail_lift_on_nofailure_pred_eq:
  \<open>sp (step_fail_lift r) (nofailure_pred p) =
    (\<lambda>(l', s', k'). (\<exists>s. r s (l', s', k') \<and> p s))\<close>
  by (simp add: sp_def fun_eq_iff)

lemma nofailure_local_eq:
  \<open>nofailure_pred (\<L> p) = \<L> p \<sqinter> nofailure_pred \<top>\<close>
  unfolding nofailure_pred_def
  by (simp add: fun_eq_iff sepconj_conj_def)


section \<open> Assert \<close>

text \<open>
  Assert fails when its precondition is not met.
  GenRGSep has no embedded fail state, and so it must be encoded into the
  state model. Separation logic is not compatible with destructive failure,
  and, moreover, atoms see the whole state, not the local state.
  Thus we place a crash in the shared state.
\<close>
definition \<open>Assert p \<equiv>
  Atomic (step_fail_lift (\<lambda>(l, s) (l', s', fl').
    l' = l \<and> s' = s \<and> (p (l, s) \<and> fl' = Running \<or> \<not> p (l, s) \<and> fl' = Failed)
  ))\<close>

lemma rgsat_assert:
  assumes precond:
    \<open>p \<^emph>\<and> F \<le> pa\<close>
    and guar:
    \<open>rel_image snd (rel_liftL (p \<^emph>\<and> F) \<sqinter> (=)) \<le> G\<close>
    and inv:
    \<open>sswa R p \<le> I\<close>
    and tree:
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { wssa R p } Assert pa { sswa R p }\<close>
  using assms
  unfolding Assert_def
proof (intro rgsat_atom[where p=\<open>nofailure_pred p\<close> and q=\<open>nofailure_pred p\<close>])
  let ?ra' = \<open>(step_fail_lift
            (\<lambda>(l, s) (l', s', k').
                l' = l \<and>
                s' = s \<and> (pa (l, s) \<and> k' = Running \<or> \<not> pa (l, s) \<and> k' = Failed)))\<close>

  show
    \<open>\<forall>f\<le>nofailure_pred F.
       sp ?ra' (nofailure_pred p \<^emph>\<and> f) \<le> nofailure_pred p \<^emph>\<and> any_shared f\<close>
    using precond
    by (simp add: all_impl_nofailure_pred_internalise
        predTimes3_sepconj_conj_distrib[symmetric] sp_step_fail_lift_on_nofailure_pred_eq,
        fastforce simp add: le_fun_def sepconj_conj_apply any_shared_def)

  show
    \<open>rel_image snd
      (rel_liftL (nofailure_pred p \<^emph>\<and> nofailure_pred F) \<sqinter> ?ra')
      \<le> G \<times>\<^sub>R (=)\<close>
    using guar precond
    by (force simp add: predTimes3_sepconj_conj_distrib[symmetric])

  show \<open>sswa (R \<times>\<^sub>R (=)) (nofailure_pred p) \<le> nofailure_pred I\<close>
    using assms
    by force
qed (simp add: sswa_weaker wssa_stronger)+

lemma frame_expanding_iff:
  \<open>(\<forall>f\<le>F. (p \<sqinter> pa) \<^emph>\<and> f \<le> (p \<^emph>\<and> any_shared f) \<sqinter> pa) \<longleftrightarrow>
    ((p \<sqinter> pa) \<^emph>\<and> F \<le> (p \<^emph>\<and> F) \<sqinter> pa)\<close>
  by (simp add: le_fun_def any_shared_def sepconj_conj_def, fast)

lemma rgsat_assert2:
  assumes
    \<open>(p \<sqinter> pa) \<^emph>\<and> F \<le> pa\<close>
    \<open>rel_image snd (rel_liftL ((p \<sqinter> pa) \<^emph>\<and> F) \<sqinter> (=)) \<le> G\<close>
    \<open>sswa R (p \<sqinter> pa) \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { wssa R (p \<sqinter> pa) } Assert pa { sswa R (p \<sqinter> pa) }\<close>
  using assms
  by (blast intro: rgsat_assert)

lemma opstep_assert_iff[simp]:
  \<open>opstep \<alpha> (s, Assert p) sc' \<longleftrightarrow>
    \<alpha> = Vis \<and>
    snd sc' = Skip \<and>
    (snd (snd s) = Running \<and>
      fst (fst sc') = fst s \<and>
      fst (snd (fst sc')) = fst (snd s) \<and>
      (p (fst s, fst (snd s)) \<and> snd (snd (fst sc')) = Running \<or>
        \<not> p (fst s, fst (snd s)) \<and> snd (snd (fst sc')) = Failed) \<or>
      snd (snd s) = Failed \<and> s = fst sc')\<close>
  by (force simp add: Assert_def case_prod_beta)


section \<open> PointerRead \<close>

definition PointerRead
  :: \<open>'x \<Rightarrow> 'pt \<Rightarrow> (('pt \<rightharpoonup> 'v discr \<times> 'perm) \<times> (('x \<Rightarrow> 'v) \<times> fail_st)) comm\<close>
  where
    \<open>PointerRead x pt \<equiv>
      Atomic (step_fail_lift (\<lambda>(l, s) (l', s', fl').
        case l pt of
          Some (v, _) \<Rightarrow> l' = l \<and> s' = s(x := the_discr v) \<and> fl' = Running
        | None \<Rightarrow> l' = l \<and> s' = s \<and> fl' = Failed
      ))\<close>

lemma rgsat_pointer_read:
  fixes x v p R \<pi> pt
  defines \<open>ra_ptr_read \<equiv> (=) \<times>\<^sub>R (\<lambda>s s'. s' = s(x := v))\<close>
  and \<open>precond \<equiv> \<L> (pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> v) \<sqinter> wssa R (\<S> (\<lambda>s. p (s(x := v))))\<close>
  and \<open>postcond \<equiv> \<L> (pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> v) \<sqinter> sswa R (\<S> p)\<close>
assumes
    \<open>rel_image snd ra_ptr_read \<le> G\<close>
    \<open>precond \<le> I\<close>
    \<open>postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { precond } PointerRead x pt { postcond }\<close>
  using assms
  unfolding PointerRead_def
proof (intro rgsat_atom[where p=\<open>nofailure_pred precond\<close> and q=\<open>nofailure_pred postcond\<close>])
  let ?ra' = \<open>step_fail_lift (\<lambda>(l, s) (l', s', fl').
               case l pt of None \<Rightarrow>
                  l' = l \<and> s' = s \<and> fl' = Failed
               | Some (v, xa) \<Rightarrow>
                  l' = l \<and> s' = s(x := the_discr v) \<and> fl' = Running)\<close>

  show \<open>nofailure_pred precond \<le> wssa (R \<times>\<^sub>R (=)) (nofailure_pred precond)\<close>
    unfolding precond_def
    by (simp add: wlp_inf)

  show \<open>sswa (R \<times>\<^sub>R (=)) (nofailure_pred postcond) \<le> nofailure_pred postcond\<close>
    unfolding postcond_def
    by simp

  show \<open>\<forall>f\<le>nofailure_pred F. sp ?ra' (nofailure_pred precond \<^emph>\<and> f) \<le> nofailure_pred postcond \<^emph>\<and> any_shared f\<close>
    unfolding any_shared_def ra_ptr_read_def precond_def postcond_def
    apply (clarsimp simp add: sp_step_fail_lift_on_nofailure_pred_eq subset_nofailure_pred_iff
        predTimes3_sepconj_conj_distrib[symmetric] case_option_disj_iff)
    apply (clarsimp simp add: sepconj_conj_def points_to_def plus_option_iff)
    apply (metis (mono_tags, lifting) Discr_inverse_iff comp_apply snd_conv sswa_trivial wssa_trivial)
    done

  show
    \<open>rel_image snd
      (rel_liftL (nofailure_pred precond \<^emph>\<and> nofailure_pred F) \<sqinter> ?ra')
    \<le> G \<times>\<^sub>R (=)\<close>
    using assms(4)
    apply (simp only: predTimes3_sepconj_conj_distrib[symmetric] predTimes3_sup_distrib[symmetric])
    apply (unfold ra_ptr_read_def precond_def postcond_def)
    apply (clarsimp simp add: sepconj_conj_def points_to_def plus_option_iff rel_image_def
        le_fun_def ex_disj_distrib all_conj_distrib split: option.splits)
    apply (force simp add: wlp_def plus_option_iff ex_disj_distrib all_conj_distrib)
    done
qed simp+


section \<open> PointerWrite \<close>

definition PointerWrite
  :: \<open>'pt \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> (('pt \<rightharpoonup> 'v discr \<times> 'perm) \<times> ('s \<times> fail_st)) comm\<close>
  where
    \<open>PointerWrite pt e \<equiv>
      Atomic (step_fail_lift (\<lambda>(l, s) (l', s', fl').
        case l pt of
          Some (_, perm) \<Rightarrow> l' = l(pt \<mapsto> (Discr (e s), perm)) \<and> s' = s \<and> fl' = Running
        | None \<Rightarrow> l' = l \<and> s' = s \<and> fl' = Failed
      ))\<close>

lemma top_write_frame_cond_iff_all_disjoint_perm:
  \<open>\<top> \<le> - \<L> (\<Squnion>x'\<in>Collect ((##) (Discr v, \<pi>)). pt \<^bold>\<mapsto>\<^sup>\<Up> x') \<longleftrightarrow> (\<forall>\<pi>'. \<not> \<pi> ## \<pi>')\<close>
  by (force simp add: points_to_upcl_def le_fun_def)

lemma nofailure_pred_any_shared_semidistrib:
  \<open>nofailure_pred (any_shared p) \<le> any_shared (nofailure_pred p)\<close>
  by (simp add: nofailure_pred_def any_shared_def le_fun_def)

lemma rgsat_pointer_write:
  fixes e pt p R \<pi> v
  defines \<open>ra_ptr_write \<equiv> (\<lambda>(l,s) (l',s'). l' = l(pt \<mapsto> e s) \<and> s' = s)\<close>
    and \<open>precond \<equiv> \<L> (pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> v) \<sqinter> wssa R (\<S> p)\<close>
    and \<open>postcond \<equiv> sswa R ((\<lambda>(ls, ss). (pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> (e ss)) ls) \<sqinter> \<S> p)\<close>
  assumes
    \<comment> \<open> this is the side condition that constrains permissions to be exclusive \<close>
    \<open>F \<le> - \<L> (\<Squnion>x'\<in>Collect ((##) (Discr v, \<pi>)). pt \<^bold>\<mapsto>\<^sup>\<Up> x')\<close>
    \<open>rel_image snd ra_ptr_write \<le> G\<close>
    \<open>precond \<le> I\<close>
    \<open>postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { precond } PointerWrite pt e { postcond }\<close>
  using assms
  unfolding PointerWrite_def
proof (intro rgsat_atom[where p=\<open>nofailure_pred precond\<close> and q=\<open>nofailure_pred postcond\<close>])
  let ?ra' = \<open>step_fail_lift (\<lambda>(l, s) (l', s', fl').
                case l pt of
                  None \<Rightarrow> l' = l \<and> s' = s \<and> fl' = Failed
                | Some (x, perm) \<Rightarrow> l' = l(pt \<mapsto> (Discr (e s), perm)) \<and> s' = s \<and> fl' = Running)\<close>

  show \<open>nofailure_pred precond \<le> wssa (R \<times>\<^sub>R (=)) (nofailure_pred precond)\<close>
    unfolding precond_def
    apply (clarsimp simp add: points_to_def wlp_def)
    apply (metis rtranclp_trans)
    done

  show \<open>sswa (R \<times>\<^sub>R (=)) (nofailure_pred postcond) \<le> nofailure_pred postcond\<close>
    unfolding postcond_def
    apply (clarsimp simp add: fun_eq_iff le_fun_def points_to_def sp_def)
    apply (metis rtranclp_trans)
    done

  let ?frame5 =
    \<open>(\<forall>f\<le>F. \<forall>lf s'.
      f (lf, s') \<longrightarrow>
      [pt \<mapsto> (Discr v, \<pi>)] ## lf \<longrightarrow>
      R\<^sup>*\<^sup>* s' \<le> p \<longrightarrow>
      (\<exists>s. R\<^sup>*\<^sup>* s s' \<and> p s \<and>
        [pt \<mapsto> (Discr (e s), \<pi>)] ## lf \<and>
        Some (Discr (e s'), \<pi>) + lf pt = Some (Discr (e s), \<pi>) + lf pt))\<close>
  let ?frame4 =
    \<open>(\<forall>f\<le>F. \<forall>lf s'.
      f (lf, s') \<longrightarrow>
      [pt \<mapsto> (Discr v, \<pi>)] ## lf \<longrightarrow>
      R\<^sup>*\<^sup>* s' \<le> p \<longrightarrow>
      (\<exists>s. R\<^sup>*\<^sup>* s s' \<and> p s \<and>
        [pt \<mapsto> (Discr (e s), \<pi>)] ## lf \<and>
        [pt \<mapsto> (Discr (e s'), \<pi>)] + lf = [pt \<mapsto> (Discr (e s), \<pi>)] + lf))\<close>
  let ?frame3 =
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
  let ?frame2 =
    \<open>(\<forall>f\<le>F. \<forall>l \<pi> s.
      l pt = None \<longrightarrow>
      (\<exists>v. (precond \<^emph>\<and> f) (l(pt \<mapsto> (Discr v, \<pi>)), s)) \<longrightarrow>
      (postcond \<^emph>\<and> any_shared f) (l(pt \<mapsto> (Discr (e s), \<pi>)), s))\<close>
  let ?frame1 =
    \<open>\<forall>f\<le>nofailure_pred F.
      sp ?ra' (nofailure_pred precond \<^emph>\<and> f) \<le> nofailure_pred postcond \<^emph>\<and> any_shared f\<close>


  have \<open>?frame5 = ?frame4\<close>
    apply (clarsimp simp add: le_fun_def points_to_upcl_def)
    sorry

  have \<open>\<top> = ?frame4\<close>
    using assms(4)
    apply (clarsimp simp add: le_fun_def points_to_upcl_def)
    sorry
  also have \<open>... = ?frame3\<close>
    apply (rule iffI)
     apply (metis predicate1I)
    apply clarsimp
    apply (drule_tac x=\<open>(=) (lf, s')\<close> in spec)
    apply blast
    done
  also have \<open>... = ?frame2\<close>
    unfolding precond_def postcond_def points_to_def
    apply (clarsimp simp add: fun_eq_iff sepconj_conj_def plus_option_iff all_conj_distrib
        any_shared_def sp_def wlp_def split: if_splits)
    apply (intro iff_allI imp_cong[OF refl])
    sorry
(*
    apply (rule imp_cong)
      (* assm equiv *)
     apply (simp add: disjoint_fun_def disjoint_option_def option_ex_split plus_option_iff2)
     apply (rule iffI)
      (** \<Rightarrow> *)
      apply clarsimp
      apply (elim exE disjE conjE; simp?) (* +1 *)
      (*** \<open>pt\<close> in the frame *)
       apply (rename_tac \<pi>')
       apply (rule_tac x=\<open>lx(pt \<mapsto> (Discr v, \<pi> + \<pi>'))\<close> in exI)
       apply simp
       apply (rule_tac x=\<open>[pt \<mapsto> (Discr v, \<pi>)]\<close> in exI)
       apply (rule_tac x=lx in exI)
       apply force
      (*** \<open>pt\<close> not in frame *)
      apply (rule_tac x=\<open>lx(pt \<mapsto> (Discr v, \<pi>))\<close> in exI)
      apply simp
      apply (rule_tac x=\<open>[pt \<mapsto> (Discr v, \<pi>)]\<close> in exI)
      apply (rule_tac x=lx in exI)
      apply force
      (** \<Leftarrow> *)
     apply (clarsimp simp add: plus_option_iff)
     apply (erule disjE)
      apply (metis plus_option_simps(3))
     apply clarsimp
     apply (rename_tac hf dv \<pi>')
     apply (rule_tac x=hf in exI)
     apply clarsimp
     apply (metis option.inject option.simps(3) prod.inject)
      (* conseq equiv *)
    apply (clarsimp simp add: disjoint_fun_def disjoint_option_def
        plus_option_iff plus_option_iff2 disj.assoc[symmetric])
    apply (subst option_ex_split)
    apply (simp split: option.splits)
    apply (rename_tac la lb)
    apply (rule iffI)
      (** \<Rightarrow> *)
     apply clarsimp
     apply (rename_tac lf s ss)
     apply (rule_tac x=\<open>[pt \<mapsto> (Discr (e s), \<pi>)]\<close> in exI)
     apply (rule_tac x=lf in exI)
     apply (intro conjI)
        apply (clarsimp; fail)
       apply (clarsimp simp add: plus_option_iff2; fail)
      apply (rule_tac x=\<open>[pt \<mapsto> (Discr (e s), \<pi>)]\<close> in exI)
      apply (simp, blast)
     apply blast
      (** \<Leftarrow> *)
    apply (clarsimp simp add: plus_option_iff)
    apply (elim disjE; metis (no_types))
    done
*)
  also have \<open>... = ?frame1\<close>
    apply -
    apply (simp add: all_impl_nofailure_pred_internalise sp_step_fail_lift_on_nofailure_pred_eq
        predTimes3_sepconj_conj_distrib[symmetric])
    apply (simp add: option_ex_split nofailure_pred_def le_fun_def ex_disj_distrib
        conj_disj_distribR sepconj_conj_def)
    apply (intro iffI)
     apply clarsimp
     apply (rule conjI)
      apply (clarsimp simp add: precond_def points_to_def sepconj_conj_def plus_option_iff)

    sorry
  finally show ?frame1
    by simp

  show
    \<open>rel_image snd
      (rel_liftL (nofailure_pred precond \<^emph>\<and> nofailure_pred F) \<sqinter> ?ra')
    \<le> G \<times>\<^sub>R (=)\<close>
    using assms(5)
    apply (simp only: predTimes3_sepconj_conj_distrib[symmetric] predTimes3_sup_distrib[symmetric])
    apply (unfold ra_ptr_write_def precond_def postcond_def)
    apply (clarsimp simp add: sepconj_conj_def points_to_def plus_option_iff rel_image_def
        le_fun_def ex_disj_distrib all_conj_distrib split: option.splits)
    apply force
    done
qed simp+

end