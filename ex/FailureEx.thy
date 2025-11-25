theory FailureEx
  imports "../Soundness"
begin

(* TODO: move *)
lemma case_option_disj_split:
  \<open>(case ma of None \<Rightarrow> p | Some a \<Rightarrow> q a) \<longleftrightarrow>
    ma = None \<and> p \<or> (\<exists>a. ma = Some a \<and> q a)\<close>
  by (metis case_optionE option.simps(4,5))


subsection \<open> Heap predicate \<close>

definition points_to_perm
  :: \<open>'a \<Rightarrow> 'perm \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b discr \<times> 'perm) \<Rightarrow> bool\<close>
  (\<open>_ \<^bold>\<mapsto>\<^bsub>_\<^esub> _\<close> [90,0,90] 90)
  where
  \<open>p \<^bold>\<mapsto>\<^bsub>perm\<^esub> v \<equiv> \<lambda>h. h p = Some (Discr v, perm)\<close>

abbreviation points_to :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b discr \<times> munit) \<Rightarrow> bool\<close> (infix \<open>\<^bold>\<mapsto>\<close> 90) where
  \<open>p \<^bold>\<mapsto> v \<equiv> p \<^bold>\<mapsto>\<^bsub>\<one>\<^esub> v\<close>


lemma shared_sepconj_conj_eq:
  \<open>(\<S> p \<^emph>\<and> q) = \<S> p \<sqinter> (\<top> \<^emph>\<and> q)\<close>
  \<open>(q \<^emph>\<and> \<S> p) = \<S> p \<sqinter> (q \<^emph>\<and> \<top>)\<close>
  by (force simp add: sepconj_conj_def fun_eq_iff)+


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
    \<open>sswa R p \<le> pa\<close>
    \<open>sswa R p \<^emph>\<and> F \<le> pa\<close>
    and step:
    \<open>sswa R p \<le> q\<close>
    \<open>\<forall>f\<le>F. sswa R p \<^emph>\<and> f \<le> q \<^emph>\<^sub>\<triangleright> f\<close>
    and guar:
    \<open>rel_image snd (rel_liftL (sswa R p \<squnion> sswa R p \<^emph>\<and> F) \<sqinter> (=)) \<le> G\<close>
    and misc:
    \<open>sswa R p \<le> I\<close>
    \<open>sswa R q \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { p } Assert pa { q }\<close>
  using assms
  unfolding Assert_def
proof (intro rgsat_atom[where q=\<open>nofailure_pred (sswa R p)\<close>])
  let ?ra' = \<open>(step_fail_lift
            (\<lambda>(l, s) (l', s', k').
                l' = l \<and>
                s' = s \<and> (pa (l, s) \<and> k' = Running \<or> \<not> pa (l, s) \<and> k' = Failed)))\<close>

  show
    \<open>sp ?ra' (sswa (R \<times>\<^sub>R (=)) (nofailure_pred p)) \<le> nofailure_pred (sswa R p)\<close>
    using precond
    by (clarsimp simp add: fun_eq_iff le_fun_def sp_step_fail_lift_on_nofailure_pred_eq)

  show
    \<open>\<forall>f\<le>nofailure_pred F.
       sp ?ra' (sswa (R \<times>\<^sub>R (=)) (nofailure_pred p) \<^emph>\<and> f) \<le> nofailure_pred (sswa R p) \<^emph>\<^sub>\<triangleright> f\<close>
    using precond
    by (simp add: all_impl_nofailure_pred_internalise
        predTimes3_sepconj_conj_distrib[symmetric] sp_step_fail_lift_on_nofailure_pred_eq,
        fastforce simp add: le_fun_def sepconj_conj_apply sepconj_left_def)

  show
    \<open>rel_image snd
      (rel_liftL
        (sswa (R \<times>\<^sub>R (=)) (nofailure_pred p) \<squnion>
          sswa (R \<times>\<^sub>R (=)) (nofailure_pred p) \<^emph>\<and> nofailure_pred F) \<sqinter>
        ?ra')
    \<le> G \<times>\<^sub>R (=)\<close>
    using guar precond
    by (clarsimp simp add: rel_image_def le_fun_def predTimes3_sepconj_conj_distrib[symmetric]
        split: prod.splits, blast)
qed (simp add: sswa_weaker wssa_stronger)+

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
    \<open>sp ra_ptr_read precond \<le> postcond\<close>
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

  show \<open>sp ?ra' (nofailure_pred precond) \<le> nofailure_pred postcond\<close>
    using assms(1) precond_def postcond_def
    by (force simp add: sp_step_fail_lift_on_nofailure_pred_eq sepconj_conj_def
        points_to_perm_def plus_option_iff)

  show \<open>\<forall>f\<le>nofailure_pred F. sp ?ra' (nofailure_pred precond \<^emph>\<and> f) \<le> nofailure_pred postcond \<^emph>\<^sub>\<triangleright> f\<close>
    unfolding sepconj_left_def ra_ptr_read_def precond_def postcond_def
    apply (clarsimp simp add: sp_step_fail_lift_on_nofailure_pred_eq subset_nofailure_pred_iff
        predTimes3_sepconj_conj_distrib[symmetric] case_option_disj_split)
    apply (clarsimp simp add: sepconj_conj_def points_to_perm_def plus_option_iff)
    apply (metis (mono_tags, lifting) Discr_inverse_iff comp_apply snd_conv sswa_trivial wssa_trivial)
    done

  show
    \<open>rel_image snd
      (rel_liftL (nofailure_pred precond \<squnion> nofailure_pred precond \<^emph>\<and> nofailure_pred F) \<sqinter> ?ra')
    \<le> G \<times>\<^sub>R (=)\<close>
    using assms(5)
    apply (simp only: predTimes3_sepconj_conj_distrib[symmetric] predTimes3_sup_distrib[symmetric])
    apply (unfold ra_ptr_read_def precond_def postcond_def)
    apply (clarsimp simp add: sepconj_conj_def points_to_perm_def plus_option_iff rel_image_def
        le_fun_def ex_disj_distrib all_conj_distrib split: option.splits)
    apply (elim disjE exE conjE)
     apply force
    apply (force simp add: wlp_def plus_option_iff ex_disj_distrib all_conj_distrib)
    done
qed simp+


section \<open> PointerWrite \<close>

definition PointerWrite
  :: \<open>'pt \<Rightarrow> (('x \<Rightarrow> 'v) \<Rightarrow> 'v) \<Rightarrow> (('pt \<rightharpoonup> 'v discr \<times> 'perm) \<times> (('x \<Rightarrow> 'v) \<times> fail_st)) comm\<close>
  where
    \<open>PointerWrite pt e \<equiv>
      Atomic (step_fail_lift (\<lambda>(l, s) (l', s', fl').
        case l pt of
          Some (_, perm) \<Rightarrow> l' = l(pt \<mapsto> (Discr (e s), perm)) \<and> s' = s \<and> fl' = Running
        | None \<Rightarrow> l' = l \<and> s' = s \<and> fl' = Failed
      ))\<close>

\<comment> \<open> Note: need full permissions, *logically*. Otherwise disjointness is not preserved.
  You could also limit the frame specification such that \<open>pt\<close> is guaranteed not to occur.
\<close>
lemma rgsat_pointer_write:
  fixes e pt p R
  defines \<open>ra_ptr_write \<equiv> (\<lambda>(l,s) (l',s'). l' = l(pt \<mapsto> e s) \<and> s' = s)\<close>
  and \<open>precond \<equiv> \<L> (\<Squnion>v. pt \<^bold>\<mapsto> v) \<sqinter> wssa R (\<S> p)\<close>
  and \<open>postcond \<equiv> sswa R ((\<lambda>(ls, ss). (pt \<^bold>\<mapsto> (e ss)) ls) \<sqinter> \<S> p)\<close>
  assumes
    \<open>sp ra_ptr_read precond \<le> postcond\<close>
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
    apply (clarsimp simp add: fun_eq_iff le_fun_def points_to_perm_def wlp_def)
    apply (metis rtranclp_trans)
    done

  show \<open>sswa (R \<times>\<^sub>R (=)) (nofailure_pred postcond) \<le> nofailure_pred postcond\<close>
    unfolding postcond_def
    apply (clarsimp simp add: fun_eq_iff le_fun_def points_to_perm_def sp_def)
    apply (metis rtranclp_trans)
    done

  show \<open>sp ?ra' (nofailure_pred precond) \<le> nofailure_pred postcond\<close>
    using assms(1) precond_def postcond_def
    by (force simp add: sp_step_fail_lift_on_nofailure_pred_eq sepconj_conj_def
        points_to_perm_def plus_option_iff)

  show \<open>\<forall>f\<le>nofailure_pred F. sp ?ra' (nofailure_pred precond \<^emph>\<and> f) \<le> nofailure_pred postcond \<^emph>\<^sub>\<triangleright> f\<close>
    unfolding sepconj_left_def ra_ptr_write_def precond_def postcond_def
    apply (clarsimp simp add: sp_step_fail_lift_on_nofailure_pred_eq subset_nofailure_pred_iff
        predTimes3_sepconj_conj_distrib[symmetric] case_option_disj_split)
    apply (clarsimp simp add: sepconj_conj_def points_to_perm_def plus_option_iff)
    apply (rename_tac ss f' ha hb v v' perm')
    apply (elim disjE conjE exE)
     apply (rule_tac x=\<open>ha(pt \<mapsto> (Discr (e ss), perm'))\<close> in exI)
     apply (rule_tac x=hb in exI)
     apply (force simp add: disjoint_fun_def; fail)
    apply (rule_tac x=\<open>ha(pt \<mapsto> (Discr (e ss), perm'))\<close> in exI)
    apply (rule_tac x=hb in exI)
    apply (intro conjI)
       apply (simp add: disjoint_fun_def)
       apply (metis disjoint_munit_def disjoint_option_simps(1) disjoint_prod_def)
      apply force
     apply force
    apply force
    done

  show
    \<open>rel_image snd
      (rel_liftL (nofailure_pred precond \<squnion> nofailure_pred precond \<^emph>\<and> nofailure_pred F) \<sqinter> ?ra')
    \<le> G \<times>\<^sub>R (=)\<close>
    using assms(5)
    apply (simp only: predTimes3_sepconj_conj_distrib[symmetric] predTimes3_sup_distrib[symmetric])
    apply (unfold ra_ptr_write_def precond_def postcond_def)
    apply (clarsimp simp add: sepconj_conj_def points_to_perm_def plus_option_iff rel_image_def
        le_fun_def ex_disj_distrib all_conj_distrib split: option.splits)
    apply (elim disjE exE conjE)
     apply force
    apply (force simp add: wlp_def plus_option_iff ex_disj_distrib all_conj_distrib)
    done
qed simp+


end