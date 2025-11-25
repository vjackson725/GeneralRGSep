theory RGLogicEx
  imports "../RGLogic"
begin

subsection \<open> Heap predicate \<close>

definition points_to
  :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b \<times> 'perm) \<Rightarrow> bool\<close>
  (infix \<open>\<^bold>\<mapsto>\<close> 90)
  where
  \<open>p \<^bold>\<mapsto> v \<equiv> \<lambda>h. \<exists>perm. h p = Some (v, perm)\<close>


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


lemma sp_triple_relTimes_predTimes3_eq[simp]:
  \<open>sp (ra \<times>\<^sub>R (rb \<times>\<^sub>R rc)) (p \<times>\<^sub>P\<^sub>3 q) = sp (ra \<times>\<^sub>R rb) p \<times>\<^sub>P\<^sub>3 sp rc q\<close>
  by (force simp add: sp_def pred_Times_third_def)

lemma reflp_wlp_equals_predTimes3_eq[simp]:
  \<open>reflp ra \<Longrightarrow> reflp rb \<Longrightarrow>
    wlp (ra \<times>\<^sub>R rb \<times>\<^sub>R (=)) (p \<times>\<^sub>P\<^sub>3 q) = wlp (ra \<times>\<^sub>R rb) p \<times>\<^sub>P\<^sub>3 q\<close>
  by (force simp add: wlp_def pred_Times_third_def fun_eq_iff reflp_def)

lemma predTimes3_sepconj_conj_distrib:
  \<open>(p \<^emph>\<and> f) \<times>\<^sub>P\<^sub>3 q = p \<times>\<^sub>P\<^sub>3 q \<^emph>\<and> f \<times>\<^sub>P\<^sub>3 q\<close>
  by (force simp add: pred_Times_third_def sepconj_conj_apply fun_eq_iff)

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

lemma sp_failure_healthy_rel_eq:
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
    \<open>\<forall>f\<le>F. sswa R p \<^emph>\<and> f \<le> q \<^emph>\<and> f\<close>
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
    by (clarsimp simp add: fun_eq_iff le_fun_def sp_failure_healthy_rel_eq)

  show
    \<open>\<forall>f\<le>nofailure_pred F.
       sp ?ra' (sswa (R \<times>\<^sub>R (=)) (nofailure_pred p) \<^emph>\<and> f) \<le> nofailure_pred (sswa R p) \<^emph>\<and> f\<close>
    using precond
    by (simp add: all_impl_nofailure_pred_internalise
        predTimes3_sepconj_conj_distrib[symmetric] sp_failure_healthy_rel_eq,
        fastforce simp add: le_fun_def sepconj_conj_apply)

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

lemma case_option_disj_split:
  \<open>(case ma of None \<Rightarrow> p | Some a \<Rightarrow> q a) \<longleftrightarrow>
    ma = None \<and> p \<or> (\<exists>a. ma = Some a \<and> q a)\<close>
  by (metis case_optionE option.simps(4,5))


lemma rgsat_pointer_read:
(*
  assumes precond:
    \<open>sswa R p \<le> pa\<close>
    \<open>sswa R p \<^emph>\<and> F \<le> pa\<close>
    and step:
    \<open>sswa R p \<le> q\<close>
    \<open>\<forall>f\<le>F. sswa R p \<^emph>\<and> f \<le> q \<^emph>\<and> f\<close>
    and guar:
    \<open>rel_image snd (rel_liftL (sswa R p \<squnion> sswa R p \<^emph>\<and> F) \<sqinter> (=)) \<le> G\<close>
    and misc:
    \<open>sswa R p \<le> I\<close>
    \<open>sswa R q \<le> I\<close>
*)
  assumes
    \<open>T RGSepAtom\<close>
    \<open>\<forall>ls ss. F (ls, ss) \<le> F (ls, ss(x := v))\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f
      { \<L> (pt \<^bold>\<mapsto> Discr v) \<sqinter> wssa R (\<S> (\<lambda>s. p (s(x := v)))) }
        PointerRead x pt
      { \<L> (pt \<^bold>\<mapsto> Discr v) \<sqinter> sswa R (\<S> p) }\<close>
  using assms
  unfolding PointerRead_def
proof (intro rgsat_atom[where
      p=\<open>nofailure_pred (\<L> (pt \<^bold>\<mapsto> Discr v) \<sqinter> \<S> (\<lambda>s. p (s(x := v))))\<close> and
      q=\<open>nofailure_pred (\<L> (pt \<^bold>\<mapsto> Discr v) \<sqinter> \<S> p)\<close>
      ])
  let ?ra' = \<open>step_fail_lift (\<lambda>(l, s) (l', s', fl').
               case l pt of None \<Rightarrow>
                  l' = l \<and> s' = s \<and> fl' = Failed
               | Some (v, xa) \<Rightarrow>
                  l' = l \<and> s' = s(x := the_discr v) \<and> fl' = Running)\<close>

  show
    \<open>nofailure_pred (\<L> (pt \<^bold>\<mapsto> Discr v) \<sqinter> wssa R (\<S> (\<lambda>s. p (s(x := v))))) \<le>
      wssa (R \<times>\<^sub>R (=)) (nofailure_pred (\<L> (pt \<^bold>\<mapsto> Discr v) \<sqinter> \<S> (\<lambda>s. p (s(x := v)))))\<close>
    by (simp add: wlp_inf)

  show
    \<open>sswa (R \<times>\<^sub>R (=)) (nofailure_pred (\<L> (pt \<^bold>\<mapsto> Discr v) \<sqinter> \<S> p )) \<le>
      nofailure_pred (\<L> (pt \<^bold>\<mapsto> Discr v) \<sqinter> sswa R ( \<S> p ))\<close>
    by (metis (no_types, opaque_lifting) inf.bounded_iff predTimes3_eqVal_le_iff
        rel_times_right_eq_rtranclp_distrib sp_eq_rel sp_inf_semidistrib
        sp_triple_relTimes_predTimes3_eq wlp_weaker_iff_sp_stronger wssa_ignore_local)

  show
    \<open>\<forall>f\<le>nofailure_pred F.
      sp ?ra' (nofailure_pred (\<L> (pt \<^bold>\<mapsto> Discr v) \<sqinter> \<S> (\<lambda>s. p (s(x := v)))) \<^emph>\<and> f)
        \<le> nofailure_pred (\<L> (pt \<^bold>\<mapsto> Discr v) \<sqinter> \<S> p) \<^emph>\<and> f\<close>
    apply (simp add: atom_variant_pointwise_frame(2))
    apply (clarsimp simp add: sp_failure_healthy_rel_eq subset_nofailure_pred_iff
        predTimes3_sepconj_conj_distrib[symmetric] case_option_disj_split)
    apply (clarsimp simp add: sepconj_conj_def points_to_def plus_option_iff)
     apply (rename_tac ss ha hb perm)
    sorry

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

lemma rgsat_pointer_write:
  assumes precond:
    \<open>sswa R p \<le> pa\<close>
    \<open>sswa R p \<^emph>\<and> F \<le> pa\<close>
    and step:
    \<open>sswa R p \<le> q\<close>
    \<open>\<forall>f\<le>F. sswa R p \<^emph>\<and> f \<le> q \<^emph>\<and> f\<close>
    and guar:
    \<open>rel_image snd (rel_liftL (sswa R p \<squnion> sswa R p \<^emph>\<and> F) \<sqinter> (=)) \<le> G\<close>
    and misc:
    \<open>sswa R p \<le> I\<close>
    \<open>sswa R q \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f
      {(\<lambda>(ls, ss). pt \<^bold>\<mapsto> v) \<^emph>\<and> \<S> p )}
        PointerWrite pt e
      {(\<lambda>(ls, ss). pt \<^bold>\<mapsto> v \<^emph>\<and> \<S> sp )}\<close>
  using assms
  unfolding Assert_def
proof (intro rgsat_atom[where q=\<open>nofailure_pred (sswa R p)\<close>])
  let ?ra' = \<open>(failure_healthy_rel
            (\<lambda>(l, s) (l', s', k').
                l' = l \<and>
                s' = s \<and> (pa (l, s) \<and> k' = Running \<or> \<not> pa (l, s) \<and> k' = Failed)))\<close>

  show
    \<open>sp ?ra' (sswa (R \<times>\<^sub>R (=)) (nofailure_pred p)) \<le> nofailure_pred (sswa R p)\<close>
    using precond
    by (clarsimp simp add: fun_eq_iff le_fun_def sp_failure_healthy_rel_eq)

  show
    \<open>\<forall>f\<le>nofailure_pred F.
       sp ?ra' (sswa (R \<times>\<^sub>R (=)) (nofailure_pred p) \<^emph>\<and> f) \<le> nofailure_pred (sswa R p) \<^emph>\<and> f\<close>
    using precond
    by (simp add: all_impl_nofailure_pred_internalise
        predTimes3_sepconj_conj_distrib[symmetric] sp_failure_healthy_rel_eq,
        fastforce simp add: le_fun_def sepconj_conj_apply)

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


end