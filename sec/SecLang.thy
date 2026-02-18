theory SecLang
  imports Security
begin


lemma pre_state_eq_eq[simp]:
  \<open>pre_state (=) = \<top>\<close>
  by (simp add: le_fun_def pre_state_eq_changedom_and_refl sup_shunt)

lemma any_shared_pred_times_top_eq[simp]:
  \<open>any_shared (p \<times>\<^sub>P \<top>) = p \<times>\<^sub>P \<top>\<close>
  by (fastforce simp add: any_shared_def)

lemma sepconj_conj_unit_right[simp]:
  fixes p  :: \<open>'l::multiunit_sep_alg \<times> 's \<Rightarrow> bool\<close>
  shows \<open>p \<^emph>\<and> (emp \<times>\<^sub>P \<top>) = p\<close>
  by (clarsimp simp add: sepconj_conj_def emp_def fun_eq_iff)
    (metis sepadd_unit_right unitof_disjoint2 unitof_is_sepadd_unit)

lemma sepconj_conj_unit_left[simp]:
  fixes p  :: \<open>'l::multiunit_sep_alg \<times> 's \<Rightarrow> bool\<close>
  shows \<open>(emp \<times>\<^sub>P \<top>) \<^emph>\<and> p = p\<close>
  by (clarsimp simp add: sepconj_conj_def emp_def fun_eq_iff)
    (metis sepadd_unit_def unitof_disjoint unitof_is_sepadd_unit)


subsection \<open> Pretty double-failure \<close>

definition
  \<open>running2_pred p \<equiv>
    \<lambda>(((lx,flx), (ly,fly)), s). p ((lx,ly), s) \<and> flx = Running \<and> fly = Running\<close>

definition
  \<open>failed2_pred p \<equiv>
    \<lambda>(((lx,flx), (ly,fly)), s). p ((lx,ly), s) \<and> flx = Failed \<and> fly = Failed\<close>

lemma subpred_running2_pred_iff:
  \<open>p \<le> running2_pred q \<longleftrightarrow> (\<exists>q'. q' \<le> q \<and> p = running2_pred q')\<close>
  apply (clarsimp simp add: le_fun_def fun_eq_iff running2_pred_def)
  apply (rule iffI)
   apply (rule_tac x=\<open>\<lambda>((lsx, lsy), ss). p (((lsx, Running), (lsy, Running)), ss)\<close> in exI)
   apply force
  apply force
  done

lemma running2_pred_subpred_internalise:
  \<open>(\<forall>p\<le>running2_pred P. \<Q> p) \<longleftrightarrow> (\<forall>p\<le>P. \<Q> (running2_pred p))\<close>
  by (simp add: subpred_running2_pred_iff) blast

lemma wssa_running2_pred_distrib:
  \<open>wssa R (running2_pred p) = running2_pred (wssa R p)\<close>
  by (force simp add: running2_pred_def wlp_def)

lemma sswa_running2_pred_distrib:
  \<open>sswa R (running2_pred p) = running2_pred (sswa R p)\<close>
  by (force simp add: running2_pred_def sp_def)

lemma any_shared_running2_pred_distrib:
  \<open>any_shared (running2_pred p) = running2_pred (any_shared p)\<close>
  by (force simp add: running2_pred_def)

lemma running2_pred_mono[simp]:
  \<open>running2_pred p \<le> running2_pred q \<longleftrightarrow> p \<le> q\<close>
  by (force simp add: running2_pred_def)

lemma running2_pred_sepconj_conj_distrib:
  \<open>running2_pred p \<^emph>\<and> running2_pred q = running2_pred (p \<^emph>\<and> q)\<close>
  by (force simp add: running2_pred_def sepconj_conj_apply)

lemma failure2_implies_running2_iff[simp]:
  \<open>failed2_pred p \<le> running2_pred q \<longleftrightarrow> \<top> \<le> - p\<close>
  by (simp add: failed2_pred_def running2_pred_def le_fun_def all_fail_st_eq)


abbreviation ff_rgsat_pretty
  (\<open>_, _, _, _, _ \<turnstile>\<^sub>f\<^sub>f { _ } _ { _ }\<close> [55, 0, 0, 0, 0, 55, 55, 55] 56) where
  \<open>R, G, I, F, T \<turnstile>\<^sub>f\<^sub>f { p } c { q } \<equiv>
    rgsat c R G
      (running2_pred p) (running2_pred q)
      (running2_pred I) (running2_pred F)
      T\<close>

lemmas ff_rgsat_weaken =
  rgsat_weaken[where
    p'=\<open>running2_pred p'\<close> and q'=\<open>running2_pred q'\<close> and
    I'=\<open>running2_pred I'\<close> and F'=\<open>running2_pred F'\<close> and
    p=\<open>running2_pred p\<close> and q=\<open>running2_pred q\<close> and
    I=\<open>running2_pred I\<close> and F=\<open>running2_pred F\<close> for p q I F p' q' I' F', simplified]



subsection \<open> Await \<close>

lemma await_quasireflp_steprel:
  \<open>\<top> \<le> quasireflp_steprel (await_rel (\<lblot> p \<rblot>\<^sub>\<ddagger>))\<close>
  by (force simp add: await_rel_def quasireflp_steprel_def reflp_on_def prepost_state_def'
      pred_lift_exch4_def)

lemma await_symp_steprel:
  \<open>\<top> \<le> symp_steprel (await_rel (\<lblot> p \<rblot>\<^sub>\<ddagger>))\<close>
  by (force simp add: await_rel_def symp_steprel_def pred_lift_exch4_def)

\<comment> \<open> If do-loops are only formed via lifting of awaits, this will be the only rule necessary. \<close>
lemma await_pred_lift_quasirefl_blocking_steprel:
  \<open>quasirefl_blocking_steprel (await_rel \<lblot> p \<rblot>\<^sub>\<ddagger>) = \<bbbA>\<^sub>\<ddagger> p\<close>
  by (force simp add: await_rel_def quasirefl_blocking_steprel_def
      pred_lift_exch4_def exch4_def fun_eq_iff sec_agree_exch4_def')


subsection \<open> Relational Assertion \<close>

definition relassert_rel
  :: \<open>(('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow>
      (('l \<times> fail_st, 's) rgstate \<Rightarrow> ('l \<times> fail_st, 's) rgstate \<Rightarrow> bool)\<close>
  where
  \<open>relassert_rel p \<equiv>
    \<lambda>(((lx,flx), (ly,fly)), s) (((lx',flx'), (ly',fly')), s').
      lx' = lx \<and> ly' = ly \<and> s' = s \<and>
        ((p ((lx,ly),s) \<or> flx = Failed \<or> fly = Failed) \<and> flx' = flx \<and> fly' = fly \<or>
          flx = Running \<and> fly = Running \<and> \<not> p ((lx,ly), s) \<and> flx' = Failed \<and> fly' = Failed)\<close>

abbreviation RelAssert :: \<open>(('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow> ('l \<times> fail_st, 's) rgstate comm\<close> where
  \<open>RelAssert p \<equiv> \<langle> relassert_rel p \<rangle>\<close>

\<comment> \<open> We subtract off the post-states where the program crashes, as we assume these will always be
    avoided. \<close>
lemma rel_assert_quasireflp_steprel:
  fixes p :: \<open>('a \<times> 'a) \<times> ('b \<times> 'b) \<Rightarrow> bool\<close>
  shows \<open>\<top> \<le> quasireflp_steprel (relassert_rel p - rel_liftR (- running2_pred \<top>))
    \<longleftrightarrow> quasireflp (curry (p \<circ> exch4))\<close>
  by (force simp add: relassert_rel_def quasireflp_steprel_def sec_agree_exch4_def
      sec_agree_def running2_pred_def reflp_on_def prepost_state_def' le_fun_def split: prod.splits)

lemma rel_assert_symp_steprel:
  \<open>\<top> \<le> symp_steprel (relassert_rel p) \<longleftrightarrow> symp (curry (p \<circ> exch4))\<close>
  by (clarsimp simp add: relassert_rel_def symp_steprel_def sec_agree_exch4_def symp_def le_fun_def
      split: prod.splits, blast)


subsection \<open> Output \<close>

definition output_rel
  :: \<open>('l \<times> 's \<Rightarrow> 'v) \<Rightarrow>
        (('l \<times> fail_st, 's) rgstate \<Rightarrow> ('l \<times> fail_st, 's) rgstate \<Rightarrow> bool)\<close>
  where
    \<open>output_rel h \<equiv> relassert_rel (\<bbbA>\<^sub>\<ddagger> h)\<close>

lemmas output_rel_def' =
  relassert_rel_def[where p=\<open>\<bbbA>\<^sub>\<ddagger> h\<close> for h, simplified output_rel_def[symmetric]]

abbreviation \<open>Output h \<equiv> \<langle> output_rel h \<rangle>\<close>

\<comment> \<open> TODO: pin down the exact condition\<close>
lemma output_quasirefl_blocking_steprel:
  \<open>running2_pred (\<bbbA>\<^sub>\<ddagger> h) \<le>
    quasirefl_blocking_steprel (output_rel h - rel_liftR (- running2_pred \<top>))\<close>
  by (clarsimp simp add: output_rel_def' relassert_rel_def quasirefl_blocking_steprel_def
      pred_lift_exch4_def exch4_def fun_eq_iff sec_agree_exch4_def' running2_pred_def)

lemma sp_output_rel_running2_pred_eq:
  \<open>sp (output_rel h) (running2_pred p) = running2_pred (\<bbbA>\<^sub>\<ddagger> h \<sqinter> p) \<squnion> failed2_pred (- \<bbbA>\<^sub>\<ddagger> h \<sqinter> p)\<close>
  by (force split: prod.splits simp add: sp_def output_rel_def' fun_eq_iff conj_disj_distribR
      running2_pred_def failed2_pred_def)


lemma rgsat_output:
  assumes main:
    \<open>wssa R p \<^emph>\<and> F \<le> \<bbbA>\<^sub>\<ddagger> h\<close>
    \<open>rel_image snd (rel_liftL (wssa R p \<^emph>\<and> F) \<sqinter> (=)) \<le> G\<close>
    \<open>wssa R p \<le> I\<close>
    and misc:
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f\<^sub>f { wssa R p } Output h { wssa R p }\<close>
  using misc
proof (intro rgsat_atom[where p=\<open>running2_pred p\<close> and q=\<open>running2_pred (wssa R p)\<close>])
  show \<open>running2_pred (wssa R p) \<le> wssa R (running2_pred p)\<close>
    by (simp add: wssa_running2_pred_distrib)
  show \<open>sswa R (running2_pred (wssa R p)) \<le> running2_pred (wssa R p)\<close>
    by (simp add: sswa_running2_pred_distrib)

  show \<open>\<forall>f\<le>running2_pred F.
       sp (output_rel h) (wssa R (running2_pred p) \<^emph>\<and> f) \<le> running2_pred (wssa R p) \<^emph>\<and> any_shared f\<close>
    using main(1)
    apply (simp add: running2_pred_subpred_internalise wssa_running2_pred_distrib
        running2_pred_sepconj_conj_distrib  sp_output_rel_running2_pred_eq
        any_shared_running2_pred_distrib all_conj_distrib imp_conjR)
    apply (rule conjI)
     apply (simp add: le_infI2 self_implies_self_any_shared sepconj_conj_monoR; fail)
    apply (simp add: shunt2[symmetric] atom_variant_compressed_frame(1))
    done
  show \<open>rel_image snd (rel_liftL (wssa R (running2_pred p) \<^emph>\<and> running2_pred F) \<sqinter> output_rel h) \<le> G\<close>
    using main(1-2)
    apply (simp add: wssa_running2_pred_distrib running2_pred_sepconj_conj_distrib output_rel_def')
    apply (force simp add: running2_pred_def le_fun_def)
    done

  show \<open>wssa R (running2_pred p) \<le> running2_pred I\<close>
    using main
    by (simp add: wssa_running2_pred_distrib)
  show \<open>sswa R (running2_pred (wssa R p)) \<le> running2_pred I\<close>
    using main
    by (simp add: sswa_running2_pred_distrib)
qed simp+


section \<open> Secure If-statement \<close>

\<comment> \<open> The program produced by \<open>liftC (IfThenElse p)\<close> \<close>
definition \<open>SecIfThenElse p ct cf \<equiv> Await (\<lblot> p \<rblot>) ;; ct \<^bold>\<box> Await (\<lblot> -p \<rblot>) ;; cf\<close>

lemma SecIfThenElse_inject[simp]:
  \<open>SecIfThenElse p1 ct1 cf1 = SecIfThenElse p2 ct2 cf2 \<longleftrightarrow> p1 = p2 \<and> ct1 = ct2 \<and> cf1 = cf2\<close>
  by (clarsimp simp add: SecIfThenElse_def await_rel_def fun_eq_iff) blast

lemma SecIfThenElse_distinct[simp]:
  \<open>SecIfThenElse p ct cf \<noteq> Skip\<close>
  \<open>SecIfThenElse p ct cf \<noteq> c1 ;; c2\<close>
  \<open>SecIfThenElse p ct cf \<noteq> c1 \<parallel> c2\<close>
  \<open>SecIfThenElse p ct cf \<noteq> \<langle>ar\<rangle>\<close>
  \<open>Skip \<noteq> SecIfThenElse p ct cf\<close>
  \<open>c1 ;; c2 \<noteq> SecIfThenElse p ct cf\<close>
  \<open>c1 \<parallel> c2 \<noteq> SecIfThenElse p ct cf\<close>
  \<open>\<langle>ar\<rangle> \<noteq> SecIfThenElse p ct cf\<close>
  by (simp add: SecIfThenElse_def)+

lemma gensep_rule_sec_if_then_else:
  assumes
    \<open>rel_image snd (rel_liftL (sswa R p \<^emph>\<and> F) \<sqinter> (=)) \<le> G\<close>
    and tt_guard_frame_cond:
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> \<lblot> pa \<rblot> \<le> (sswa R p \<sqinter> \<lblot> pa \<rblot>) \<^emph>\<and> any_shared f\<close>
    and ff_guard_frame_cond:
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> \<lblot> -pa \<rblot> \<le> (sswa R p \<sqinter> \<lblot> -pa \<rblot>) \<^emph>\<and> any_shared f\<close> 
    and body_assms:
    \<open>R, G, I, F, T \<turnstile> { sswa R (sswa R p \<sqinter> \<lblot> pa \<rblot>) } ctt { q }\<close>
    \<open>R, G, I, F, T \<turnstile> { sswa R (sswa R p \<sqinter> \<lblot> -pa \<rblot>) } cff { q }\<close>
    and misc_assms:
    \<open>T RGSepWeaken\<close>
    \<open>T RGSepAtom\<close>
    \<open>T RGSepEndet\<close>
    \<open>T RGSepSeq\<close>
    \<open>sswa R p \<le> I\<close>
  shows
    \<open>R, G, I, F, T \<turnstile> { p } SecIfThenElse pa ctt cff { q }\<close>
  using misc_assms
  unfolding SecIfThenElse_def
proof (intro rgsat_weaken_prepost[where p=p and p'=\<open>sswa R p\<close> and q=q and q'=q],
    intro rgsat_endet[OF rgsat_seq rgsat_seq order.refl order.refl,
      where I=I and Ia=\<open>sswa R p \<squnion> I\<close> and Ib=\<open>sswa R p \<squnion> I\<close>])
  show \<open>R, G, sswa R p, F, T \<turnstile> { sswa R p } Await (\<lblot> pa \<rblot>) { sswa R (sswa R p \<sqinter> \<lblot> pa \<rblot>) }\<close>
    using misc_assms assms(1) tt_guard_frame_cond
    apply (intro rgsat_atom[where p=\<open>sswa R p\<close> and q=\<open>sswa R p \<sqinter> \<lblot> pa \<rblot>\<close>])
          apply force
         apply force
        apply (simp add: inf_commute[of \<open>\<lblot> pa \<rblot>\<close>]; fail)
       apply (simp add: await_rel_def inf_left_commute le_infI2 rel_image_snd_galois; fail)
      apply force
     apply (metis order.refl inf_sup_aci(1) inf_sup_ord(2) wlp_weaker_iff_sp_stronger
        wssa_over_sswa_eq)
    apply force
    done
  show \<open>R, G, I, F, T \<turnstile> { sswa R (sswa R p \<sqinter> \<lblot> pa \<rblot>) } ctt { q }\<close>
    using body_assms
    by blast
  show \<open>R, G, sswa R p, F, T \<turnstile> { sswa R p } Await (\<lblot> -pa \<rblot>) { sswa R (sswa R p \<sqinter> \<lblot> -pa \<rblot>) }\<close>
    using ff_guard_frame_cond misc_assms assms
    apply (intro rgsat_atom[where p=\<open>sswa R p\<close> and q=\<open>sswa R p \<sqinter> \<lblot> -pa \<rblot>\<close>])
          apply force
         apply force
        apply (simp add: inf_commute[of \<open>\<lblot> - pa \<rblot>\<close>]; fail)
       apply (simp add: await_rel_def inf_left_commute le_infI2 rel_image_snd_galois; fail)
      apply force
     apply (metis order.refl inf_sup_aci(1) inf_sup_ord(2) wlp_weaker_iff_sp_stronger
        wssa_over_sswa_eq)
    apply force
    done
  show \<open>R, G, I, F, T \<turnstile> { sswa R (sswa R p \<sqinter> \<lblot> -pa \<rblot>) } cff { q }\<close>
    using body_assms
    by blast
  show \<open>p \<le> sswa R p\<close>
    by blast
qed simp+


section \<open> Declassification \<close>

definition declassify_rel
  :: \<open>('l \<times> 's \<Rightarrow> 'v) \<Rightarrow> (('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool)\<close>
  where
    \<open>declassify_rel h \<equiv> await_rel (\<bbbA>\<^sub>\<ddagger> h)\<close>

lemmas declassify_rel_def' =
  await_rel_def[where p=\<open>\<bbbA>\<^sub>\<ddagger> h\<close> for h, simplified declassify_rel_def[symmetric]]

abbreviation \<open>Declassify h \<equiv> \<langle> declassify_rel h \<rangle>\<close>

lemma declassify_quasireflp_steprel:
  \<open>\<top> \<le> quasireflp_steprel (declassify_rel h)\<close>
  by (clarsimp simp add: declassify_rel_def' await_rel_def quasireflp_steprel_def reflp_on_def
      prepost_state_def' sec_agree_exch4_def')

lemma declassify_symp_steprel:
  \<open>\<top> \<le> symp_steprel (declassify_rel h)\<close>
  by (clarsimp simp add: declassify_rel_def' await_rel_def symp_steprel_def sec_agree_exch4_def')

lemma declassify_quasirefl_blocking_steprel:
  \<open>quasirefl_blocking_steprel (declassify_rel h) = \<bbbA>\<^sub>\<ddagger> h\<close>
  by (clarsimp simp add: declassify_rel_def' await_rel_def quasirefl_blocking_steprel_def
      sec_agree_exch4_def' exch4_def)


lemma rgsat_declassify:
  assumes
    \<open>\<forall>f\<le>F. (wssa R p \<^emph>\<and> f) \<sqinter> \<bbbA>\<^sub>\<ddagger> h \<le> (p \<sqinter> \<bbbA>\<^sub>\<ddagger> h) \<^emph>\<and> any_shared f\<close>
    \<open>rel_image snd (rel_liftL ((wssa R p \<^emph>\<and> F) \<sqinter> \<bbbA>\<^sub>\<ddagger> h) \<sqinter> (=)) \<le> G\<close>
    \<open>wssa R p \<le> I\<close>
    \<open>sswa R (p \<sqinter> \<bbbA>\<^sub>\<ddagger> h) \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile> { wssa R p } Declassify h { sswa R (p \<sqinter> \<bbbA>\<^sub>\<ddagger> h) }\<close>
  using assms(3-)
proof (intro rgsat_atom[OF order.refl order.refl])
  show \<open>\<forall>f\<le>F. sp (declassify_rel h) (wssa R p \<^emph>\<and> f) \<le> (p \<sqinter> \<bbbA>\<^sub>\<ddagger> h) \<^emph>\<and> any_shared f\<close>
    using assms(1)
    by (clarsimp simp add: sp_def declassify_rel_def) blast
  show \<open>rel_image snd (rel_liftL (wssa R p \<^emph>\<and> F) \<sqinter> declassify_rel h) \<le> G\<close>
    using assms(2)
    by (force simp add: declassify_rel_def')
qed simp+

lemma declassify_as_assume_helper:
  \<open>\<forall>f\<le>emp \<times>\<^sub>P \<top>. (\<top> \<^emph>\<and> f) \<sqinter> \<bbbA>\<^sub>\<ddagger> h \<le> \<bbbA>\<^sub>\<ddagger> h \<^emph>\<and> any_shared f\<close>
  apply (clarsimp simp add: le_fun_def emp_def sepconj_conj_def)
  apply (metis sepadd_unit_right)
  done

lemmas declassify_as_assume =
  rgsat_declassify[where R=\<open>(=)\<close> and p=\<open>\<top>\<close> and h=\<open>h :: ('l::multiunit_sep_alg \<times> 's) \<Rightarrow> bool\<close>
                    and I=\<open>\<top>\<close> and F=\<open>emp \<times>\<^sub>P \<top>\<close> for h, simplified, OF declassify_as_assume_helper]


section \<open> Purely Relational \<close>

definition purely_relational
  :: \<open>(('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
    \<open>purely_relational ar \<equiv>
      (\<forall>z x' y'. (ar \<circ>\<^sub>2 exch4) (z,z) (x',y') \<longrightarrow> x' = z \<and> y' = z)\<close>

lemma purely_relational_output:
  \<open>purely_relational (output_rel h)\<close>
  by (simp add: output_rel_def' purely_relational_def sec_agree_exch4_def')

lemma await_agree_purely_relational:
  \<open>purely_relational (await_rel p)\<close>
  by (clarsimp simp add: await_rel_def purely_relational_def)

lemma purely_relational_atom_unlifts_to_nop:
  \<open>purely_relational ar \<Longrightarrow>
    unliftC \<langle> ar \<rangle> = \<langle> rel_liftL (pre_state ar \<circ> exch4 \<circ> \<Delta>) \<sqinter> (=) \<rangle>\<close>
  by (force simp add: purely_relational_def fun_eq_iff pre_state_def)


section \<open> Pair Step \<close>

definition pair_step
  :: \<open>(('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
    \<open>pair_step rr \<equiv> (\<exists>r. rr \<circ>\<^sub>2 exch4 = liftR r)\<close>


end