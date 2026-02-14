theory SecLang
  imports Security
begin

section \<open> Security Programs \<close>

definition
  \<open>nonfail_ff p \<equiv>
    \<lambda>(((lx,flx), (ly,fly)), s). p ((lx,ly), s) \<and> flx = Running \<and> fly = Running\<close>


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
  shows \<open>\<top> \<le> quasireflp_steprel (relassert_rel p - rel_liftR (- nonfail_ff \<top>))
    \<longleftrightarrow> quasireflp (curry (p \<circ> exch4))\<close>
  by (force simp add: relassert_rel_def quasireflp_steprel_def sec_agree_exch4_def
      sec_agree_def nonfail_ff_def reflp_on_def prepost_state_def' le_fun_def split: prod.splits)

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

definition \<open>Output h \<equiv> \<langle> output_rel h \<rangle>\<close>

\<comment> \<open> TODO: pin down the exact condition\<close>
lemma output_quasirefl_blocking_steprel:
  \<open>nonfail_ff (\<bbbA>\<^sub>\<ddagger> h) \<le>
    quasirefl_blocking_steprel (output_rel h - rel_liftR (- nonfail_ff \<top>))\<close>
  by (clarsimp simp add: output_rel_def' relassert_rel_def quasirefl_blocking_steprel_def
      pred_lift_exch4_def exch4_def fun_eq_iff sec_agree_exch4_def' nonfail_ff_def)


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