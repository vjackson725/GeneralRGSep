theory SecurityEx
  imports "../sec/Security"
begin

lemma parallel_inheritance:
  \<open>sswa (R \<squnion> Gb) Ia \<le> Ia \<Longrightarrow>
    sswa (R \<squnion> Ga) Ib \<le> Ib \<Longrightarrow>
    Ia \<^emph>\<and> (Ib \<squnion> Ib \<^emph>\<and> F) \<le> X \<Longrightarrow>
    Ib \<^emph>\<and> (Ia \<squnion> Ia \<^emph>\<and> F) \<le> X \<Longrightarrow>
    sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib \<le> I \<Longrightarrow>
    I \<^emph>\<and> F \<le> X\<close>
  nitpick
  sorry

lemma eq_rtimes_R_iff:
  \<open>((=) \<times>\<^sub>R r) s s' \<longleftrightarrow> r (snd s) (snd s') \<and> fst s = fst s'\<close>
  by (cases s, cases s', force)

lemma top_rtimes_R_iff:
  \<open>(\<top> \<times>\<^sub>R r) s s' \<longleftrightarrow> r (snd s) (snd s')\<close>
  by (cases s, cases s', force)


definition
  \<open>atom_rel c \<equiv> THE ar. c = \<langle>ar\<rangle>\<close>

abbreviation(input)
  \<open>atom_guard c \<equiv> pre_state (atom_rel c)\<close>

lemma atom_rel_atom_eq[simp]:
  \<open>atom_rel \<langle>ar\<rangle> = ar\<close>
  by (simp add: atom_rel_def)


lemma sepconj_comp_exch4_distrib:
  \<open>(p \<^emph> q) \<circ> exch4 = (p \<circ> exch4) \<^emph> (q \<circ> exch4)\<close>
  by (force simp add: fun_eq_iff sepconj_def)

lemma sp_times_distrib[simp]:
  \<open>sp (Ra \<times>\<^sub>R Rb) (pa \<times>\<^sub>P pb) = sp Ra pa \<times>\<^sub>P sp Rb pb\<close>
  by (force simp add: sp_def fun_eq_iff)

lemma sp_rtrancl_times_semidistrib:
  \<open>sp (Ra \<times>\<^sub>R Rb)\<^sup>*\<^sup>* (pa \<times>\<^sub>P pb) \<le> sp Ra\<^sup>*\<^sup>* pa \<times>\<^sub>P sp Rb\<^sup>*\<^sup>* pb\<close>
  by (metis rel_times_rtranclp_semidistrib sp_rel_mono sp_times_distrib)

lemma sswa_rel_times_prod_times_exch4_semidistrib:
  \<open>sswa (Ra \<times>\<^sub>R Rb) (\<lblot> p \<rblot>\<^sub>\<ddagger>) \<le> (sswa Ra p \<times>\<^sub>P sswa Rb p) \<circ> exch4\<close>
  oops

lemma rel_times_sup_semidistrib:
  \<open>(ra \<times>\<^sub>R rb) \<squnion> (ra \<times>\<^sub>R rb) \<le> (ra \<squnion> rb) \<times>\<^sub>R (ra \<squnion> rb)\<close>
  by (simp add: le_fun_def)

lemma sp_exch4_of_rel_Times_eq[simp]:
  \<open>sp ((r \<times>\<^sub>R r) \<circ>\<^sub>2 exch4) \<lblot> p \<rblot>\<^sub>\<ddagger> = \<lblot> sp r p \<rblot>\<^sub>\<ddagger>\<close>
  (* by (force simp add: fun_eq_iff sp_def) *)
  oops

definition
  \<open>nonfail_ff p \<equiv> \<lambda>(l, ((sx,flx), (sy,fly))). p (l,(sx,sy)) \<and> flx = Running \<and> fly = Running\<close>

definition
  \<open>nonfail_rel_lift_ff r \<equiv>
    \<lambda>(l, ((sx,flx), (sy,fly))) (l', ((sx',flx'), (sy',fly'))).
      flx = Running \<and> fly = Running \<and> r (l,(sx,sy)) (l',(sx',sy')) \<and> flx' = Running \<and> fly' = Running \<or>
      (flx = Failed \<or> fly = Failed) \<and> flx' = flx \<and> fly' = fly \<or>
      \<not> r (l,(sx,sy)) (l',(sx',sy')) \<and> flx' = Failed \<and> fly' = Failed\<close>

definition RelAssert :: \<open>(('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow> ('l, 's \<times> fail_st) rgstate comm\<close> where
  \<open>RelAssert p \<equiv>
    \<langle>\<lambda>(l, ((sx,flx), (sy,fly))) (l', (sx',flx'), (sy',fly')).
      l' = l \<and> sx' = sx \<and> sy' = sy \<and>
        ((p (l,(sx,sy)) \<or> flx = Failed \<or> fly = Failed) \<and> flx' = flx \<and> fly' = fly \<or>
          flx = Running \<and> fly = Running \<and> \<not> p (l,(sx,sy)) \<and> flx' = Failed \<and> fly' = Failed)\<rangle>\<close>

\<comment> \<open> We subtract off the post-states where the program crashes, as we assume these will always be
    avoided. \<close>
lemma rel_assert_quasireflp_steprel:
  fixes p :: \<open>('a \<times> 'a) \<times> 'b \<times> 'b \<Rightarrow> bool\<close>
  shows \<open>\<top> \<le> quasireflp_steprel (atom_rel (RelAssert p) - rel_liftR (- nonfail_ff \<top>))
    \<longleftrightarrow> quasireflp (curry (p \<circ> exch4))\<close>
  by (force simp add: RelAssert_def quasireflp_steprel_def sec_agree_exch4_def
      sec_agree_def nonfail_ff_def reflp_on_def prepost_state_def' le_fun_def split: prod.splits)

lemma rel_assert_symp_steprel:
  \<open>\<top> \<le> symp_steprel (atom_rel (RelAssert p))
    \<longleftrightarrow> symp (curry (p \<circ> exch4))\<close>
  by (clarsimp simp add: RelAssert_def symp_steprel_def sec_agree_exch4_def symp_def le_fun_def
      split: prod.splits, blast)


definition Output :: \<open>('l \<times> 's \<Rightarrow> 'v) \<Rightarrow> ('l, 's \<times> fail_st) rgstate comm\<close> where
  \<open>Output h \<equiv> RelAssert (\<bbbA>\<^sub>\<ddagger> h)\<close>

\<comment> \<open> TODO: pin down the exact condition\<close>
lemma output_quasirefl_blocking_steprel:
  \<open>nonfail_ff (\<bbbA>\<^sub>\<ddagger> h) \<le>
    quasirefl_blocking_steprel (atom_rel (Output h) - rel_liftR (- nonfail_ff \<top>))\<close>
  by (clarsimp simp add: Output_def RelAssert_def quasirefl_blocking_steprel_def
      pred_lift_exch4_def exch4_def fun_eq_iff sec_agree_exch4_def' nonfail_ff_def)


section \<open> Secure If-statement \<close>

lemma await_quasireflp_steprel:
  \<open>\<top> \<le> quasireflp_steprel (atom_rel (Await (\<lblot> p \<rblot>\<^sub>\<ddagger>)))\<close>
  by (force simp add: Await_def quasireflp_steprel_def reflp_on_def prepost_state_def'
      pred_lift_exch4_def)

lemma await_symp_steprel:
  \<open>\<top> \<le> symp_steprel (atom_rel (Await (\<lblot> p \<rblot>\<^sub>\<ddagger>)))\<close>
  by (force simp add: Await_def symp_steprel_def pred_lift_exch4_def)

\<comment> \<open> The only qrefl blocking condition that is going to occur when all do-loops are lifted. \<close>
lemma await_pred_lift_quasirefl_blocking_steprel:
  \<open>quasirefl_blocking_steprel (atom_rel (Await (\<lblot> p \<rblot>\<^sub>\<ddagger>))) = \<bbbA>\<^sub>\<ddagger> p\<close>
  by (force simp add: Await_def quasirefl_blocking_steprel_def
      pred_lift_exch4_def exch4_def fun_eq_iff sec_agree_exch4_def')


\<comment> \<open> The program produced by \<open>liftC (IfThenElse p)\<close> \<close>
definition \<open>SecIfThenElse p ct cf \<equiv> Await (\<lblot> p \<rblot>) ;; ct \<^bold>\<box> Await (\<lblot> -p \<rblot>) ;; cf\<close>

lemma ecIfThenElse_inject[simp]:
  \<open>SecIfThenElse p1 ct1 cf1 = SecIfThenElse p2 ct2 cf2 \<longleftrightarrow> p1 = p2 \<and> ct1 = ct2 \<and> cf1 = cf2\<close>
  by (force simp add: SecIfThenElse_def fun_eq_iff)

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
    \<open>rel_image snd (rel_liftL (sswa R p \<squnion> sswa R p \<^emph>\<and> F) \<sqinter> (=)) \<le> G\<close>
    and tt_guard_frame_cond:
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> \<lblot> pa \<rblot> \<le> (sswa R p \<sqinter> \<lblot> pa \<rblot>) \<^emph>\<and> f\<close>
    and ff_guard_frame_cond:
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> \<lblot> -pa \<rblot> \<le> (sswa R p \<sqinter> \<lblot> -pa \<rblot>) \<^emph>\<and> f\<close> 
    and body_assms:
    \<open>R, G, I, F, T \<turnstile> { sswa R (sswa R p \<sqinter> \<lblot> pa \<rblot>) } ctt { q }\<close>
    \<open>R, G, I, F, T \<turnstile> { sswa R (sswa R p \<sqinter> \<lblot> -pa \<rblot>) } cff { q }\<close>
    and misc_assms:
    \<open>T RGSepAtom\<close>
    \<open>T RGSepEndet\<close>
    \<open>T RGSepSeq\<close>
    \<open>sswa R p \<le> I\<close>
  shows
    \<open>R, G, I, F, T \<turnstile> { p } SecIfThenElse pa ctt cff { q }\<close>
  using misc_assms
  unfolding SecIfThenElse_def
proof (intro rgsat_endet[OF rgsat_seq rgsat_seq order.refl order.refl,
      where I=I and Ia=\<open>sswa R p \<squnion> I\<close> and Ib=\<open>sswa R p \<squnion> I\<close>])
  show \<open>R, G, sswa R p, F, T \<turnstile> { p } Await (\<lblot> pa \<rblot>) { sswa R (sswa R p \<sqinter> \<lblot> pa \<rblot>) }\<close>
    using misc_assms assms(1) tt_guard_frame_cond
    apply (intro rgsat_await; simp)
     apply (simp add: inf_sup_aci(2,3) le_infI2 rel_image_snd_galois rel_liftL_conj_eq; fail)
    apply (metis order.refl inf_sup_ord(1) wlp_weaker_iff_sp_stronger wssa_over_sswa_eq)
    done
  show \<open>R, G, I, F, T \<turnstile> { sswa R (sswa R p \<sqinter> \<lblot> pa \<rblot>) } ctt { q }\<close>
    using body_assms
    by blast
  show \<open>R, G, sswa R p, F, T \<turnstile> { p } Await (\<lblot> -pa \<rblot>) { sswa R (sswa R p \<sqinter> \<lblot> -pa \<rblot>) }\<close>
    using ff_guard_frame_cond misc_assms assms
    apply (intro rgsat_await; simp)
     apply (simp add: inf.assoc inf.left_commute le_infI2 rel_image_snd_galois
        rel_liftL_conj_distrib; fail)
    apply (meson le_infI1 relyrel_trans transp_relcompp wlp_sp_weak_absorb
        wlp_weaker_iff_sp_stronger; fail)
    done
  show \<open>R, G, I, F, T \<turnstile> { sswa R (sswa R p \<sqinter> \<lblot> -pa \<rblot>) } cff { q }\<close>
    using body_assms
    by blast
qed simp+

section \<open> Declassification \<close>

definition Declassify :: \<open>('l \<times> 's \<Rightarrow> 'v) \<Rightarrow> ('l, 's) rgstate comm\<close> where
  \<open>Declassify h \<equiv> Await (\<bbbA>\<^sub>\<ddagger> h)\<close>

lemma declassify_quasireflp_steprel:
  \<open>\<top> \<le> quasireflp_steprel (atom_rel (Declassify h))\<close>
  by (clarsimp simp add: Declassify_def Await_def quasireflp_steprel_def reflp_on_def
      prepost_state_def' sec_agree_exch4_def')

lemma declassify_symp_steprel:
  \<open>\<top> \<le> symp_steprel (atom_rel (Declassify h))\<close>
  by (clarsimp simp add: Declassify_def Await_def symp_steprel_def sec_agree_exch4_def')

lemma declassify_quasirefl_blocking_steprel:
  \<open>quasirefl_blocking_steprel (atom_rel (Declassify h)) = \<bbbA>\<^sub>\<ddagger> h\<close>
  by (clarsimp simp add: Declassify_def Await_def quasirefl_blocking_steprel_def
      sec_agree_exch4_def' exch4_def)


section \<open> Purely Relational \<close>

\<comment> \<open> TODO \<close>

definition purely_relational
  :: \<open>(('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
    \<open>purely_relational ar \<equiv>
      (\<forall>z x' y'. (ar \<circ>\<^sub>2 exch4) (z,z) (x',y') \<longrightarrow> x' = z \<and> y' = z)\<close>

definition purely_relational2
  :: \<open>(('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
    \<open>purely_relational2 ar \<equiv>
      (\<forall>xa ya xa' ya' xb yb xb' yb'.
        (ar \<circ>\<^sub>2 exch4) (xa, ya) (xa', ya') \<longrightarrow>
        (ar \<circ>\<^sub>2 exch4) (xb, yb) (xb', yb') \<longrightarrow>
        (ar \<circ>\<^sub>2 exch4) (xa, yb) (xa', yb') \<and>
        (ar \<circ>\<^sub>2 exch4) (xb, ya) (xb', ya'))\<close>

definition pr3 :: \<open>(('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>pr3 ar \<equiv> ar \<sqinter> (rel_lift (case_prod (=)) \<top> \<circ>\<^sub>2 exch4) \<le> (=)\<close>

lemma \<open>purely_relational ar = pr3 ar\<close>
  unfolding pr3_def purely_relational_def
  by (force simp add: le_fun_def)

lemma
  \<open>(\<forall>x y x' y'. (ar \<circ>\<^sub>2 exch4) (x, y) (x', y') \<longrightarrow> (ar \<circ>\<^sub>2 exch4) (y, x) (y', x')) \<Longrightarrow>
    (\<forall>x y x' y'. (ar \<circ>\<^sub>2 exch4) (x, x) (x', y') \<longrightarrow>
      (ar \<circ>\<^sub>2 exch4) (x, x) (x', x') \<and> (ar \<circ>\<^sub>2 exch4) (x, x) (y', y')) \<Longrightarrow>
    purely_relational2 ar \<Longrightarrow>
    purely_relational ar\<close>
  unfolding purely_relational_def purely_relational2_def
  oops

lemma purely_relational_output:
  \<open>purely_relational (atom_rel (Output h))\<close>
  unfolding Output_def RelAssert_def sec_agree_exch4_def sec_agree_def
  by (simp add: purely_relational_def fun_eq_iff pre_state_def, metis)

lemma await_agree_purely_relational:
  \<open>purely_relational (atom_rel (Await (\<bbbA>\<^sub>\<ddagger> h)))\<close>
  unfolding Await_def purely_relational_def pre_state_def
  apply (clarsimp simp add: fun_eq_iff sec_agree_def)
  apply (rename_tac la sa lb sb)
  sorry

lemma await_purely_relational:
  \<open>purely_relational (atom_rel (Await pp))\<close>
  unfolding Await_def purely_relational_def
  by (clarsimp simp add: fun_eq_iff)

lemma purely_relational_atom_unlifts_to_nop:
  fixes ar :: \<open>('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> ('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool\<close>
  shows
    \<open>purely_relational (atom_rel \<langle> ar \<rangle>) \<Longrightarrow>
      unliftC \<langle> ar \<rangle> = \<langle> rel_liftL (\<lambda>(l,s). pre_state ar ((l,l),(s,s))) \<sqinter> (=) \<rangle>\<close>
  unfolding Await_def purely_relational_def
  by (force simp add: fun_eq_iff pre_state_def)



section \<open> Old things \<close>

lemma helper:
  \<open>A \<and> B \<and> C \<or> B \<and> C \<longleftrightarrow> B \<and> C\<close>
  by blast

lemma
  \<open>unliftC (RelAssert p :: ('l, 's \<times> fail_st) rgstate comm) =
    ( \<langle>\<lambda>(l,(s,fl)) (l',(s',fl')).
        l' = l \<and> s' = s \<and>
        (fl = Failed \<longrightarrow> fl' = Running \<longrightarrow> False) \<and>
        (fl = Running \<longrightarrow> fl' = Failed \<longrightarrow> (\<exists>ly sy. \<not> p ((l, ly), (s, sy))))
      \<rangle>
    , \<langle>\<lambda>(l,(s,fl)) (l',(s',fl')).
        l' = l \<and> s' = s \<and>
          (fl = fl' \<or>
            fl = Running \<and> fl' = Failed \<and> (\<exists>lx sx. \<not> p ((lx, l), (sx, s))
          ))
      \<rangle>
    )\<close>
  by (force simp add: RelAssert_def fun_eq_iff all_fail_st_eq ex_fail_st_eq)

section \<open> Examples \<close>

subsection \<open> SecCSL example \<close>

datatype lock = Locked | Unlocked
datatype 'v s_val = SVal 'v | SLock lock


definition Acquire :: \<open>'x \<Rightarrow> ('l \<times> (('x \<Rightarrow> 'v s_val) \<times> bool)) comm\<close> where
  \<open>Acquire x \<equiv>
    \<langle>\<lambda>(ls, (m, f)) (ls', (m', f')).
      ((\<nexists>lk. m x = SLock lk) \<or> f) \<and> m' = m \<and> f' = True \<or>
      m x = SLock Unlocked \<and> \<not> f \<and> m' = m(x := SLock Locked) \<and> f' = f
      \<comment> \<open> m x = SLock Locked ~> blocked \<close>
    \<rangle>\<close>

lemma guard_Acquire[simp]:
  \<open>atom_guard (Acquire x) s \<longleftrightarrow>
    (\<forall>lk. fst (snd s) x \<noteq> SLock lk) \<or>
      snd (snd s) \<or>
      \<not> snd (snd s) \<and> fst (snd s) x = SLock Unlocked\<close>
  by (simp add: Acquire_def pre_state_def split: prod.splits, blast)


definition Release :: \<open>'x \<Rightarrow> ('l \<times> (('x \<Rightarrow> 'v s_val) \<times> bool)) comm\<close> where
  \<open>Release x \<equiv>
    \<langle>\<lambda>(ls, (m, f)) (ls', (m', f')).
      (m x \<noteq> SLock Locked \<or> f) \<and> m' = m \<and> f' = True \<or>
      m x = SLock Locked \<and> \<not> f \<and> m' = m(x := SLock Unlocked) \<and> f' = f
    \<rangle>\<close>

lemma guard_Release[simp]:
  \<open>atom_guard (Release x) s \<longleftrightarrow> True\<close>
  by (simp add: Release_def pre_state_def split: prod.splits, blast)


definition Load
  :: \<open>'x \<Rightarrow> 'p \<Rightarrow> (('p \<rightharpoonup> 'v discr) \<times> (('x \<Rightarrow> ('v discr) s_val) \<times> bool)) comm\<close>
  where
    \<open>Load x p \<equiv> undefined\<close>

definition Store
  :: \<open>'p \<Rightarrow> 'x \<Rightarrow> (('p \<rightharpoonup> 'v discr) \<times> (('x \<Rightarrow> ('v discr) s_val) \<times> bool)) comm\<close>
  where
    \<open>Store p x \<equiv> undefined\<close>


definition procA :: \<open>string \<Rightarrow> ((nat \<rightharpoonup> 'v discr) \<times> ((string \<Rightarrow> ('v discr) s_val) \<times> bool)) comm\<close> where
  \<open>procA x \<equiv>
    Acquire ''mutex'' ;;
    Load x 0 ;;
    Store 0 x ;;
    Release ''mutex''\<close>

definition
  \<open>prog_mutex_contest \<equiv> procA ''x'' \<parallel> procA ''y''\<close>


definition mdefined :: \<open>'x \<Rightarrow> ('x \<rightharpoonup> 'v) \<Rightarrow> bool\<close> where
  \<open>mdefined x \<equiv> \<lambda>m. m x \<noteq> None\<close>

definition locked :: \<open>'x \<Rightarrow> ('x \<Rightarrow> 'v s_val) \<Rightarrow> bool\<close> where
  \<open>locked x \<equiv> \<lambda>f. f x = SLock Locked\<close>

definition unlocked :: \<open>'x \<Rightarrow> ('x \<Rightarrow> 'v s_val) \<Rightarrow> bool\<close> where
  \<open>unlocked x \<equiv> \<lambda>f. f x = SLock Unlocked\<close>

definition rinv :: \<open>('l::multiunit_sep_alg \<times> 's \<Rightarrow> bool) \<Rightarrow> ('l \<Rightarrow> bool) \<Rightarrow> ('l \<times> 's \<Rightarrow> bool)\<close> where
  \<open>rinv p pl \<equiv> (\<lambda>s. if p s then pl (fst s) else emp (fst s))\<close>

lemma prog_mutex_contest:
  fixes I :: \<open>(nat \<rightharpoonup> 'v discr) \<times> ((string \<Rightarrow> 'v discr s_val) \<times> bool) \<Rightarrow> bool\<close>
  defines
    \<open>I \<equiv> \<S> (\<top> \<times>\<^sub>P Not) \<sqinter> (rinv (\<S> (locked ''mutex'' \<times>\<^sub>P \<top>)) (mdefined 0) \<^emph>\<and> \<top>)\<close>
  shows
    \<open>(=), \<top>, I, \<top>, \<top> \<turnstile> { \<L> emp } prog_mutex_contest { \<L> emp }\<close>
  unfolding prog_mutex_contest_def
  sorry

text \<open> There's no (non-parallelism) non-determinism, thus it's always security deterministic. \<close>
lemma security_determ_prog_mutex_contest:
  \<open>\<top> \<le> sec_determ prog_mutex_contest\<close>
  by (force simp add: prog_mutex_contest_def)

lemma secure_prog_mutex_contest:
  defines
    \<open>I \<equiv> \<S> (\<top> \<times>\<^sub>P Not) \<sqinter> (rinv (\<S> (locked ''mutex'' \<times>\<^sub>P \<top>)) (mdefined 0) \<^emph>\<and> \<top>)\<close>
  shows
    \<open>(=), \<top>, \<lblot> I \<rblot>\<^sub>\<ddagger>, \<top>, \<top> \<turnstile> { \<lblot> \<L> emp \<rblot>\<^sub>\<ddagger> } liftC prog_mutex_contest { \<lblot> \<L> emp \<rblot>\<^sub>\<ddagger> }\<close>
  using assms
  by (intro double_program_lifting[OF prog_mutex_contest]) force+


subsection \<open> Wordle \<close> (* TODO *)

type_synonym varnm = \<open>char list\<close>
type_synonym wordle_ls = \<open>varnm \<rightharpoonup> char list discr \<times> munit\<close>
type_synonym wordle_ss = \<open>varnm \<Rightarrow> char list\<close>

definition wordle_output
  :: \<open>wordle_ls \<times> wordle_ss \<Rightarrow> bool \<times> nat set\<close>
  where
  \<open>wordle_output \<equiv> \<lambda>(ls, ss).
    let word = the_discr (fst (the (ls ''word'')))
      ; guess = ss ''guess''
    in
    (mset word = mset guess,
      {i. i \<le> max (length word) (length guess) \<longrightarrow> word ! i = guess ! i})\<close>

lemma wordle_output_local_reduce:
  \<open>lsa ## lsb \<Longrightarrow>
    lsa ''word'' \<noteq> None \<Longrightarrow>
    wordle_output (lsa + lsb, ss) = wordle_output (lsa, ss)\<close>
  apply (clarsimp simp add: wordle_output_def Let_def disjoint_fun_def)
  apply (subgoal_tac \<open>lsa ''word'' ## lsb ''word''\<close>)
   apply force
  apply metis
  done

lemma wordle_output_agree_frame_local:
  fixes p F :: \<open>(wordle_ls \<times> wordle_ls) \<times> (wordle_ss \<times> wordle_ss) \<Rightarrow> bool\<close>
  assumes \<open>post_state (curry p) \<le> post_state (curry F)\<close>
    and \<open>p \<le> \<lblot>\<lambda>(ls, ss). ls ''word'' \<noteq> None\<rblot> \<circ> exch4\<close>
  shows \<open>frame_local F p (\<bbbA> wordle_output \<circ> exch4)\<close>
  using assms
  apply (simp add: frame_local_def le_fun_def post_state_def)
  apply (rule conjI[rotated], blast)
  apply (clarsimp simp add: sec_agree_def sepconj_conj_apply)
  apply (subst (asm) wordle_output_local_reduce, blast, blast)
  apply (subst (asm) wordle_output_local_reduce, blast, blast)
  apply blast
  done


(* TODO: move *)

(* TODO: write examples: (1) Arthur's nointerference, (2) observing local state *)

lemma sepimp_conj_step_mp:
  \<open>p \<le> p' \<Longrightarrow> (p' \<midarrow>\<^emph>\<^sub>\<and> q) \<^emph>\<and> p \<le> q\<close>
  by (meson order_refl sepimp_conj_mono sepimp_conj_sepconj_conj_shunt)

lemma comp2_exch4_over_rel_times[simp]:
  fixes ra :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
    and rb :: \<open>'b \<Rightarrow> 'b \<Rightarrow> bool\<close>
  shows \<open>((ra \<times>\<^sub>R rb) \<times>\<^sub>R (rc \<times>\<^sub>R rd)) \<circ>\<^sub>2 exch4 = ((ra \<times>\<^sub>R rc) \<times>\<^sub>R (rb \<times>\<^sub>R rd))\<close>
  by (force simp add: comp_rel_def exch4_def rel_times_def)

lemma example_observing_local_state:
  fixes F :: \<open>(('p \<rightharpoonup> 'v::perm_alg) \<times> ('p \<rightharpoonup> 'v)) \<times> ('h \<times> 'h) \<Rightarrow> bool\<close>
  assumes
    \<open>x \<noteq> y\<close>
  shows
    \<open>(=), (=) \<turnstile>\<^bsub>F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4), F\<^esub>
    { (F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4)) }
      liftC (\<langle>\<top>, (\<lambda>hl hl'. hl' = hl(x \<mapsto> v)) \<times>\<^sub>R (=)\<rangle>)
    { (F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4)) }\<close>
  apply (simp add: liftC_def)
  apply (rule rgsat_atom[of _ _
        \<open>F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4)\<close>
        \<open>F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4)\<close>
        ])
        apply force
       apply force
      apply force
     apply force
    apply force
   apply clarsimp
   apply (clarsimp simp add: sp_def sepconj_conj_def sepimp_conj_def split: prod.splits)
  sorry


definition
  \<open>location_independent Pt \<equiv> \<lambda>(p,q).
    \<forall>h h' s s'.
      p (h, s) \<longrightarrow>
      q (h, s) (h', s') \<longrightarrow>
      (\<forall>\<sigma>.
        bij \<sigma> \<longrightarrow>
        (\<forall>\<rho>. \<rho> \<notin> Pt \<longrightarrow> \<sigma> \<rho> = \<rho>) \<longrightarrow>
        p (h \<circ> \<sigma>, s) \<and> q (h \<circ> \<sigma>, s) (h' \<circ> \<sigma>, s'))\<close>

definition
  \<open>value_independent Pt \<equiv> \<lambda>(p,q).
    \<forall>h h' s s'.
      p (h, s) \<longrightarrow>
      q (h, s) (h', s') \<longrightarrow>
      (\<forall>hx hx'.
        (\<forall>\<rho>. \<rho> \<notin> Pt \<longrightarrow> hx \<rho> = hx' \<rho>) \<longrightarrow>
        p (hx, s) \<and> q (hx, s) (hx', s'))\<close>


lemma example_deAmorim_noninterference:
  fixes S :: \<open>('p \<rightharpoonup> 'l::pre_perm_alg) \<times> 's \<Rightarrow> bool\<close>
  assumes
    \<open>R, G, I, F, \<top> \<turnstile> { p } c { q }\<close>
    \<open>\<forall>ra\<in>#all_atoms c. (\<forall>x x'. (I \<squnion> (I \<^emph>\<and> F)) x \<longrightarrow> ra x x' \<longrightarrow> {\<rho>. fst x \<rho> \<noteq> fst x' \<rho>} \<subseteq> V)\<close>
  shows
    \<open>liftR R, liftR G, \<bbbA>\<^sub>\<ddagger> f, \<lblot> F \<rblot>\<^sub>\<ddagger>, \<top> \<turnstile> { \<lblot> p \<rblot>\<^sub>\<ddagger> } liftC c { \<lblot> q \<rblot>\<^sub>\<ddagger> }\<close>
  sorry

lemma opstep_all_atoms_antimono:
  \<open>sc \<midarrow>\<alpha>\<rightarrow> sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    all_atoms c' \<le> all_atoms c\<close>
  apply (induct \<alpha> sc sc' arbitrary: s c s' c' rule: opstep.induct)
        apply force
       apply force
      apply force
     apply clarsimp
     apply (elim disjE conjE; clarsimp; blast)
    apply clarsimp
    apply (elim disjE conjE; clarsimp; blast)
   apply (clarsimp split: if_splits; fail)
  apply (clarsimp split: if_splits; fail)
  done


\<comment> \<open> note the instantiation of X to \<open>(FF \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> \<oo> \<circ> exch4))\<close> \<close>
lemma pred_preserved_then_pred_all_states:
  fixes c :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
  assumes
    \<open>safe n c z r g q S F\<close>
    \<open>z = s\<close>
    \<open>\<forall>s s'. ((=) \<times>\<^sub>R r) s s' \<longrightarrow> S s \<longrightarrow> X s \<longrightarrow> X s'\<close>
    \<open>\<forall>p q. (p, q) \<in> all_atoms c \<longrightarrow>
      (\<forall>hl hs hl' hs'.
        (\<forall>fl.
          hl ## fl \<longrightarrow> F (fl, hs) \<longrightarrow> hl' ## fl \<longrightarrow>
          p (hl + fl, hs) \<longrightarrow> q (hl + fl, hs) (hl' + fl, hs') \<longrightarrow>
          S (hl, hs) \<longrightarrow>
          X (hl, hs) \<longrightarrow> X (hl', hs')))\<close>
    \<open>X s\<close>
  shows
    \<open>safe n c z r g q X F\<close>
  using assms
proof (induct n c z r g q S F arbitrary: s rule: safe.induct)
  case (safe_nil S hl hs c r g q F)
  then show ?case by force
next
  case (safe_suc c q hl hs S r n g F)
  then show ?case
    apply (clarsimp simp add: safe_suc_iff eq_rtimes_R_iff top_rtimes_R_iff)
    apply (drule meta_spec2, drule meta_spec2, drule meta_mp, assumption,
        drule meta_mp, assumption, drule meta_mp, assumption)
    apply clarsimp
    apply (rule_tac x=hl' in exI)
    apply clarsimp
    apply (drule mp[of \<open>All _\<close>])
     apply (meson opstep_all_atoms_antimono subsetD; fail)
    apply clarsimp
    apply (erule opstep_act_cases, force)
    apply (frule vis_step_impl_atom)
    apply clarsimp
    apply (drule spec2, drule mp, rule set_mp[OF head_atoms_subseteq_all_atoms], assumption)
    apply metis
    done
qed


end