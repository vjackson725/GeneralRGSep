theory Security
  imports "../Security"
begin


section \<open> Semantic Security Rules \<close>

text \<open> Proving the exact sec-determ conditions \<close>

lemma secure_endet:
  \<open>secure R F G I q n ca s \<Longrightarrow>
    secure R F G I q n cb s \<Longrightarrow>
    sswa R ((=) s) \<^emph>\<and> F \<le> all_sec_determ (unliftC (ca \<^bold>\<box> cb)) \<circ> exch4 \<Longrightarrow>
    secure R F G I q n (ca \<^bold>\<box> cb) s\<close>
proof (induct n arbitrary: ca cb s)
  case (Suc n)
  obtain ls ss where \<open>s = (ls, ss)\<close>
    by (metis prod.collapse)
  then show ?case
    using Suc.prems
    apply -
    apply (rule secureI, assumption)
      (* subgoal: terminated *)
        apply blast
      (* subgoal: state invariant *)
       apply blast
      (* subgoal: rely *)
      apply (clarsimp simp del: all_sec_determ_eq comp_apply sup_apply)
      apply (frule secure_suc_relyD[where c=ca], force)
      apply (frule secure_suc_relyD[where c=cb], force)
      apply (frule(1) Suc.hyps[where ca=ca and cb=cb])
       apply (simp del: all_sec_determ_eq comp_apply sup_apply)
       apply (rule order.trans[rotated], assumption)
       apply (rule sepconj_conj_monoL)
       apply (clarsimp simp add: sswa_eqpred_eq)
       apply (metis (mono_tags) converse_rtranclp_into_rtranclp sp_apply)
      apply force
      (* subgoal: opstep *)
     apply (simp del: all_sec_determ_eq comp_apply sup_apply)
     apply (case_tac \<alpha>)
      apply (simp del: all_sec_determ_eq comp_apply sup_apply)
      apply (rule_tac x=\<open>fst ls\<close> in exI, rule conjI, fast)
      apply (rule_tac x=\<open>snd ls\<close> in exI, rule conjI, fast)
      apply (simp del: all_sec_determ_eq comp_apply sup_apply)
      apply (rule conjI)
       apply (metis (no_types, opaque_lifting) opstep_tau_preserves_heap split_pairs2)
      apply (simp only: disj.assoc[of _ _ \<open>_ \<or> _\<close>, symmetric])
      apply (erule disjE)
       apply (frule secure_mono_sucD)
       apply (clarsimp simp del: all_sec_determ_eq comp_apply sup_apply)
       apply (meson secure_mono_sucD; fail)
    subgoal sorry
     apply (simp del: all_sec_determ_eq comp_apply sup_apply)
     apply (elim disjE conjE exE)
    sorry
     apply (frule_tac \<alpha>=\<alpha> in secure_suc_stepD[where c=ca], force, force)
      apply (frule_tac \<alpha>=\<alpha> in secure_suc_stepD[where c=cb], force, force)


    sorry
    apply (clarsimp simp del: sup_apply)
    apply (rule conjI)
     apply (metis act.distinct(1) safe_sucE sup2I1 sup2I2)
    apply (simp only: disj.assoc[symmetric, of _ _ \<open>_ \<or> _\<close>])
    apply (erule disjE, erule disjE)
      apply (clarsimp simp add: conj_disj_distribR_middle[symmetric] conj_disj_distribL[symmetric])
      apply (meson inf_sup_ord(4) lessI order_le_less safe_mono sup.cobounded1; fail)
     apply (elim disjE; clarify)
      apply (frule(3) safe_sucD(2))
      apply (metis Suc.hyps opstep_tau_preserves_heap split_pairs2 safe_step_SucD)
     apply (frule(3) safe_sucD(2))
     apply (metis Suc.hyps opstep_tau_preserves_heap split_pairs2 safe_step_SucD)
    apply (elim disjE; clarify)
     apply (frule(3) safe_sucD(2))
     apply clarsimp
     apply (intro exI conjI, assumption, rule refl)
     apply (meson safe_mono order.refl sup_ge1; fail)
    apply (frule(3) safe_sucD(2))
    apply clarsimp
    apply (intro exI conjI, assumption, rule refl)
    apply (meson safe_mono order.refl sup_ge2; fail)
    done
qed blast


section \<open> Security Theory 1 \<close>

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
  \<open>nonfail_rel_lift_ff r \<equiv>
    \<lambda>(l, ((sx,flx), (sy,fly))) (l', ((sx',flx'), (sy',fly'))).
      flx = Running \<and> fly = Running \<and> r (l,(sx,sy)) (l',(sx',sy')) \<and> flx' = Running \<and> fly' = Running \<or>
      (flx = Failed \<or> fly = Failed) \<and> flx' = flx \<and> fly' = fly \<or>
      \<not> r (l,(sx,sy)) (l',(sx',sy')) \<and> flx' = Failed \<and> fly' = Failed\<close>

definition purely_relational2
  :: \<open>(('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
    \<open>purely_relational2 ar \<equiv>
      (\<forall>xa ya xa' ya' xb yb xb' yb'.
        (ar \<circ>\<^sub>2 exch4) (xa, ya) (xa', ya') \<longrightarrow>
        (ar \<circ>\<^sub>2 exch4) (xb, yb) (xb', yb') \<longrightarrow>
        (ar \<circ>\<^sub>2 exch4) (xa, yb) (xa', yb') \<and>
        (ar \<circ>\<^sub>2 exch4) (xb, ya) (xb', ya'))\<close>

definition purely_relational3 :: \<open>(('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>purely_relational3 ar \<equiv> ar \<sqinter> (rel_lift (case_prod (=)) \<top> \<circ>\<^sub>2 exch4) \<le> (=)\<close>


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
  by (force simp add: relassert_rel_def fun_eq_iff all_fail_st_eq ex_fail_st_eq)

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


section \<open> Security theory 2 \<close>

lemma secure_atom':
  assumes
    \<open>p \<^emph>\<and> F \<le> quasireflp_atoms cc\<close>
    \<open>p \<^emph>\<and> F \<le> quasirefl_blocking_doloops_head_atoms cc\<close>
    \<open>p \<^emph>\<and> F \<le> all_sec_determ (unliftC cc) \<circ> exch4\<close>
    \<open>\<forall>f\<le>F. sp ar (wssa R p \<^emph>\<and> f) \<le> sswa R q \<^emph>\<and> any_shared f\<close>
    \<open>wssa R p s\<close>
  shows
    \<open>secure R F
      (rel_image snd (rel_liftL (sswa R p \<^emph>\<and> F) \<sqinter> ar)) \<comment> \<open> G \<close>
      (wssa R p \<squnion> sswa R q) \<comment> \<open> I \<close>
      (sswa R q) \<comment> \<open> q \<close>
      n \<langle>ar\<rangle> s\<close>
proof (induct n arbitrary: s)
  case (Suc n)
  note ih = Suc.hyps[simplified fst_conv snd_conv]
  show ?case
    using Suc.prems
    apply -
    apply (cases s)
    apply (rename_tac sl ss)
    apply (clarsimp simp del: sup_apply inf_apply top_apply rel_lift_apply rel_image_apply)
    apply (rule safeI)
      (* subgoal: termination *)
       apply force
      (* subgoal: state inv *)
      apply force
      (* subgoal: rely *)
     apply (clarsimp simp del: sup_apply inf_apply rel_lift_apply top_apply rel_image_apply)
     apply (simp add: ih wssa_step; fail)
      (* subgoal: local framed opstep *)
    apply (rule conjI)
      (* subsubgoal: guarantee *)
     apply clarsimp
     apply (meson rely_rel_wlp_impl_sp sepconj_conjI; fail)
      (* subsubgoal: safety after opstep *)
    apply (clarsimp simp del: sup_apply inf_apply top_apply rel_lift_apply
        simp add: safe_skip_stable_iff sp_sup)
    apply (frule spec[of _ \<open>(=) _\<close>], frule mp, blast)
    apply (clarsimp simp add: sp_def[of ar] le_fun_def imp_ex_conjL sepconj_conj_def any_shared_def)
    done
qed simp











lemma basic_tau_aact_exclusive:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    TauBasic = snd \<pi>\<alpha> \<Longrightarrow>
    sc \<midarrow>\<pi>\<alpha>'\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    TauBasic = snd \<pi>\<alpha>'\<close>
  apply (frule aopstep_tau_preserves_state, force)
  apply (induct \<pi>\<alpha> sc sc' arbitrary: \<pi>\<alpha>' rule: aopstep.induct)
        apply force
       apply force
      apply force
    (* endet *)
     apply (clarsimp simp add: if_bool_eq_disj)
     apply (rename_tac s' c' \<alpha>')
     apply (case_tac \<open>ca = Skip \<and> cb = Skip\<close>)
      apply force
     apply (clarsimp simp add: vis_tau_aact_incompatible(2))
  subgoal sorry
      (* par *)
    apply clarsimp
  subgoal sorry
      (* do-loop *)
  subgoal sorry
      (* atom *)
  apply force
  oops

lemma basic_tau_reducts_from_basic_tau_exec:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    sc \<midarrow>\<rho>'\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    list_all (basic_tau_aact \<circ> snd) \<rho>' \<Longrightarrow>
    length \<rho> \<le> length \<rho>' \<Longrightarrow>
    fst sc' = fst sc \<and> list_all (basic_tau_aact \<circ> snd) \<rho>\<close>
  apply (induct arbitrary: \<rho>' rule: aopsteps.induct)
   apply clarsimp
  oops


subsection \<open> aaa \<close>

definition
  \<open>sec_core p \<equiv>
    (\<lambda>(x,y). (p \<circ> exch4) (x,y) \<and> (p \<circ> exch4) (y, x) \<and> (p \<circ> exch4) (x, x) \<and> (p \<circ> exch4) (y, y)) \<circ> exch4\<close>

definition
  \<open>sec_ext p \<equiv>
    (\<lambda>(x,y). (p \<circ> exch4) (x,y) \<or> (p \<circ> exch4) (y, x) \<or>
      (x = y \<and> (\<exists>z. (p \<circ> exch4) (x, z) \<and> (p \<circ> exch4) (z, y)))
    ) \<circ> exch4\<close>

lemma
  fixes p :: \<open>('l, 's) rgstate \<Rightarrow> bool\<close>
    and r :: \<open>('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool\<close>
  shows
  \<open>sec_core p \<le> quasireflp_steprel r \<Longrightarrow>
    sec_core p \<le> symp_steprel r \<Longrightarrow>
    sp r (sec_core p) \<le> sec_core (sp r p)\<close>
  apply (clarsimp simp add: sec_core_def exch4_def le_fun_def quasireflp_steprel_def
      symp_steprel_def sp_def)
  apply metis
  done

lemma
  fixes p :: \<open>('l, 's) rgstate \<Rightarrow> bool\<close>
    and r :: \<open>('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool\<close>
  shows
  \<open>sec_core p \<le> quasireflp_steprel r \<Longrightarrow>
    sec_core p \<le> symp_steprel r \<Longrightarrow>
    q = sp r (sec_core p) \<Longrightarrow>
    q' = sec_core (sp r p) \<Longrightarrow>
    q' \<le> q\<close>
(*  nitpick[card 'l=2, card 's=1] *)
  oops
(*
    p = (\<lambda>x. _)
        (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) := False, ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) := False, ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) := True,
           ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True)
    q = (\<lambda>x. _)
        (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) := False, ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) := False, ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) := False,
           ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True)
    q' = (\<lambda>x. _)
         (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) := True, ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True, ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) := True,
            ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True)
    r = (\<lambda>x. _)
        (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) :=
           (\<lambda>x. _)
           (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) := False, ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True, ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) := False,
              ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True),
           ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) :=
             (\<lambda>x. _)
             (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) := True, ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True, ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) := True,
                ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True),
           ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) :=
             (\<lambda>x. _)
             (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) := True, ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True, ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) := True,
                ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) := False),
           ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) :=
             (\<lambda>x. _)
             (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) := False, ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) := False, ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) := False,
                ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True))
*)


section \<open> Scratch Space \<close>

definition
  \<open>symp_atoms \<equiv> all_atom_comm
    (\<lambda>ar. \<forall>lx sx ly sy lx' sx' ly' sy'.
      ar ((lx,ly),(sx,sy)) ((lx',ly'),(sx',sy')) \<longrightarrow>
      ar ((ly,lx),(sy,sx)) ((ly',lx'),(sy',sx')))\<close>

lemma symp_atomsD:
  \<open>symp_atoms cc \<Longrightarrow> ar \<in># all_atoms cc \<Longrightarrow>
    ar ((lx,ly),(sx,sy)) ((lx',ly'),(sx',sy')) \<Longrightarrow>
    ar ((ly,lx),(sy,sx)) ((ly',lx'),(sy',sx'))\<close>
  by (simp add: all_atom_comm_def symp_atoms_def, blast)

lemmas symp_atoms_simps[simp] =
  all_atom_comm_simps[of \<open>\<lambda>ar. \<forall>lx sx ly sy lx' sx' ly' sy'.
      ar ((lx,ly),(sx,sy)) ((lx',ly'),(sx',sy')) \<longrightarrow>
      ar ((ly,lx),(sy,sx)) ((ly',lx'),(sy',sx'))\<close>,
    simplified symp_atoms_def[symmetric]]

text \<open> Old definition of security from Jul-Aug that doesn't quite work \<close>
inductive secure_old
  :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow>
      ('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow>
      (('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow>
      ('l::pre_perm_alg \<times> 's) comm \<times> ('l::pre_perm_alg \<times> 's) comm \<Rightarrow>
      ('l, 's) secstate \<Rightarrow>
      bool\<close>
  for R F G I q
  where secure_oldI[intro]:
  \<open>zz = ((slx::'l, ssx::'s), (sly::'l, ssy::'s)) \<Longrightarrow>
    \<comment> \<open> Post-condition
         Note that \<^emph>\<open>both\<close> programs need to be terminated. \<close>
    cx = Skip \<longrightarrow> cy = Skip \<longrightarrow> q ((slx, sly), (ssx, ssy)) \<Longrightarrow>
    \<comment> \<open> State Invariant \<close>
    I ((slx, sly), (ssx, ssy)) \<Longrightarrow>
    \<comment> \<open> Rely Steps \<close>
    (\<And>n' ssx' ssy'.
      n = Suc n' \<Longrightarrow>
      R (ssx, ssy) (ssx', ssy') \<Longrightarrow>
      secure_old R F G I q n' (cx, cy) ((slx, ssx'), (sly, ssy'))) \<Longrightarrow>
    \<comment> \<open> Opsteps \<close>
    (\<And>n' \<pi>\<alpha> sx' sy' cx' cy'.
      n = Suc n' \<Longrightarrow>
      ((slx, ssx), cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', cx') \<Longrightarrow>
      ((sly, ssy), cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', cy') \<Longrightarrow>
      (vis_aact (snd \<pi>\<alpha>) \<longrightarrow> G (ssx, ssy) (snd sx', snd sy')) \<and>
      (tau_aact (snd \<pi>\<alpha>) \<longrightarrow> fst sx' = slx \<and> fst sy' = sly) \<and>
      secure_old R F G I q n' (cx', cy') (sx', sy') ) \<Longrightarrow>
    \<comment> \<open> Framed opsteps \<close>
    (\<And>n' fx fy \<pi>\<alpha> slfx' slfy' ssx' ssy' cx' cy'.
      n = Suc n' \<Longrightarrow>
      F ((fx, fy), (ssx, ssy)) \<Longrightarrow>
      slx ## fx \<Longrightarrow>
      sly ## fy \<Longrightarrow>
      ((slx + fx, ssx), cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((slfx', ssx'), cx') \<Longrightarrow>
      ((sly + fy, ssy), cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((slfy', ssy'), cy') \<Longrightarrow>
      (vis_aact (snd \<pi>\<alpha>) \<longrightarrow> G (ssx, ssy) (ssx', ssy')) \<and>
      (\<exists>slx'.
        slx' ## fx \<and>
        slfx' = slx' + fx \<and>
        (\<exists>sly'.
          sly' ## fy \<and>
          slfy' = sly' + fy \<and>
          (tau_aact (snd \<pi>\<alpha>) \<longrightarrow> slx' = slx \<and> sly' = sly) \<and>
          secure_old R F G I q n' (cx', cy') ((slx', ssx'), (sly', ssy')) ))) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    secure_old R F G I q n (cx, cy) zz\<close>


subsection \<open> (Old) Safety Implies Security \<close>

theorem safety_implies_security_old:
  fixes n :: nat
    and c :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
    and ss :: \<open>('l, 's) rgstate\<close>
    and F I q :: \<open>('l, 's) rgstate \<Rightarrow> bool\<close>
    and R G :: \<open>'s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool\<close>
  assumes
    \<open>safe R F G I q n cc ss\<close>
    \<open>cc = liftC c\<close>
    \<open>I \<squnion> I \<^emph>\<and> F \<le> all_sec_determ c \<circ> exch4\<close>
  shows
    \<open>secure_old R F G I q n (c, c) (exch4 ss)\<close>
  using assms
proof (induct arbitrary: c rule: safe.induct)
  case (safeI c' s n)
  obtain lsx lsy ssx ssy where
    \<open>s = ((lsx, lsy), (ssx, ssy))\<close>
    by (metis surjective_pairing)
  then show ?case
    using safeI.prems safeI.hyps(1-2)
    apply (clarsimp simp del: sup_apply comp_apply)
    apply (rule secure_oldI)
      (* subgoals: destructuring *)
         apply (simp add: exch4_def; fail)
      (* term *)
        apply (simp add: exch4_def; fail)
      (* subgoal: invariant *)
       apply force
      (* subgoal: rely *)
      apply (frule safeI.hyps(4), force, force, force)
      apply (simp add: exch4_def; fail)
      (* subgoal: double-step *)
     apply clarsimp
     apply (frule(1) same_initcomm_and_aact_then_same_fincomm[
          where sx=\<open>(lsx, ssx)\<close> and sy=\<open>(lsy, ssy)\<close>])
      apply (simp add: le_fun_def exch4_def)
      apply (metis all_sec_determ_implies_head_sec_determ)
     apply (frule full_sync_double_aopstep_to_aopstep[
          where sx=\<open>(lsx, ssx)\<close> and sy=\<open>(lsy, ssy)\<close>], blast)
      apply (simp add: le_fun_def exch4_def)
      apply (metis all_sec_determ_implies_head_sec_determ)
     apply (simp del: comp_apply add: exch4_two_apply)
     apply (frule safeI(5)[OF _ aopstep_then_opstep], blast)
     apply (frule aopstep_preserves_all_sec_determ)
     apply (intro conjI)
       apply force
      apply force
     apply (clarsimp simp del: sup_apply comp_apply del: disjCI)
     apply (meson leq_exch4_shunt order_trans)
        (* subgoal: framed double-step *)
    apply (subgoal_tac \<open>(I \<^emph>\<and> F) ((lsx + fx, lsy + fy), (ssx, ssy))\<close>)
     prefer 2
     apply (rule sepconj_conjI, assumption, assumption, force, force)
    apply (frule_tac sx=\<open>(lsx + fx, ssx)\<close> and sy=\<open>(lsy + fy, ssy)\<close> in
        same_initcomm_and_aact_then_same_fincomm, assumption)
     apply (simp add: le_fun_def exch4_def)
     apply (metis all_sec_determ_implies_head_sec_determ)
    apply (frule_tac sx=\<open>(lsx + fx, ssx)\<close> and sy=\<open>(lsy + fy, ssy)\<close> in
        full_sync_double_aopstep_to_aopstep)
      apply force
     apply (simp add: le_fun_def exch4_def)
     apply (metis all_sec_determ_implies_head_sec_determ)
    apply (clarsimp simp del: comp_apply)
    apply (frule_tac fs=\<open>(fx, fy)\<close> in safeI(6)[OF _ aopstep_then_opstep])
       apply force
      apply force
     apply force
    apply (frule aopstep_preserves_all_sec_determ)
    apply (clarsimp simp del: sup_apply comp_apply)
    apply (intro exI conjI, fast, fast, fast, fast, fast)
    apply (meson order.trans leq_exch4_shunt; fail)
    done
qed


end
