theory Security2
  imports "../sec/Security"
begin


lemma
  \<open>induced_staterel Skip l\<alpha> = \<bottom>\<close>
  \<open>induced_staterel (ca ;; cb) l\<alpha> =
    (if l\<alpha> = (LHere, ATau) \<and> ca = Skip then (=) else induced_staterel ca l\<alpha>)\<close>
  \<open>induced_staterel (ca \<^bold>\<sqinter> cb) l\<alpha> =
    (if l\<alpha> = (LIndetL, ATau) \<or> l\<alpha> = (LIndetR, ATau) then (=) else \<bottom>)\<close>
  \<open>induced_staterel (ca \<^bold>\<box> cb) l\<alpha> =
    (if l\<alpha> = (LEndetL LHere, ATau) \<and> ca = Skip \<or> l\<alpha> = (LEndetR LHere, ATau) \<and> cb = Skip then
        (=)x

      else if \<exists>l. fst l\<alpha> = LEndetL l then
        induced_staterel ca (l, snd l\<alpha>)
      else if \<exists>l. fst l\<alpha> = LEndetR l then
       induced_staterel cb (l, snd l\<alpha>)
      else \<bottom>)\<close>
     apply (force simp add: induced_staterel_def fun_eq_iff)
    apply (force simp add: induced_staterel_def fun_eq_iff)
   apply (force simp add: induced_staterel_def fun_eq_iff)
  apply (clarsimp simp add: induced_staterel_def fun_eq_iff)
  oops



section \<open> Nonrelational and blocking-merge step relations \<close>

lemma sec_agree_exch4_apply[simp]:
  \<open>\<bbbA>\<^sub>\<ddagger> f ((ax,ay), (bx,by)) = \<bbbA> f ((ax,bx), (ay,by))\<close>
  by (simp add: sec_agree_exch4_def)

lemma sec_agree_exch4_on_refl[simp]:
  \<open>\<bbbA>\<^sub>\<ddagger> f ((x,x), (y,y))\<close>
  by (simp add: sec_agree_exch4_def2)

lemma sec_agree_exch4_on_exch4[simp]:
  \<open>\<bbbA>\<^sub>\<ddagger> f (exch4 s) = \<bbbA> f s\<close>
  by (simp add: sec_agree_exch4_def)

lemma sec_agree_on_refl[simp]:
  \<open>\<bbbA> f (x, x)\<close>
  by (simp add: sec_agree_def)


section \<open> aopstep lemmas \<close>


lemma aopstep_preserves_other_steps:
  assumes
    \<open>(s, c) \<midarrow>(lx, ATau)\<rightarrow>\<^sub>a scx'\<close>
    \<open>(s, c) \<midarrow>l\<alpha>y\<rightarrow>\<^sub>a scy'\<close>
  shows
    \<open>\<exists>cx' l\<alpha>y'. scx' \<midarrow>l\<alpha>y'\<rightarrow>\<^sub>a (fst scy', cx')\<close>
  using assms
  apply (induct c arbitrary: scx' scy')
        apply clarsimp
       apply clarsimp
       apply (elim disjE; clarsimp)
  oops


lemma btau_astep_preserves_nextstep:
  assumes
    \<open>sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc'\<close>
    \<open>snd l\<alpha> = ATau\<close>
    \<open>sc \<midarrow>l\<alpha>x\<rightarrow>\<^sub>a scx\<close>
    \<open>l\<alpha>x \<noteq> l\<alpha>\<close>
  shows
    \<open>\<exists>cx'. sc' \<midarrow>l\<alpha>x\<rightarrow>\<^sub>a (fst scx, cx')\<close>
proof -
  have H1: \<open>fst sc = fst sc'\<close>
    using assms(1-2)
    by (simp add: aopstep_tau_preserves_state)
  
  show ?thesis
    using assms H1
  proof (induct _ sc sc' arbitrary: l\<alpha>x scx rule: aopstep_induct)
    case (Seq l\<alpha> s ca cb sc')
    then show ?case
      apply clarsimp
      apply (metis aopstep.simps(1) aopstep_then_aopstep_right_seqD fst_conv
          prod.exhaust)
      done
  next
    case (Endet l\<alpha> s ca cb sc')
    show ?case
      using Endet.prems(1-4)
      apply (cases scx, rename_tac sx cx)
      apply clarsimp
      apply (subgoal_tac \<open>fst l\<alpha> = LHere \<or> (\<exists>l'. fst l\<alpha> = LEndetL l') \<or> (\<exists>l'. fst l\<alpha> = LEndetR l')\<close>)
       prefer 2
       apply (metis fst_conv)
      apply (subgoal_tac \<open>fst l\<alpha>x = LHere \<or> (\<exists>l'. fst l\<alpha>x = LEndetL l') \<or> (\<exists>l'. fst l\<alpha>x = LEndetR l')\<close>)
       prefer 2
       apply (metis fst_conv)
      apply (elim disjE[of \<open>fst _ = _\<close>] disjE[of \<open>\<exists>l'. fst _ = _ l'\<close>])
              apply (clarsimp simp add: split_pairs2 prod_eq_iff; fail)
             apply (clarsimp simp add: split_pairs2 prod_eq_iff split: aact.splits)
              apply (elim disjE; clarsimp)
      sorry
        apply fastforce
       apply fastforce
      apply (elim disjE[of \<open>l\<alpha>x = _ \<and> _\<close>])
        apply (cut_tac Endet.prems(5))
        apply clarsimp
        apply (metis aopstep.simps(4) surjective_pairing)
       apply (cut_tac Endet.prems(5))
       apply clarsimp
       apply (metis aopstep.simps(4) surjective_pairing)
      apply (elim disjE exE conjE)
         apply (cut_tac Endet.prems(5))
         apply (frule(3) Endet.hyps(1))
          apply force
         apply (simp split: act.splits; metis aopstep_then_aopstep_right_endetD split_pairs)
        apply (cut_tac Endet.prems(5))
        apply (simp split: act.splits; metis aopstep_then_aopstep_left_endetD split_pairs)
        apply (cut_tac Endet.prems(5))
       apply (simp split: act.splits; metis aopstep_then_aopstep_right_endetD split_pairs)
      apply (cut_tac Endet.prems(5))
      apply (frule(3) Endet.hyps(2))
       apply force
      apply (simp split: act.splits; metis aopstep_then_aopstep_left_endetD split_pairs)
      done
  next
    case (Par l\<alpha> s ca cb sc')
    then show ?case
      apply (cases l\<alpha>, cases l\<alpha>x, rename_tac l \<alpha> lx \<alpha>x)
      apply clarsimp
      apply (case_tac \<open>l = PHere\<close>)
       apply simp
       apply (metis Par.prems(4) aopstep.simps(1))
      apply (case_tac \<open>lx = PHere\<close>)
       apply (simp; fail)
      apply (case_tac \<open>
        (\<exists>l'. l = PL l') \<and> (\<exists>l'. lx = PL l') \<or>
        (\<exists>l'. l = PR l') \<and> (\<exists>l'. lx = PR l') \<or>
        (\<exists>l'. l = PL l') \<and> (\<exists>l'. lx = PR l') \<or>
        (\<exists>l'. l = PR l') \<and> (\<exists>l'. lx = PL l')\<close>)
       apply (elim conjE disjE[of \<open>Ex _ \<and> Ex _\<close>]; clarsimp; blast)
        (* other cases *)
      apply clarsimp
      apply metis
      done
  next
    case (DoLoop l\<alpha> s c sc')
    show ?case
      using DoLoop.prems
      apply (clarsimp simp add: pretty_no_aopstep_def)
      apply (metis DoLoop.hyps(1) aopstep_then_aopstep_right_seqD split_pairs2)
      done
  qed fastforce+
qed

lemmas btau_astep_preserves_nextstep2 =
  btau_astep_preserves_nextstep[of \<open>(l, \<alpha>)\<close> for l \<alpha>, simplified]



(*
fun comm_all2
  :: \<open>(('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('u \<Rightarrow> 'u \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> ('s comm \<Rightarrow> 'u comm \<Rightarrow> bool)\<close>
  where
  \<open>comm_all2 p Skip Skip = True\<close>
| \<open>comm_all2 p (cxa ;; cxb) (cya ;; cyb) = comm_all2 p cxa cya \<sqinter> comm_all2 p cxa cya\<close>
| \<open>comm_all2 p (cxa \<parallel> cxb) (cya \<parallel> cyb) = comm_all2 p cxa cya \<sqinter> comm_all2 p cxa cya\<close>
| \<open>comm_all2 p (cxa \<^bold>\<sqinter> cxb) (cya \<^bold>\<sqinter> cyb) = comm_all2 p cxa cya \<sqinter> comm_all2 p cxa cya\<close>
| \<open>comm_all2 p (cxa \<^bold>\<box> cxb) (cya \<^bold>\<box> cyb) = comm_all2 p cxa cya \<sqinter> comm_all2 p cxa cya\<close>
| \<open>comm_all2 p (Atomic a) (Atomic b) = p a b\<close>
| \<open>comm_all2 p (DO cx OD) (DO cy OD) =comm_all2 p cx cy\<close>
| \<open>comm_all2 p _ _ = False\<close>

definition \<open>map_state f \<equiv> map_atom (\<lambda>a. a \<circ>\<^sub>2 f)\<close>

lemmas map_state_eq[simp] =
  map_atom.simps[where f=\<open>(\<lambda>a. a \<circ>\<^sub>2 f)\<close> for f, simplified map_state_def[symmetric]]

lemmas map_state_rev_iff =
  map_atom_rev_iff[where f=\<open>(\<lambda>a. a \<circ>\<^sub>2 f)\<close> for f, simplified map_state_def[symmetric]]

lemmas map_state_rev_iff2 =
  map_atom_rev_iff2[where f=\<open>(\<lambda>a. a \<circ>\<^sub>2 f)\<close> for f, simplified map_state_def[symmetric]]


lemma no_opstep_then_no_opstep_map_state:
  fixes f :: \<open>'y \<Rightarrow> 'x\<close>
  shows
  \<open>(f x, c) \<midarrow>/\<rightarrow> \<Longrightarrow> (x, map_state f c) \<midarrow>/\<rightarrow>\<close>
  unfolding pretty_no_opstep_def
  apply (induct c)
        apply fastforce
       apply (fastforce simp add: map_state_rev_iff)
      apply (fastforce simp add: map_state_rev_iff)
     apply fastforce
    apply (clarsimp simp add: map_state_rev_iff all_conj_distrib, metis)
   apply fastforce
  apply (clarsimp simp add: all_conj_distrib pretty_no_opstep_def)
  done


lemma no_opstep_map_state_then_no_opstep:
  fixes f :: \<open>'y \<Rightarrow> 'x\<close>
  shows
  \<open>(x, map_state f c) \<midarrow>/\<rightarrow> \<Longrightarrow>
    all_atoms (\<lambda>a. \<forall>y'. a (f x) y' \<longrightarrow> (\<exists>x'. y' = f x')) c \<Longrightarrow>
    (f x, c) \<midarrow>/\<rightarrow>\<close>
  unfolding pretty_no_opstep_def
  apply (induct c)
        apply fastforce
       apply fastforce
      apply fastforce
     apply fastforce
    apply (clarsimp del: disjCI simp add: all_conj_distrib map_state_rev_iff)
    apply (metis (lifting))
   apply force
   apply (force simp add: all_conj_distrib pretty_no_opstep_def)
  done

lemma opstep_preserves_map_state:
  fixes f :: \<open>'y \<Rightarrow> 'x\<close>
  shows
  \<open>(x, map_state f c) \<midarrow>\<alpha>\<rightarrow> (x', fc') \<Longrightarrow>
    all_atoms (\<lambda>a. \<forall>y'. a (f x) y' \<longrightarrow> (\<exists>x'. y' = f x')) c \<Longrightarrow>
    (\<exists>c'. fc' = map_state f c' \<and> (f x, c) \<midarrow>\<alpha>\<rightarrow> (f x', c'))\<close>
  apply (simp add: map_state_def)
  apply (frule opstep_preserves_map_atom)
  apply (clarsimp simp add: map_state_def[symmetric])
  apply (induct c arbitrary: fc')
    (* Skip *)
        apply force
    (* Seq *)
       apply (clarsimp simp add: map_state_rev_iff)
       apply (elim disjE)
        apply force
       apply (clarsimp simp add: map_state_rev_iff2, metis)
    (* Par *)
      apply (clarsimp simp add: map_state_rev_iff)
      apply (elim disjE)
        apply force
       apply (clarsimp simp add: map_state_rev_iff2, metis)
      apply (clarsimp simp add: map_state_rev_iff2, metis)
    (* Indet *)
     apply fastforce
    (* Endet *)
    apply (clarsimp simp add: map_state_rev_iff)
    apply (elim disjE)
         apply blast
        apply blast
       apply (clarsimp simp add: map_state_rev_iff2, metis)
      apply (clarsimp simp add: map_state_rev_iff2, metis)
     apply metis
    apply metis
    (* Atom *)
   apply force
    (* Iter *)
  apply (clarsimp simp add: map_state_rev_iff)
  apply (elim disjE)
   apply (clarsimp simp add: map_state_rev_iff2)
   apply (force dest: no_opstep_map_state_then_no_opstep[rotated])
  apply force
  done
*)




section \<open> \<close>

definition
  \<open>control_flow_determ c \<equiv> \<lambda>(sx, sy).
    \<forall>\<pi>\<alpha> sx' cx' sy' cy'.
      ((\<Delta> sx), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((\<Delta> sx'), cx') \<longrightarrow>
      ((\<Delta> sy), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((\<Delta> sy'), cy') \<longrightarrow>
      cy' = cx'\<close>

lemma any_head_guard_unliftC_impl:
  \<open>any_head_guard (unliftC c) \<le> any_head_guard c \<circ> \<ddagger> \<circ> \<Delta>\<close>
  by (induct c) (force simp add: pre_state_def fun_eq_iff)+


fun branch_determ2 :: \<open>('s \<times> 's) comm \<Rightarrow> 's \<times> 's \<Rightarrow> bool\<close> where
  \<open>branch_determ2 (ca \<^bold>\<box> cb) =
    undefined ''endet'' ca cb \<sqinter>
      \<lblot> stable_comm ca \<circ> \<Delta> \<rblot> \<sqinter>
      \<lblot> stable_comm cb \<circ> \<Delta> \<rblot> \<sqinter>
      - \<lblot> \<lambda>s. \<not> (\<Delta> s, ca) \<midarrow>/\<rightarrow>\<^sub>a \<bar> \<lambda>s. \<not> (\<Delta> s, cb) \<midarrow>/\<rightarrow>\<^sub>a \<rblot> \<sqinter>
      - \<lblot> \<lambda>s. \<not> (\<Delta> s, cb) \<midarrow>/\<rightarrow>\<^sub>a \<bar> \<lambda>s. \<not> (\<Delta> s, ca) \<midarrow>/\<rightarrow>\<^sub>a \<rblot>\<close>
| \<open>branch_determ2 (DO c OD) = \<bbbA> (\<lambda>s. (\<Delta> s, c) \<midarrow>/\<rightarrow>\<^sub>a)\<close>
| \<open>branch_determ2 (ca \<^bold>\<sqinter> cb) = (\<lambda>_. False)\<close>
| \<open>branch_determ2 c = (\<lambda>_. True)\<close>

lemma all_head_branch_determ_implies_control_flow_determ:
  \<open>all_head_subcomms branch_determ2 c \<le> control_flow_determ c\<close>
proof (induct c)
  case (Endet c1 c2)
  then show ?case
    apply (clarsimp simp add: control_flow_determ_def le_fun_def)
    apply (intro conjI)
       apply (metis aopstep_then_opstep snd_conv stable_comm_def)
      apply (metis aopstep_then_opstep snd_conv stable_comm_def)
     apply (metis aopstep_no_aopstep_contra aopstep_then_opstep snd_conv stable_comm_def)
    apply (metis aopstep_no_aopstep_contra aopstep_then_opstep snd_conv stable_comm_def)
    done
next
  case (Iter c)
  then show ?case
    by (force simp add: control_flow_determ_def sec_agree_def
        dest: aopstep_no_aopstep_contra)
qed (force simp add: control_flow_determ_def)+


lemma
  \<open>same_state_noninfoflow r \<Longrightarrow>
    noninfoflow r \<top> \<le> quasirefl_blocking_steprel r\<close>
  oops


subsection \<open> Basic Commands \<close>

paragraph \<open> Lifted Relation \<close>

\<comment> \<open> rellift is always noninfoflow \<close>
lemma noninfoflow_lift_rel_eq[simp]:
  \<open>noninfoflow \<lblot> r \<rblot>\<^sub>R q = \<top>\<close>
  by (force simp add: noninfoflow_def predrel_def pre_state_def)


paragraph \<open> Output \<close>

lemma noninfoflow_output_eq:
  \<open>noninfoflow\<^sub>\<ddagger> (output_rel f) \<top> = running2_pred (\<bbbA>\<^sub>\<ddagger> f) \<squnion> doublefl_pred (- \<lblot> (=) Running \<rblot>) \<top>\<close>
    by (clarsimp simp add: noninfoflow_exch4_eq output_rel_eq
        fun_eq_iff all_fail_st_eq all_conj_distrib conj_disj_distribR)
      blast

lemma nondeclassifying_output_eq:
  \<open>nondeclassifying\<^sub>\<ddagger> (output_rel f) = \<top>\<close>
  by (clarsimp simp add: nondeclassifying_exch4_eq output_rel_eq running2_pred_def fun_eq_iff
      ex_disj_distrib)


paragraph \<open> Await \<close>

lemma purely_relational_await:
  \<open>purely_relational (await_rel p)\<close>
  by (simp add: purely_relational_def await_rel_def le_fun_def)


paragraph \<open> Declassify \<close>

\<comment> \<open> declassify is noninfoflow exactly when the declassified information is known. \<close>
lemma
  \<open>noninfoflow\<^sub>\<ddagger> (declassify_rel f) \<top> = \<bbbA>\<^sub>\<ddagger> f\<close>
  by (force simp add: noninfoflow_exch4_eq declassify_rel_def2)

\<comment> \<open> declassify is blockingmerge exactly when the declassified information is known. \<close>
lemma
  \<open>nondeclassifying\<^sub>\<ddagger> (declassify_rel f) = \<bbbA>\<^sub>\<ddagger> f\<close>
  by (clarsimp simp add: nondeclassifying_exch4_eq  declassify_rel_def2 sec_agree_exch4_def)




section \<open> Misc \<close>

definition block_very_secure_alt_def:
  \<open>block_very_secure r = (\<lambda>(sx, sy).
    \<not> Ex (r (sx,sy)) \<longrightarrow> ((\<nexists>sx'. r (\<Delta> sx) (\<Delta> sx')) = (\<nexists>sy'. r (\<Delta> sy) (\<Delta> sy'))))\<close>
  by (force simp add: block_secure_def)

lemma
  \<open>\<top> \<le> quasireflp_steprel a \<Longrightarrow>
    nondeclassifying a =
      (\<lambda>(sx, sy).
        (\<exists>sx'. a (\<Delta> sx) (\<Delta> sx')) \<and> (\<exists>sy'. a (\<Delta> sy) (\<Delta> sy')) \<longrightarrow>
        Ex (a (sx, sy)) )\<close>
  apply (simp add: nondeclassifying_def quasireflp_steprel_def)
  apply blast
  done

lemma
  \<open>same_state_noninfoflow a \<Longrightarrow>
    quasirefl_blocking_steprel a =
      (\<lambda>(sx, sy). (\<exists>sx'. a (\<Delta> sx) (\<Delta> sx')) \<or> (\<exists>sy'. a (\<Delta> sy) (\<Delta> sy')) \<longrightarrow> Ex (a (sx, sy)))\<close>
  apply (simp add: quasirefl_blocking_steprel_def fun_eq_iff same_state_noninfoflow_def
      noninfoflow_def le_fun_def)
  apply blast
  done

lemma
  \<open>same_state_noninfoflow a \<Longrightarrow>
    \<top> \<le> quasireflp_steprel a \<Longrightarrow>
    ND = Collect (nondeclassifying a) \<Longrightarrow>
    QB = Collect (quasirefl_blocking_steprel a) \<Longrightarrow>
    ND \<le> QB\<close>
  apply (simp add: quasirefl_blocking_steprel_def fun_eq_iff same_state_noninfoflow_def
      noninfoflow_def nondeclassifying_def le_fun_def)
  nitpick[card 'a=2, card 'b=1]
  done



lemma noninfoflow_rel_conj_merge_eq:
  \<open>\<top> \<le> sym_prestate a \<Longrightarrow>
    \<top> \<le> sym_prestate b \<Longrightarrow>
    same_state_noninfoflow a \<Longrightarrow>
    same_state_noninfoflow b \<Longrightarrow>
    ab = a \<sqinter> b \<Longrightarrow>
    Na = Collect (noninfoflow a \<top>) \<Longrightarrow>
    Nb = Collect (noninfoflow b \<top>) \<Longrightarrow>
    Nab = Collect (noninfoflow (a \<sqinter> b) \<top>) \<Longrightarrow>
    \<top> \<le> nondeclassifying a \<Longrightarrow>
    \<top> \<le> nondeclassifying b \<Longrightarrow>
    b \<le> \<bottom> \<Longrightarrow>
    noninfoflow a \<top> \<sqinter> noninfoflow b \<top> \<ge> noninfoflow (a \<sqinter> b) \<top>\<close>
  apply (clarsimp simp add: noninfoflow_def le_fun_def)
  oops

lemma noninfoflow_rel_conj_merge:
  fixes a b :: \<open>'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool\<close>
  shows
  \<open>ab = a \<sqinter> b \<Longrightarrow>
    pre_state a = pre_state b \<Longrightarrow>
    same_state_noninfoflow a \<Longrightarrow>
    same_state_noninfoflow b \<Longrightarrow>
    \<top> \<le> sym_prestate a \<Longrightarrow>
    \<top> \<le> sym_prestate b \<Longrightarrow>
    \<top> \<le> noninfoflow a \<top> \<Longrightarrow>
    \<top> \<le> nondeclassifying b \<Longrightarrow>
    Nb = Collect (noninfoflow b (\<lblot> diag_states (post_state b) \<rblot>)) \<Longrightarrow>
    Nab = Collect (noninfoflow (a \<sqinter> b) \<top>) \<Longrightarrow>
    Nb \<ge> Nab\<close>
  apply (simp add: noninfoflow_def)
  nitpick
  oops

lemma nondeclassifying_rel_conj_eq:
  \<open>diag_steps b \<le> diag_steps a \<Longrightarrow>
    same_state_noninfoflow a \<Longrightarrow>
    same_state_noninfoflow b \<Longrightarrow>
    nondeclassifying b \<le> quasireflp_steprel b \<Longrightarrow>
    (noninfoflow a \<top> \<sqinter> nondeclassifying b) \<le>
      nondeclassifying (a \<sqinter> b)\<close>
  apply clarsimp
  oops


lemma nondeclassifying_rel_conj_eq:
  \<open>diag_steps b \<le> diag_steps a \<Longrightarrow>
    same_state_noninfoflow a \<Longrightarrow>
    same_state_noninfoflow b \<Longrightarrow>
    nondeclassifying b \<le> quasireflp_steprel b \<Longrightarrow>
    (noninfoflow a \<top> \<sqinter> nondeclassifying b) \<le> nondeclassifying (a \<sqinter> b)\<close>
  apply clarsimp
  oops



definition
  \<open>really_weak_nondeclassifying a \<equiv> \<lambda>(sx, sy).
    (\<exists>sx'. a (exch4 (\<Delta> sx)) (exch4 (\<Delta> sx'))) \<or>
    (\<exists>sy'. a (exch4 (\<Delta> sy)) (exch4 (\<Delta> sy'))) \<longrightarrow>
    Ex (a (exch4 (sx, sy)))\<close>


(*
section \<open> Improved same_initcomm_and_aact_then_same_fincomm \<close>

definition
  \<open>strong_quasireflp_steprel r \<equiv>
    (\<lambda>(ax, ay).
      (\<forall>ax' ay'.
        r (\<ddagger> (ax, ay)) (\<ddagger> (ax', ay')) \<longrightarrow>
        r (\<ddagger> (\<Delta> ax)) (\<ddagger> (\<Delta> ax')) \<and> r (\<ddagger> (\<Delta> ay)) (\<ddagger> (\<Delta> ay'))) \<and>
      (\<forall>a1' a2'.
        r (\<ddagger> (ax, ax)) (\<ddagger> (a1', a2')) \<longrightarrow>
        r (\<ddagger> (\<Delta> ax)) (\<ddagger> (\<Delta> a1')) \<and> r (\<ddagger> (\<Delta> ax)) (\<ddagger> (\<Delta> a2'))) \<and>
      (\<forall>a1' a2'.
        r (\<ddagger> (ay, ay)) (\<ddagger> (a1', a2')) \<longrightarrow>
        r (\<ddagger> (\<Delta> ay)) (\<ddagger> (\<Delta> a1')) \<and> r (\<ddagger> (\<Delta> ay)) (\<ddagger> (\<Delta> a2'))) ) \<circ> exch4\<close>

lemma strong_quasireflp_atoms_extract_left:
  \<open>all_atoms strong_quasireflp_steprel c (\<ddagger> (a, b)) \<Longrightarrow>
    all_atoms strong_quasireflp_steprel c (\<ddagger> (\<Delta> a))\<close>
  by (induct c) (force simp add: strong_quasireflp_steprel_def)+

lemma strong_quasireflp_atoms_extract_right:
  \<open>all_atoms strong_quasireflp_steprel c (\<ddagger> (a, b)) \<Longrightarrow>
    all_atoms strong_quasireflp_steprel c (\<ddagger> (\<Delta> b))\<close>
  by (induct c) (force simp add: strong_quasireflp_steprel_def)+

lemma strong_quasireflp_atoms_then_unliftC_ablocked_iff_reflpair_ablocked:
  \<open>all_atoms strong_quasireflp_steprel c (\<ddagger> (\<Delta> a)) \<Longrightarrow>
    (a, unliftC c) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> (\<ddagger> (\<Delta> a), c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  by (induct c) (force simp add: unliftC_rev_iff strong_quasireflp_steprel_def)+

lemma pred_lift_false[simp]:
  \<open>\<lblot> \<lambda>s. False \<bar> q \<rblot> = \<bottom>\<close>
  \<open>\<lblot> p \<bar> \<lambda>s. False \<rblot> = \<bottom>\<close>
  by (simp add: fun_eq_iff)+

lemma same_initcomm_and_aact_then_same_fincomm2:
  assumes
    \<open>(sx, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', cx')\<close>
    \<open>sx = \<ddagger> (\<Delta> ax)\<close>
    \<open>sx' = \<ddagger> (\<Delta> ax')\<close>
    \<open>(sy, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', cy')\<close>
    \<open>sy = \<ddagger> (\<Delta> ay)\<close>
    \<open>sy' = \<ddagger> (\<Delta> ay')\<close>
    \<open>head_branch_determ (unliftC c) (\<ddagger> (ax, ay))\<close>
    \<open>all_head_atoms strong_quasireflp_steprel c (\<ddagger> (ax, ay))\<close>
  shows
    \<open>cy' = cx'\<close>
  using assms
proof (induct c arbitrary: \<pi>\<alpha> cx' cy')
  case (Endet c1 c2)
  show ?case
    using Endet.prems
    apply (clarsimp simp del: disj_not1 simp add: head_atomic_then_any_head_guard_eq_not_ablocked)
    sorry
    apply (case_tac \<open>c2 = Skip\<close>, force)
    apply (case_tac \<open>snd \<pi>\<alpha>\<close>)
     apply clarsimp
     apply (elim disjE[of \<open>Ex _\<close>])
        apply (force intro: Endet.hyps(1))
       apply (metis aopstep_no_aopstep_contra
        strong_quasireflp_atoms_extract_left
        strong_quasireflp_atoms_extract_right
        strong_quasireflp_atoms_then_unliftC_ablocked_iff_reflpair_ablocked)
       apply (metis aopstep_no_aopstep_contra
        strong_quasireflp_atoms_extract_left
        strong_quasireflp_atoms_extract_right
        strong_quasireflp_atoms_then_unliftC_ablocked_iff_reflpair_ablocked)
     apply (force intro: Endet.hyps(2))
    apply clarsimp
    apply (elim disjE[of \<open>aopstep _ _ _\<close>])
       apply (force intro: Endet.hyps(1))
      apply (metis aopstep_no_aopstep_contra
        strong_quasireflp_atoms_extract_left
        strong_quasireflp_atoms_extract_right
        strong_quasireflp_atoms_then_unliftC_ablocked_iff_reflpair_ablocked)
     apply (metis aopstep_no_aopstep_contra
        strong_quasireflp_atoms_extract_left
        strong_quasireflp_atoms_extract_right
        strong_quasireflp_atoms_then_unliftC_ablocked_iff_reflpair_ablocked)
    apply (force intro: Endet.hyps(2))
    done
next
  case (Iter c)
  show ?case
    using Iter.prems
    apply (clarsimp simp add: head_atomic_then_agree_pass_guard_iff_agree_ablocked)
    apply (simp add: sec_agree_def)
    apply (simp add: strong_quasireflp_atoms_then_unliftC_ablocked_iff_reflpair_ablocked
        strong_quasireflp_atoms_extract_left strong_quasireflp_atoms_extract_right)
    apply (elim disjE)
       apply force
      apply (force dest: aopstep_no_aopstep_contra)
     apply (force dest: aopstep_no_aopstep_contra)
    apply (force intro: Iter.hyps)
    done
qed force+
*)

section \<open> Comm Times \<close>

function(sequential) comm_Times :: \<open>'a comm \<Rightarrow> 'b comm \<Rightarrow> ('a \<times> 'b) comm\<close> (infixr \<open>\<times>\<^sub>C\<close> 80) where
  \<open>Skip \<times>\<^sub>C Skip = Skip\<close>
| \<open>(cax;;cay) \<times>\<^sub>C (cbx;;cby) = (cax \<times>\<^sub>C cbx) ;; (cay \<times>\<^sub>C cby)\<close>
| \<open>(cax \<parallel> cay) \<times>\<^sub>C (cbx \<parallel> cby) = (cax \<times>\<^sub>C cbx) \<parallel> (cay \<times>\<^sub>C cby)\<close>
| \<open>(cax \<^bold>\<sqinter> cay) \<times>\<^sub>C (cbx \<^bold>\<sqinter> cby) = (cax \<times>\<^sub>C cbx) \<^bold>\<sqinter> (cay \<times>\<^sub>C cby)\<close>
| \<open>(cax \<^bold>\<box> cay) \<times>\<^sub>C (cbx \<^bold>\<box> cby) = (cax \<times>\<^sub>C cbx) \<^bold>\<box> (cay \<times>\<^sub>C cby)\<close>
| \<open>(DO ca OD) \<times>\<^sub>C (DO cb OD) = DO (ca \<times>\<^sub>C cb) OD\<close>
| \<open>\<langle>ra\<rangle> \<times>\<^sub>C \<langle>rb\<rangle> = \<langle>ra \<times>\<^sub>R rb\<rangle>\<close>
| \<open>_ \<times>\<^sub>C _ = undefined\<close>
  by pat_completeness auto (* slow *)

termination
  by (relation \<open>measure (\<lambda>(ca,cb). size ca + size cb)\<close>) simp+

lemma comm_Times_rev[simp]:
  \<open>c \<times>\<^sub>C c = Skip \<longleftrightarrow> c = Skip\<close>
  \<open>c \<times>\<^sub>C c = ca' ;; cb' \<longleftrightarrow>
    (\<exists>ca cb. ca' = ca \<times>\<^sub>C ca \<and> cb' = cb \<times>\<^sub>C cb \<and> c = ca ;; cb)\<close>
  \<open>c \<times>\<^sub>C c = ca' \<parallel> cb' \<longleftrightarrow>
    (\<exists>ca cb. ca' = ca \<times>\<^sub>C ca \<and> cb' = cb \<times>\<^sub>C cb \<and> c = ca \<parallel> cb)\<close>
  \<open>c \<times>\<^sub>C c = ca' \<^bold>\<sqinter> cb' \<longleftrightarrow>
    (\<exists>ca cb. ca' = ca \<times>\<^sub>C ca \<and> cb' = cb \<times>\<^sub>C cb \<and> c = ca \<^bold>\<sqinter> cb)\<close>
  \<open>c \<times>\<^sub>C c = ca' \<^bold>\<box> cb' \<longleftrightarrow>
    (\<exists>ca cb. ca' = ca \<times>\<^sub>C ca \<and> cb' = cb \<times>\<^sub>C cb \<and> c = ca \<^bold>\<box> cb)\<close>
  \<open>c \<times>\<^sub>C c = DO c' OD \<longleftrightarrow> (\<exists>ca cb. c' = ca \<times>\<^sub>C ca \<and> c = DO ca OD)\<close>
  \<open>c \<times>\<^sub>C c = \<langle>r'\<rangle> \<longleftrightarrow> (\<exists>r. r' = r \<times>\<^sub>R r \<and> c = \<langle>r\<rangle>)\<close>
  by (induct c; clarsimp; argo)+

subsubsection \<open> control-flow matching \<close>

inductive cfmatchC :: \<open>'a comm \<Rightarrow> 'b comm \<Rightarrow> bool\<close> where
  cfmatch_skip[simp]: \<open>cfmatchC Skip Skip\<close>
| cfmatch_seq[intro!]:
  \<open>cfmatchC cax cay \<Longrightarrow> cfmatchC cbx cby \<Longrightarrow> cfmatchC (cax ;; cbx) (cay ;; cby)\<close>
| cfmatch_indet[intro!]:
  \<open>cfmatchC cax cay \<Longrightarrow> cfmatchC cbx cby \<Longrightarrow> cfmatchC (cax \<^bold>\<sqinter> cbx) (cay \<^bold>\<sqinter> cby)\<close>
| cfmatch_endet[intro!]:
  \<open>cfmatchC cax cay \<Longrightarrow> cfmatchC cbx cby \<Longrightarrow> cfmatchC (cax \<^bold>\<box> cbx) (cay \<^bold>\<box> cby)\<close>
| cfmatch_par[intro!]:
  \<open>cfmatchC cax cay \<Longrightarrow> cfmatchC cbx cby \<Longrightarrow> cfmatchC (cax \<parallel> cbx) (cay \<parallel> cby)\<close>
| cfmatch_dood[intro!]:
  \<open>cfmatchC cx cy \<Longrightarrow> cfmatchC (DO cx OD) (DO cy OD)\<close>
| cfmatch_atom[simp]: \<open>cfmatchC (\<langle>arx\<rangle>) (\<langle>ary\<rangle>)\<close>

inductive_cases cfmatchC_Skip_leftE[elim!]: \<open>cfmatchC Skip cy\<close>
inductive_cases cfmatchC_Seq_leftE[elim!]: \<open>cfmatchC (cax ;; cbx) cy\<close>
inductive_cases cfmatchC_INDet_leftE[elim!]: \<open>cfmatchC (cax \<^bold>\<sqinter> cbx) cy\<close>
inductive_cases cfmatchC_ENDet_leftE[elim!]: \<open>cfmatchC (cax \<^bold>\<box> cbx) cy\<close>
inductive_cases cfmatchC_Par_leftE[elim!]: \<open>cfmatchC (cax \<parallel> cbx) cy\<close>
inductive_cases cfmatchC_Iter_leftE[elim!]: \<open>cfmatchC (DO cx OD) cy\<close>
inductive_cases cfmatchC_Atom_leftE[elim!]: \<open>cfmatchC (\<langle>arx\<rangle>) cy\<close>

inductive_cases cfmatchC_Skip_rightE[elim!]: \<open>cfmatchC cx Skip\<close>
inductive_cases cfmatchC_Seq_rightE[elim!]: \<open>cfmatchC cx (cay ;; cby)\<close>
inductive_cases cfmatchC_INDet_rightE[elim!]: \<open>cfmatchC cx (cay \<^bold>\<sqinter> cby)\<close>
inductive_cases cfmatchC_ENDet_rightE[elim!]: \<open>cfmatchC cx (cay \<^bold>\<box> cby)\<close>
inductive_cases cfmatchC_Par_rightE[elim!]: \<open>cfmatchC cx (cay \<parallel> cby)\<close>
inductive_cases cfmatchC_Iter_rightE[elim!]: \<open>cfmatchC cx (DO cy OD)\<close>
inductive_cases cfmatchC_Atom_rightE[elim!]: \<open>cfmatchC cx (\<langle>ary\<rangle>)\<close>

lemma cfmatchC_iff[simp]:
  \<open>cfmatchC Skip cy \<longleftrightarrow> cy = Skip\<close>
  \<open>cfmatchC cx Skip \<longleftrightarrow> cx = Skip\<close>
  \<open>cfmatchC (cax ;; cbx) cy \<longleftrightarrow> (\<exists>cay cby. cy = cay ;; cby \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC cx (cay ;; cby) \<longleftrightarrow> (\<exists>cax cbx. cx = cax ;; cbx \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC (cax \<^bold>\<sqinter> cbx) cy \<longleftrightarrow> (\<exists>cay cby. cy = cay \<^bold>\<sqinter> cby \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC cx (cay \<^bold>\<sqinter> cby) \<longleftrightarrow> (\<exists>cax cbx. cx = cax \<^bold>\<sqinter> cbx \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC (cax \<^bold>\<box> cbx) cy \<longleftrightarrow> (\<exists>cay cby. cy = cay \<^bold>\<box> cby \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC cx (cay \<^bold>\<box> cby) \<longleftrightarrow> (\<exists>cax cbx. cx = cax \<^bold>\<box> cbx \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC (cax \<parallel> cbx) cy \<longleftrightarrow> (\<exists>cay cby. cy = cay \<parallel> cby \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC cx (cay \<parallel> cby) \<longleftrightarrow> (\<exists>cax cbx. cx = cax \<parallel> cbx \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC (DO cx' OD) cy \<longleftrightarrow> (\<exists>cy'. cy = DO cy' OD \<and> cfmatchC cx' cy')\<close>
  \<open>cfmatchC cx (DO cy' OD) \<longleftrightarrow> (\<exists>cx'. cx = DO cx' OD \<and> cfmatchC cx' cy')\<close>
  \<open>cfmatchC \<langle>arx\<rangle> cy \<longleftrightarrow> (\<exists>ary. cy = \<langle>ary\<rangle>)\<close>
  \<open>cfmatchC cx \<langle>ary\<rangle> \<longleftrightarrow> (\<exists>arx. cx = \<langle>arx\<rangle>)\<close>
  by fastforce+

lemma liftC_eq:
  \<open>liftC c = map_atom (\<lambda>ar. ar \<circ>\<^sub>2 exch4) (c \<times>\<^sub>C c)\<close>
  unfolding liftR_def
  by (induct c) simp+


section \<open> Extended Action Semantics \<close>

subsection \<open> Extended Actions \<close>

datatype 'a eact =
  EAEndetL \<open>'a eact\<close> |
  EAEndetR \<open>'a eact\<close> |
  EAParL \<open>'a eact\<close> |
  EAParR \<open>'a eact\<close> |
  EATau |
  EAAtom 'a

fun eact_to_plabel :: \<open>'a eact \<Rightarrow> plabel\<close> where
  \<open>eact_to_plabel (EAEndetL ha) = eact_to_plabel ha\<close>
| \<open>eact_to_plabel (EAEndetR ha) = eact_to_plabel ha\<close>
| \<open>eact_to_plabel (EAParL ha) = PL (eact_to_plabel ha)\<close>
| \<open>eact_to_plabel (EAParR ha) = PR (eact_to_plabel ha)\<close>
| \<open>eact_to_plabel EATau = PHere\<close>
| \<open>eact_to_plabel (EAAtom a) = PHere\<close>

fun eact_leaf :: \<open>'a eact \<Rightarrow> 'a option\<close> where
  \<open>eact_leaf (EAEndetL ha) = eact_leaf ha\<close>
| \<open>eact_leaf (EAEndetR ha) = eact_leaf ha\<close>
| \<open>eact_leaf (EAParL ha) = eact_leaf ha\<close>
| \<open>eact_leaf (EAParR ha) = eact_leaf ha\<close>
| \<open>eact_leaf EATau = None\<close>
| \<open>eact_leaf (EAAtom a) = Some a\<close>

definition \<open>eact_to_act \<alpha> = (if eact_leaf \<alpha> = None then Tau else Vis)\<close>

lemmas eact_to_act_simps[simp] =
  eact_leaf.simps[
    THEN arg_cong[where f=\<open>\<lambda>x. if x = None then Tau else Vis\<close>],
    simplified eact_to_act_def[symmetric], simplified]


subsection \<open> Annotated Opstep \<close>

fun aaopstep :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) eact \<Rightarrow> 's pconfig \<Rightarrow> 's pconfig \<Rightarrow> bool\<close> where
  \<open>aaopstep \<eta> (s, Skip) sc' \<longleftrightarrow> False\<close>
| \<open>aaopstep \<eta> (s, ca ;; cb) sc' \<longleftrightarrow>
    \<eta> = EATau \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    (\<exists>s' ca'. aaopstep \<eta> (s, ca) (s', ca') \<and> sc' = (s', ca' ;; cb))\<close>
| \<open>aaopstep \<eta> (s, ca \<^bold>\<sqinter> cb) sc' \<longleftrightarrow>
    \<eta> = EATau \<and> sc' = (s, ca) \<or>
    \<eta> = EATau \<and> sc' = (s, cb)\<close>
| \<open>aaopstep \<eta> (s, ca \<^bold>\<box> cb) sc' \<longleftrightarrow>
    \<eta> = EATau \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    \<eta> = EATau \<and> cb = Skip \<and> sc' = (s, ca) \<or>
    (\<exists>\<eta>' s' ca'.
      \<eta> = EAEndetL \<eta>' \<and>
      aaopstep \<eta>' (s, ca) (s', ca') \<and>
      sc' = (if eact_leaf \<eta> = None then (s', ca' \<^bold>\<box> cb) else (s', ca'))) \<or>
    (\<exists>\<eta>' s' cb'.
      \<eta> = EAEndetR \<eta>' \<and> 
      aaopstep \<eta>' (s, cb) (s', cb') \<and>
      sc' = (if eact_leaf \<eta> = None then (s', ca \<^bold>\<box> cb') else (s', cb')))\<close>
| \<open>aaopstep \<eta> (s, ca \<parallel> cb) sc' \<longleftrightarrow>
    \<eta> = EATau \<and> ca = Skip \<and> cb = Skip \<and> sc' = (s, Skip) \<or>
    (\<exists>\<eta>' s' ca'. \<eta> = EAParL \<eta>' \<and> aaopstep \<eta>' (s, ca) (s', ca') \<and> sc' = (s', ca' \<parallel> cb)) \<or>
    (\<exists>\<eta>' s' cb'. \<eta> = EAParR \<eta>' \<and> aaopstep \<eta>' (s, cb) (s', cb') \<and> sc' = (s', ca \<parallel> cb'))\<close>
| \<open>aaopstep \<eta> (s, DO c OD) sc' \<longleftrightarrow>
    \<eta> = EATau \<and> (\<forall>\<eta>' sc'. \<not> aaopstep \<eta>' (s, c) sc') \<and> sc' = (s, Skip) \<or>
    (\<exists>s' c'. aaopstep \<eta> (s, c) (s', c') \<and> sc' = (s', c' ;; DO c OD))\<close>
| \<open>aaopstep \<eta> (s, \<langle>a\<rangle>) sc' \<longleftrightarrow>
    \<eta> = EAAtom a \<and> a s (fst sc') \<and> snd sc' = Skip\<close>

lemmas aaopstep_induct = aaopstep.induct[case_names Skip Seq Indet Endet Par DoLoop Atom]


paragraph \<open> Pretty parallel operational semantics \<close>

text \<open> \<open>sc\<close> can step to \<open>sc'\<close> \<close>
abbreviation pretty_aaopstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sub>a\<^sub>a _\<close> [60,0,60] 60) where
  \<open>sc \<midarrow>\<eta>\<rightarrow>\<^sub>a\<^sub>a sc' \<equiv> aaopstep \<eta> sc sc'\<close>

text \<open> no steps from \<open>sc\<close> can take place \<close>
definition no_aaopstep :: \<open>'s \<times> 's comm \<Rightarrow> bool\<close> (\<open>_ \<midarrow>'/\<rightarrow>\<^sub>a\<^sub>a\<close> [60] 60) where
  \<open>sc \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a \<equiv> \<forall>\<eta> sc'. \<not> aaopstep \<eta> sc sc'\<close>

lemma aaopstep_do_loop_iff[simp]:
  \<open>aaopstep \<eta> (s, DO c OD) sc' \<longleftrightarrow>
    \<eta> = EATau \<and> (s, c) \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a \<and> sc' = (s, Skip) \<or>
    (\<exists>s' c'. aaopstep \<eta> (s, c) (s', c') \<and> sc' = (s', c' ;; DO c OD))\<close>
  by (simp add: no_aaopstep_def)

declare aaopstep.simps(6)[simp del]


lemma pretty_no_aopstep_simps[simp]:
  \<open>(s, Skip) \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a\<close>
  \<open>(s, ca ;; cb) \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a \<longleftrightarrow> ca \<noteq> Skip \<and> (s, ca) \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a\<close>
  \<open>(s, ca \<^bold>\<sqinter> cb) \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a \<longleftrightarrow> False\<close>
  \<open>(s, ca \<^bold>\<box> cb) \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a \<longleftrightarrow> ca \<noteq> Skip \<and> cb \<noteq> Skip \<and> (s, ca) \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a \<and> (s, cb) \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a\<close>
  \<open>(s, ca \<parallel> cb) \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a \<longleftrightarrow> (cb \<noteq> Skip \<or> ca \<noteq> Skip) \<and> (s, ca) \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a \<and> (s, cb) \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a\<close>
  \<open>(s, DO c OD) \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a \<longleftrightarrow> False\<close>
  \<open>(s, \<langle> ar \<rangle>) \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a \<longleftrightarrow> (\<nexists>s'. ar s s')\<close>
  by (clarsimp simp add: no_aaopstep_def all_conj_distrib; blast)+


subsubsection \<open> aaopstep lemmas \<close>

lemma aaopstep_tau_preserves_state:
  \<open>sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a\<^sub>a sc' \<Longrightarrow> eact_leaf \<alpha> = None \<Longrightarrow> fst sc' = fst sc\<close>
  by (induct \<alpha> sc sc' rule: aaopstep_induct) fastforce+

lemma vis_aaopstep_vis_eact_is_head_atom:
  \<open>sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a\<^sub>a sc' \<Longrightarrow> eact_leaf \<alpha> = Some a \<Longrightarrow> a \<in># head_atoms (snd sc)\<close>
  by (induct \<alpha> sc sc' rule: aaopstep_induct) fastforce+

lemma aaopstep_vis_eact_is_exec_atom:
  \<open>sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a\<^sub>a sc' \<Longrightarrow> eact_leaf \<alpha> = Some a \<Longrightarrow> a (fst sc) (fst sc')\<close>
  by (induct \<alpha> sc sc' rule: aaopstep_induct) fastforce+

lemma aaopstep_eact_cases:
  \<open>sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a\<^sub>a sc' \<Longrightarrow>
    (\<And>a. sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a\<^sub>a sc' \<Longrightarrow> eact_leaf \<alpha> = Some a \<Longrightarrow> a (fst sc) (fst sc') \<Longrightarrow> P) \<Longrightarrow>
    (sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a\<^sub>a sc' \<Longrightarrow> eact_leaf \<alpha> = None \<Longrightarrow> fst sc' = fst sc \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  by (metis aaopstep_tau_preserves_state aaopstep_vis_eact_is_exec_atom option.collapse)

lemma aaopstep_aablocked_contra:
  \<open>sc \<midarrow>\<eta>\<rightarrow>\<^sub>a\<^sub>a sc' \<Longrightarrow> sc \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a \<Longrightarrow> False\<close>
  using no_aaopstep_def by blast

subsubsection \<open> aaopstep and opstep \<close>

lemma no_opstep_iff_no_aaopstep:
  \<open>(s, c) \<midarrow>/\<rightarrow> \<longleftrightarrow> (s, c) \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a\<close>
  by (induct c)
    (force simp add: all_act_iff all_conj_distrib pretty_no_opstep_def)+

lemmas head_atomic_then_any_head_guard_eq_not_aablocked =
  head_atomic_then_any_head_guard_eq_not_blocked[simplified no_opstep_iff_no_aaopstep]

lemma opstep_then_aaopstep:
  \<open>sc \<midarrow>\<alpha>\<rightarrow> sc' \<Longrightarrow> \<exists>\<epsilon>. eact_to_act \<epsilon> = \<alpha> \<and> sc \<midarrow>\<epsilon>\<rightarrow>\<^sub>a\<^sub>a sc'\<close>
  apply (induct \<alpha> sc sc' rule: opstep_induct)
        apply force
       apply force
      apply force
     apply (clarsimp del: disjCI simp add: conj_disj_distribL ex_disj_distrib)
     apply (case_tac \<alpha>)
      apply clarsimp
      apply (metis (full_types) act_not_eq_iff(1) eact_leaf.simps(1) eact_to_act_def eact_to_act_simps(2)
      option.distinct(1))
     apply clarsimp
     apply (metis (full_types) act_not_eq_iff(2) eact_leaf.simps(1,2) eact_to_act_def)
    apply clarsimp
    apply (metis eact_to_act_simps(3,4,5))
   apply (clarsimp simp add: conj_disj_distribL ex_disj_distrib)
   apply (metis no_opstep_iff_no_aaopstep split_pairs)
  apply force
  done

lemma aaopstep_then_opstep:
  \<open>sc \<midarrow>\<epsilon>\<rightarrow>\<^sub>a\<^sub>a sc' \<Longrightarrow> sc \<midarrow>eact_to_act \<epsilon>\<rightarrow> sc'\<close>
  apply (induct \<epsilon> sc sc' rule: aaopstep_induct)
        apply force
       apply force
      apply force
     apply clarsimp
  oops


section \<open> Declassification is Local \<close>

lemma same_initcomm_and_plabel_then_same_eact_and_fincomm:
  \<open>(sx, c) \<midarrow>\<alpha>x\<rightarrow>\<^sub>a\<^sub>a (sx', cx') \<Longrightarrow>
    (sy, c) \<midarrow>\<alpha>y\<rightarrow>\<^sub>a\<^sub>a (sy', cy') \<Longrightarrow>
    head_branch_determ c (sx, sy) \<Longrightarrow>
    eact_to_plabel \<alpha>x = eact_to_plabel \<alpha>y \<Longrightarrow>
    \<alpha>x = \<alpha>y \<and> cx' = cy'\<close>
proof (induct c arbitrary: \<alpha>x cx' \<alpha>y cy')
  case (Endet c1 c2)
  then show ?case
    apply (clarsimp simp del: disj_not1 simp add: head_atomic_then_any_head_guard_eq_not_aablocked)
    apply (case_tac \<open>\<alpha>x = EATau\<close>; case_tac \<open>\<alpha>y = EATau\<close>)
       apply force
      apply clarsimp
    subgoal sorry
    subgoal sorry
    apply clarsimp
    apply (subgoal_tac
        \<open>(\<exists>\<alpha>'. \<alpha>x = EAEndetL \<alpha>') \<and> (\<exists>\<alpha>'. \<alpha>y = EAEndetL \<alpha>') \<or>
        (\<exists>\<alpha>'. \<alpha>x = EAEndetR \<alpha>') \<and> (\<exists>\<alpha>'. \<alpha>y = EAEndetR \<alpha>')\<close>)
     prefer 2
     apply (simp add: no_aaopstep_def, blast)
    apply (elim disjE[of \<open>Ex _ \<and> Ex _\<close>])
     apply clarsimp
     apply (metis prod.inject)
    apply clarsimp
    apply (metis prod.inject)
    done
next
  case (Iter c)
  then show ?case
    apply (clarsimp simp add: stable_comm_then_any_head_guard_iff_not_blocked
        no_opstep_iff_no_aaopstep sec_agree_def)
    apply (blast dest: aaopstep_aablocked_contra)
    done
qed fastforce+


section \<open> Proving Step Bismulation \<close>

definition simstep_bkw :: \<open>('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a \<Rightarrow> bool)\<close> where
  \<open>simstep_bkw a q \<equiv> \<lambda>(x, y).
    (\<forall>x'. a x x' \<longrightarrow> (\<exists>y'. a y y' \<and> q (x', y'))) \<and>
    (\<forall>y'. a y y' \<longrightarrow> (\<exists>x'. a x x' \<and> q (x', y')))\<close>

definition simstep_bkw_exch4
  :: \<open>('a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool) \<Rightarrow>
        (('a \<times> 'a) \<times> ('b \<times> 'b) \<Rightarrow> bool) \<Rightarrow>
        (('a \<times> 'a) \<times> ('b \<times> 'b) \<Rightarrow> bool)\<close>
  (\<open>simstep'_bkw\<^sub>\<ddagger>\<close>)
  where
    \<open>simstep_bkw\<^sub>\<ddagger> r q \<equiv> simstep_bkw r (q \<circ> exch4) \<circ> exch4\<close>

abbreviation \<open>head_atoms_simstep c q \<equiv> all_head_atoms (\<lambda>a. simstep_bkw a q) c\<close>
abbreviation \<open>all_atoms_simstep c q \<equiv> all_atoms (\<lambda>a. simstep_bkw a q) c\<close>

lemma head_equiv_blocking_then_nostepl_iff_nostepr:
  \<open>head_atoms_simstep c q (sx, sy) \<Longrightarrow>
    (sx, c) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> (sy, c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  by (induct c)
    (force simp add: simstep_bkw_def)+

lemma head_atoms_simstep_corresponding_step_left:
  assumes
    \<open>(sx, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', c')\<close>
    \<open>head_atoms_simstep c I (sx, sy)\<close>
    \<open>I (sx, sy)\<close>
  shows
    \<open>\<exists>sy'. (sy, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', c') \<and> I (sx', sy')\<close>
  using assms
proof (induct c arbitrary: \<pi>\<alpha> c')
  case (Seq cc1 cc2)
  show ?case
    using Seq.prems
    apply clarsimp
    apply (elim disjE; clarsimp)
    apply (frule Seq.hyps(1); force)
    done
next
  case (Par cc1 cc2)
  show ?case
    using Par.prems
    apply clarsimp
    apply (elim disjE; clarsimp)
     apply (frule(1) Par.hyps(1); force)
    apply (frule(1) Par.hyps(2); force)
    done
next
  case (Indet c1 c2)
  then show ?case
    by auto
next
  case (Endet cc1 cc2)
  show ?case
    using Endet.prems
    apply clarsimp
    apply (elim disjE; clarsimp)
         apply blast
        apply blast
       apply (frule Endet.hyps(1); force)
      apply (frule Endet.hyps(2); force)
     apply (frule Endet.hyps(1); force)
    apply (frule Endet.hyps(2); force)
    done
next
  case (Iter cc)
  show ?case
    using Iter.prems
    apply clarsimp
    apply (elim disjE; clarsimp)
     apply (simp add: head_equiv_blocking_then_nostepl_iff_nostepr; fail)
    apply (frule Iter.hyps(1); force)
    done
qed (clarsimp simp add: simstep_bkw_def)+

lemma head_atoms_simstep_corresponding_step_right:
  assumes
    \<open>(sy, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', c')\<close>
    \<open>head_atoms_simstep c I (sx, sy)\<close>
    \<open>I (sx, sy)\<close>
  shows
    \<open>\<exists>sx'. (sx, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', c') \<and> I (sx', sy')\<close>
  using assms
proof (induct c arbitrary: \<pi>\<alpha> c')
  case (Seq cc1 cc2)
  show ?case
    using Seq.prems
    apply clarsimp
    apply (elim disjE; clarsimp)
    apply (frule Seq.hyps(1); force)
    done
next
  case (Par cc1 cc2)
  show ?case
    using Par.prems
    apply clarsimp
    apply (elim disjE; clarsimp)
     apply (frule(1) Par.hyps(1); force)
    apply (frule(1) Par.hyps(2); force)
    done
next
  case (Indet c1 c2)
  then show ?case
    by auto
next
  case (Endet cc1 cc2)
  show ?case
    using Endet.prems
    apply clarsimp
    apply (elim disjE; clarsimp)
         apply blast
        apply blast
       apply (frule Endet.hyps(1); force)
      apply (frule Endet.hyps(2); force)
     apply (frule Endet.hyps(1); force)
    apply (frule Endet.hyps(2); force)
    done
next
  case (Iter cc)
  show ?case
    using Iter.prems
    apply clarsimp
    apply (elim disjE; clarsimp)
     apply (simp add: head_equiv_blocking_then_nostepl_iff_nostepr; fail)
    apply (frule Iter.hyps(1); force)
    done
qed (clarsimp simp add: simstep_bkw_def)+


section \<open> Sim reflstep \<close>

lemma head_atoms_simstep_corresponding_reflstep_l2r:
  assumes
    \<open>(exch4 (\<Delta> sx), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (exch4 (\<Delta> sx'), c')\<close>
    \<open>head_atoms_simstep (unliftC c) I (sx, sy)\<close>
    \<open>I (sx, sy)\<close>
  shows
    \<open>\<exists>sy'. (exch4 (\<Delta> sy), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (exch4 (\<Delta> sy'), c') \<and> I (sx', sy')\<close>
  using assms
proof (induct c arbitrary: \<pi>\<alpha> c')
  case (Seq cc1 cc2)
  show ?case
    using Seq.prems
    apply clarsimp
    apply (elim disjE)
     apply (metis surjective_pairing)
    apply (metis Seq.hyps(1)[simplified])
    done
next
  case (Par cc1 cc2)
  show ?case
    using Par.prems
    apply clarsimp
    apply (elim disjE; clarsimp)
     apply (frule(1) Par.hyps(1); force)
    apply (frule(1) Par.hyps(2); force)
    sorry
next
  case (Indet c1 c2)
  then show ?case
    sorry
next
  case (Endet cc1 cc2)
  show ?case
    using Endet.prems
    apply clarsimp
    apply (elim disjE; clarsimp)
         apply blast
        apply blast
       apply (frule Endet.hyps(1); force)
      apply (frule Endet.hyps(2); force)
     apply (frule Endet.hyps(1); force)
    apply (frule Endet.hyps(2); force)
    sorry
next
  case (Iter cc)
  show ?case
    using Iter.prems
    apply clarsimp
    apply (elim disjE; clarsimp)
     apply (simp add: head_equiv_blocking_then_nostepl_iff_nostepr; fail)
    apply (frule Iter.hyps(1); force)
    sorry
qed (force simp add: simstep_bkw_def exch4_def)+

lemmas head_atoms_simstep_corresponding_reflstep_l2r' =
  head_atoms_simstep_corresponding_reflstep_l2r[
    where sx=\<open>(lsx,ssx)\<close> and sy=\<open>(lsy,ssy)\<close> and
       sx'=\<open>(lsx',ssx')\<close> for lsx ssx lsy ssy lsx' ssx',
      simplified exch4_def, simplified]



section \<open> Strong Quasireflexivity \<close>

definition
  \<open>strong_quasireflp_steprel r \<equiv>
    quasireflp_steprel r \<sqinter>
    (\<lambda>(sx,_). \<forall>sa' sb'.
      r (sx, sx) (sa', sb') \<longrightarrow> r (sx,sx) (sa', sa') \<and> r (sx,sx) (sb', sb')) \<sqinter>
    (\<lambda>(_, sy). \<forall>sa' sb'.
      r (sy, sy) (sa', sb') \<longrightarrow> r (sy,sy) (sa', sa') \<and> r (sy,sy) (sb', sb'))\<close>

lemma await_rel_comp2_exch4_eq[simp]:
  \<open>await_rel p \<circ>\<^sub>2 \<ddagger> = await_rel (p \<circ> \<ddagger>)\<close>
  by (simp add: await_rel_def fun_eq_iff)

lemma strong_quasireflp_steprel_await:
  \<open>\<top> \<le> strong_quasireflp_steprel (await_rel p) \<longleftrightarrow> quasireflp (curry p)\<close>
  by (simp add: strong_quasireflp_steprel_def quasireflp_steprel_def await_rel_def
      quasireflp_iff split: prod.splits; blast)

lemma strong_quasireflp_steprel_declassify:
  \<open>\<top> \<le> strong_quasireflp_steprel (declassify_rel f \<circ>\<^sub>2 exch4)\<close>
  by (simp add: declassify_rel_def strong_quasireflp_steprel_await quasireflp_iff)

lemma strong_quasireflp_steppredrelR:
  \<open>\<top> \<le> strong_quasireflp_steprel (liftR a \<circ>\<^sub>2 exch4)\<close>
  by (clarsimp simp add: strong_quasireflp_steprel_def quasireflp_steprel_def le_fun_def)


section \<open> refl-step vs. unliftC \<close>

definition dpair_merge :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>dpair_merge r \<equiv> \<lambda>s. \<forall>a b. r (s,s) (a,b) \<longrightarrow> r (s,s) (a,a) \<and> r (s,s) (b,b)\<close>

definition dpair_merge_exch4
  :: \<open>(('a, 'b) rgstate \<Rightarrow> ('a, 'b) rgstate \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close>
  (\<open>dpair'_merge\<^sub>\<ddagger>\<close>)
  where
    \<open>dpair_merge\<^sub>\<ddagger> r \<equiv> dpair_merge (r \<circ>\<^sub>2 \<ddagger>)\<close>

lemma no_unliftC_step_iff_no_reflstep:
  assumes \<open>all_atoms dpair_merge\<^sub>\<ddagger> c s\<close>
  shows \<open>(s, unliftC c) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> (\<ddagger> (s, s), c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  using assms
proof (induct c)
  case (Atomic x)
  then show ?case
    by (force simp add: unliftC_rev_iff dpair_merge_exch4_def dpair_merge_def)
qed (simp add: unliftC_rev_iff)+


lemma unliftC_step_iff_reflstep1:
  assumes
    \<open>all_head_atoms quasireflp_steprel\<^sub>\<ddagger> c (\<ddagger> (sx, sx))\<close>
    \<open>all_atoms dpair_merge\<^sub>\<ddagger> c sx\<close>
  shows
    \<open>(sx, unliftC c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', unliftC c') \<Longrightarrow>
      (\<exists>c''. unliftC c' = unliftC c'' \<and> (\<ddagger> (sx, sx), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (\<ddagger> (sx', sx'), c''))\<close>
  using assms
  apply (induct c arbitrary: \<pi>\<alpha> c')
        apply force
       apply (clarsimp simp add: unliftC_rev_iff)
       apply (elim disjE)
        apply force
       apply (metis surj_pair unliftC_simps(2))
      apply (clarsimp simp add: unliftC_rev_iff)
      apply (elim disjE)
        apply force
       apply (clarsimp simp add: unliftC_rev_iff)
       apply metis
      apply (clarsimp simp add: unliftC_rev_iff)
      apply metis
     apply fastforce
    apply (clarsimp simp add: unliftC_rev_iff)
    apply (elim disjE)
         apply blast
        apply blast
       apply (clarsimp simp add: unliftC_rev_iff, metis)
      apply (clarsimp simp add: unliftC_rev_iff, metis)
     apply metis
    apply metis
   apply force
  apply (clarsimp simp add: unliftC_rev_iff)
  apply (elim disjE)
   apply (simp add: unliftC_rev_iff)
   apply (blast dest: no_unliftC_step_iff_no_reflstep)
  apply force
  done

(*
lemma unliftC_step_iff_reflstep2:
  assumes \<open>quasireflp_head_atoms c (exch4 (sx, sx))\<close>
  shows
    \<open>(exch4 (\<Delta> sx), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (exch4 (\<Delta> sx'), c') \<Longrightarrow>
      (sx, unliftC c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', unliftC c')\<close>
  using assms
  apply (induct c arbitrary: \<pi>\<alpha> c')
        apply force
       apply (clarsimp simp add: unliftC_rev_iff)
       apply (elim disjE)
        apply force
       apply (clarsimp simp add: unliftC_rev_iff)
       apply (metis surj_pair)
      apply (clarsimp simp add: unliftC_rev_iff)
      apply (metis surj_pair)
     apply force
    apply (clarsimp simp add: unliftC_rev_iff)
    apply (rename_tac \<pi> \<alpha> c')
    apply (case_tac \<alpha>)
     apply clarsimp
     apply metis
    apply force
   apply force
  apply (clarsimp simp add: unliftC_rev_iff)
  apply (elim disjE)
   apply (force dest: no_unliftC_step_iff_no_reflstep simp add: unliftC_rev_iff)
  apply clarsimp
  apply (metis surjective_pairing)
  done
*)


subsection \<open> misc \<close>

lemma aopstep_preserves_map_atom:
  \<open>(b, map_atom f c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (b', fc') \<Longrightarrow> \<exists>c'. fc' = map_atom f c'\<close>
  by (metis aopstep_then_opstep opstep_preserves_map_atom)

lemma aopstep_preserves_unliftC:
  \<open>(b, unliftC c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (b', uc') \<Longrightarrow> \<exists>c'. uc' = unliftC c'\<close>
  by (simp add: aopstep_preserves_map_atom unliftC_def)

lemma
  assumes \<open>all_head_atoms quasireflp_steprel\<^sub>\<ddagger> c (\<ddagger> (sx, sy))\<close>
  shows
    \<open>(\<ddagger> (sx, sy), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (\<ddagger> (sx', sy'), c') \<Longrightarrow>
      (\<ddagger> (sx, sx), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (\<ddagger> (sx', sx'), c')\<close>
  using assms
  apply (induct c arbitrary: \<pi>\<alpha> c')
        apply force
       apply clarsimp
       apply (metis surjective_pairing)
      apply clarsimp
      apply (metis act.distinct(1) prod.collapse)
     apply force
    apply clarsimp
    apply (rename_tac \<pi> \<alpha> c')
    apply (case_tac \<alpha>)
     apply clarsimp
     apply metis
    apply force
   apply (clarsimp simp add: quasireflp_steprel_exch4_eq simp del: split_paired_All; fail)
  apply clarsimp
  subgoal sorry
  oops


lemma refl_aopstep_then_not_no_unlift_step:
  \<open>(\<ddagger> (\<Delta> sx), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (\<ddagger> (\<Delta> sx'), c') \<Longrightarrow> ((sx, unliftC c) \<midarrow>/\<rightarrow>\<^sub>a) = False\<close>
  \<open>(\<ddagger> (\<Delta> sy), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (\<ddagger> (\<Delta> sy'), c') \<Longrightarrow> ((sy, unliftC c) \<midarrow>/\<rightarrow>\<^sub>a) = False\<close>
  by (induct c arbitrary: \<pi>\<alpha> c')
    (fastforce simp add: quasireflp_steprel_def exch4_def)+

lemma aopstep_merge:
  fixes c :: \<open>('a, 'b) rgstate comm\<close>
  shows
  \<open>all_head_subcomms branch_determ\<^sub>\<ddagger> c (\<ddagger> (sx, sy)) \<Longrightarrow>
    all_head_atoms noninfoflow\<^sub>\<ddagger> c (\<ddagger> (sx, sy)) \<Longrightarrow>
    (\<ddagger> (sx, sy), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (\<ddagger> (sx', sy'), c') \<longleftrightarrow>
      (\<ddagger> (sx, sx), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (\<ddagger> (sx', sx'), c') \<and> (\<ddagger> (sy, sy), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (\<ddagger> (sy', sy'), c')\<close>
proof (induct c arbitrary: \<pi>\<alpha> c')
  case (Seq c1 c2)
  show ?case
    using Seq.prems
    apply (clarsimp simp add: unliftC_rev_iff exch4_def)
    apply (rule iffI)
     apply (elim disjE[of \<open>\<pi>\<alpha> = _ \<and> _\<close>]; clarsimp) (* +0 *)
     apply (metis Seq.hyps(1) exch4_two_apply)
    apply (metis Seq.hyps(1) aopstep.simps(1) comm.inject(1) exch4_two_apply)
    done
next
  case (Par c1 c2)
  show ?case
    using Par.prems
    apply (clarsimp simp del: split_paired_Ex del: disjCI simp add: unliftC_rev_iff exch4_def)
    apply (subgoal_tac \<open>(\<exists>\<alpha>. \<pi>\<alpha> = (PHere, \<alpha>)) \<or> (\<exists>\<pi>' \<alpha>. \<pi>\<alpha> = (PL \<pi>', \<alpha>)) \<or> (\<exists>\<pi>' \<alpha>. \<pi>\<alpha> = (PR \<pi>', \<alpha>))\<close>)
     prefer 2
     apply (case_tac \<open>fst \<pi>\<alpha>\<close>; simp add: split_pairs2; fail)
    apply (elim disjE; clarsimp)
      apply force
     apply (rule iffI; clarsimp; metis Par.hyps(1) exch4_two_apply)
    apply (rule iffI; clarsimp; metis Par.hyps(2) exch4_two_apply)
    done
next
  case (Indet c1 c2)
  show ?case
    using Indet.prems
    by (clarsimp simp add: unliftC_rev_iff)
next
  case (Endet c1 c2)
  show ?case
    using Endet.prems
    apply (clarsimp del: disjCI simp add: unliftC_rev_iff)
    apply (case_tac \<open>snd \<pi>\<alpha>\<close>)
     apply (case_tac \<open>c1 = Skip\<close>; case_tac \<open>c2 = Skip\<close>)
        apply force
       apply clarsimp
       apply (metis (no_types, lifting) Endet.hyps(2) aopstep_tau_preserves_state comm.inject(4)
        exch4_eq_iff fst_conv)
      apply clarsimp
      apply (metis (no_types, lifting) Endet.hyps(1) aopstep_tau_preserves_state comm.inject(4)
        exch4_eq_iff fst_conv)
     apply clarsimp
     apply (metis (no_types, lifting) Endet.hyps(1,2) comm.inject(4) self_aopstep_impossible(1))
    apply clarsimp
    apply (metis Endet.hyps(1,2) aopstep.simps(1) head_atomic_then_any_head_guard_eq_not_ablocked
        refl_aopstep_then_not_no_unlift_step(2) self_aopstep_impossible(1))
    done
next
  case (Atomic x)
  then show ?case
    apply clarsimp
    apply (rule iffI)
     apply (clarsimp simp del: split_paired_All simp add: noninfoflow_exch4_eq; fail)
    apply (clarsimp simp del: split_paired_All simp add: noninfoflow_exch4_eq; fail)
    done
next
  case (Iter c)
  show ?case
    using Iter.prems
    apply (clarsimp simp add: unliftC_rev_iff)
    subgoal sorry
    done
qed simp+

lemma
  fixes r :: \<open>'l \<times> 's \<Rightarrow> 'l \<times> 's \<Rightarrow> bool\<close>
  shows
    \<open>(pre_state r \<times>\<^sub>P pre_state r) \<le> simstep_bkw r (post_state r \<times>\<^sub>P post_state r)\<close>
  by (force simp add: simstep_bkw_def le_fun_def pre_state_def post_state_def)

lemma
  \<open>I \<le> simstep_bkw (declassify_rel f \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)) I\<close>
  by (simp add: simstep_bkw_def le_fun_def declassify_rel_def2 sec_agree_exch4_def')

lemma
  \<open>I \<le> simstep_bkw (output_rel f \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)) I\<close>
  by (clarsimp simp add: simstep_bkw_def le_fun_def output_rel_def' all_conj_distrib
      running2_pred_def all_fail_st_eq sec_agree_exch4_def' del: disjCI)


lemma vis_eact_then_that_atom:
  \<open>eact_leaf \<eta> = Some a \<Longrightarrow>
    (s, c) \<midarrow>\<eta>\<rightarrow>\<^sub>a\<^sub>a sc' \<Longrightarrow>
    a s (fst sc')\<close>
  by (induct c arbitrary: \<eta> sc') fastforce+


section \<open> Noninterference bisimulation \<close>

inductive noninterference_bisim
  :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<times> 's \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ('s \<times> 's) comm \<Rightarrow> 's \<times> 's \<Rightarrow> bool\<close>
  for R G I
  where noninterference_bisimI[intro]:
  \<open>\<comment> \<open> State Invariant \<close>
    I s \<Longrightarrow>
    \<comment> \<open> Rely Step \<close>
    (\<And>n' s'. n = Suc n' \<Longrightarrow> R s s' \<Longrightarrow> noninterference_bisim R G I n' c s') \<Longrightarrow>
    \<comment> \<open> Bisimulation \<close>
    (\<And>n' sx sy \<pi>.
      n = Suc n' \<Longrightarrow>
      (\<exists>\<alpha> sc'. (s, c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a sc') \<Longrightarrow>
      s = (sx, sy) \<Longrightarrow>
      (\<forall>\<alpha> sx' c'.
        (\<Delta> sx, c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a (\<Delta> sx', c') \<longrightarrow>
        (\<exists>sy'. (\<Delta> sy, c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a (\<Delta> sy', c') \<and>
            noninterference_bisim R G I n' c' (sx', sy') )) \<and>
      (\<forall>\<alpha> sy' c'.
        (\<Delta> sy, c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a (\<Delta> sy', c') \<longrightarrow>
        (\<exists>sx'. (\<Delta> sx, c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a (\<Delta> sx', c') \<and>
            noninterference_bisim R G I n' c' (sx', sy') ))) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    noninterference_bisim R G I n c s\<close>

thm head_atoms_simstep_corresponding_step_left

(*
lemma
  \<open>(sx, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', c') \<Longrightarrow>
    all_atoms simstep_bkw\<^sub>\<ddagger> (unliftC c) I (\<ddagger> (sx, sy)) \<Longrightarrow>
    I (\<ddagger> (sx, sy)) \<Longrightarrow>
    \<exists>sy'. (sy, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', c') \<and> I (\<ddagger> (sx', sy'))\<close>
  sorry
*)

definition
  \<open>diagstep_replace r \<equiv> \<lambda>(sx, sy).
    (\<forall>sx' sy' sxb'.
      r (sx,sy) (sx', sy') \<longrightarrow>
      r (sx,sx) (sxb', sxb') \<longrightarrow>
      r (sx,sy) (sxb', sy')) \<and>
    (\<forall>sx' sy' syb'.
      r (sx,sy) (sx', sy') \<longrightarrow>
      r (sy,sy) (syb', syb') \<longrightarrow>
      r (sx,sy) (sx', syb'))\<close>

lemma aaopstep_diagstep_replacement_left:
  assumes
    \<open>all_atoms (\<lambda>a. diagstep_replace (a \<circ>\<^sub>2 \<ddagger>) \<circ> \<ddagger>) c (\<ddagger> (sx, sy))\<close>
    \<open>(\<ddagger> (sx, sy), c) \<midarrow>\<eta>\<rightarrow>\<^sub>a\<^sub>a (\<ddagger> (sx', sy'), c')\<close>
    \<open>(\<ddagger> (\<Delta> sx), c) \<midarrow>\<eta>\<rightarrow>\<^sub>a\<^sub>a (\<ddagger> (\<Delta> sx''), c')\<close>
  shows
    \<open>(\<ddagger> (sx, sy), c) \<midarrow>\<eta>\<rightarrow>\<^sub>a\<^sub>a (\<ddagger> (sx'', sy'), c')\<close>
  using assms
  apply (induct c arbitrary: \<eta> c')
        apply force
       apply (clarsimp simp del: split_paired_All)
       apply (case_tac \<open>c1 = Skip\<close>)
        apply (simp; fail)
       apply (clarsimp, metis exch4_def)
      apply (case_tac \<open>\<eta>\<close>; simp) (* +1 *)
       apply (clarsimp, metis exch4_def)
      apply (clarsimp, metis exch4_def)
     apply force
    apply (case_tac \<open>\<eta>\<close>; simp) (* +2 *)
      apply (clarsimp split: if_splits; metis exch4_apply)
     apply (clarsimp split: if_splits; metis exch4_apply)
    apply force
   apply (clarsimp simp add: diagstep_replace_def, metis exch4_two_apply)
  apply (subgoal_tac \<open>c' = Skip \<or> (\<exists>ca' cb'. c' = ca' ;; cb')\<close>)
   prefer 2
   apply force
  apply (elim disjE)
   apply force
  apply (clarsimp simp add: exch4_two_apply)
  done

lemma aaopstep_diagstep_replacement_right:
  assumes
    \<open>all_atoms (\<lambda>a. diagstep_replace (a \<circ>\<^sub>2 \<ddagger>) \<circ> \<ddagger>) c (\<ddagger> (sx, sy))\<close>
    \<open>(\<ddagger> (sx, sy), c) \<midarrow>\<eta>\<rightarrow>\<^sub>a\<^sub>a (\<ddagger> (sx', sy'), c')\<close>
    \<open>(\<ddagger> (\<Delta> sy), c) \<midarrow>\<eta>\<rightarrow>\<^sub>a\<^sub>a (\<ddagger> (\<Delta> sy''), c')\<close>
  shows
    \<open>(\<ddagger> (sx, sy), c) \<midarrow>\<eta>\<rightarrow>\<^sub>a\<^sub>a (\<ddagger> (sx', sy''), c')\<close>
  using assms
  apply (induct c arbitrary: \<eta> c')
        apply force
       apply (clarsimp simp del: split_paired_All)
       apply (case_tac \<open>c1 = Skip\<close>)
        apply (simp; fail)
       apply (clarsimp, metis exch4_def)
      apply (case_tac \<open>\<eta>\<close>; simp) (* +1 *)
       apply (clarsimp, metis exch4_def)
      apply (clarsimp, metis exch4_def)
     apply force
    apply (case_tac \<open>\<eta>\<close>; simp) (* +2 *)
      apply (clarsimp split: if_splits; metis exch4_apply)
     apply (clarsimp split: if_splits; metis exch4_apply)
    apply force
   apply (clarsimp simp add: diagstep_replace_def, metis exch4_two_apply)
  apply (subgoal_tac \<open>c' = Skip \<or> (\<exists>ca' cb'. c' = ca' ;; cb')\<close>)
   prefer 2
   apply force
  apply (elim disjE)
   apply force
  apply (clarsimp simp add: exch4_two_apply)
  done

lemma no_aopstep_iff_no_aaopstep:
  \<open>sc \<midarrow>/\<rightarrow>\<^sub>a = sc \<midarrow>/\<rightarrow>\<^sub>a\<^sub>a\<close>
  using no_opstep_iff_no_aaopstep no_opstep_iff_no_aopstep
  by (cases sc) force

lemma aaopstep_to_aopstep:
  assumes \<open>sc \<midarrow>\<eta>\<rightarrow>\<^sub>a\<^sub>a sc'\<close>
  shows \<open>sc \<midarrow>(eact_to_plabel \<eta>, eact_to_act \<eta>)\<rightarrow>\<^sub>a sc'\<close>
  using assms
proof -
  {
    fix s c
    assume \<open>(s, c) \<midarrow>\<eta>\<rightarrow>\<^sub>a\<^sub>a sc'\<close>
    then have \<open>(s, c) \<midarrow>(eact_to_plabel \<eta>, eact_to_act \<eta>)\<rightarrow>\<^sub>a sc'\<close>
    proof (induct c arbitrary: \<eta> sc')
      case (Endet c1 c2)
      then show ?case
        apply (clarsimp simp add: eact_to_act_def)
        apply (case_tac \<open>eact_leaf \<eta>\<close>) (* +1 *)
         apply (clarsimp split: if_splits)
         apply (cases \<eta>; clarsimp) (* +2 *)
           apply presburger
          apply fastforce
         apply fastforce
        apply (clarsimp, fastforce)
        done
    next
      case (Iter c)
      then show ?case
        by (force simp add: no_aopstep_iff_no_aaopstep)
    qed fastforce+
  }
  then show ?thesis
    using assms
    by (cases sc) force
qed

lemma aopstep_to_aaopstep:
  assumes \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c')\<close>
  shows \<open>\<exists>\<eta>. \<pi>\<alpha> = (eact_to_plabel \<eta>, eact_to_act \<eta>) \<and> (s, c) \<midarrow>\<eta>\<rightarrow>\<^sub>a\<^sub>a (s', c')\<close>
  using assms
proof (induct c arbitrary: \<pi>\<alpha> c')
  case (Par c1 c2)
  then show ?case
    apply (clarsimp simp add: split_pairs2)
    apply (case_tac \<open>fst \<pi>\<alpha>\<close>)
      apply clarsimp
      apply (metis eact_to_act_simps(3) eact_to_plabel.simps(3))
     apply clarsimp
     apply (metis eact_to_act_simps(4) eact_to_plabel.simps(4))
    apply force
    done
next
  case (Indet c1 c2)
  then show ?case
    apply clarsimp
    apply (metis eact_to_act_simps(5) eact_to_plabel.simps(5))
    done
next
  case (Endet c1 c2)
  show ?case
    using Endet.prems
    apply (case_tac \<open>snd \<pi>\<alpha>\<close>)
     apply clarsimp
     apply (elim disjE; clarsimp) (* +3 *)
        apply force
       apply force
      apply (frule Endet.hyps(1))
      apply (metis act.simps(2) eact_leaf.simps(1) eact_to_act_def eact_to_plabel.simps(1)
        option.distinct(1) snd_conv)
     apply (frule Endet.hyps(2))
     apply (metis act.simps(2) eact_leaf.simps(2) eact_to_act_def eact_to_plabel.simps(2)
        option.distinct(1) snd_conv)
    apply (clarsimp simp add: split_pairs2)
    apply (elim disjE)
     apply (frule Endet.hyps(1))
     apply clarsimp
     apply (metis act.simps(2) eact_leaf.simps(1) eact_to_act_def eact_to_plabel.simps(1))
    apply (frule Endet.hyps(2))
    apply clarsimp
    apply (metis act.simps(2) eact_leaf.simps(2) eact_to_act_def eact_to_plabel.simps(2))
    done
next
  case (Iter c)
  then show ?case
    apply clarsimp
    apply (elim disjE)
     apply clarsimp
     apply (metis no_opstep_iff_no_aaopstep no_opstep_iff_no_aopstep)
    apply (metis Iter.hyps)
    done
qed fastforce+


lemma aopstep_iff_aaopstep:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<longleftrightarrow>
    (\<exists>\<eta>. \<pi>\<alpha> = (eact_to_plabel \<eta>, eact_to_act \<eta>) \<and> sc \<midarrow>\<eta>\<rightarrow>\<^sub>a\<^sub>a sc')\<close>
  by (metis aaopstep_to_aopstep aopstep_to_aaopstep surj_pair)


(*
definition \<open>diag_pre_state a \<equiv> (\<lambda>s. \<exists>s'. a (\<Delta> s) (\<Delta> s'))\<close>

abbreviation \<open>any_head_guard_diag \<equiv> any_head_atom diag_pre_state\<close>


fun branch_determ2 :: \<open>('s \<times> 's) comm \<Rightarrow> 's \<times> 's \<Rightarrow> bool\<close> where
  \<open>branch_determ2 (ca \<^bold>\<box> cb) = (
    (\<lambda>_. head_atomic ca) \<sqinter>
    (\<lambda>_. head_atomic cb) \<sqinter>
    - \<lblot> any_head_guard_diag ca \<bar> any_head_guard_diag cb \<rblot> \<sqinter>
    - \<lblot> any_head_guard_diag cb \<bar> any_head_guard_diag ca \<rblot>)\<close>
| \<open>branch_determ2 (DO c OD) =
    (stable_comm c \<sqinter> \<bbbA> (any_head_guard_diag c))\<close>
| \<open>branch_determ2 (ca \<^bold>\<sqinter> cb) = (\<lambda>_. False)\<close>
| \<open>branch_determ2 c = (\<lambda>_. True)\<close>

definition branch_determ2_exch4
  :: \<open>(('a \<times> 'a) \<times> ('b \<times> 'b)) comm \<Rightarrow> (('a \<times> 'a) \<times> ('b \<times> 'b)) \<Rightarrow> bool\<close>
  (\<open>branch'_determ2\<^sub>\<ddagger>\<close>)
  where
    \<open>branch_determ2\<^sub>\<ddagger> c \<equiv> branch_determ2 (map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) \<circ> \<ddagger>\<close>

lemmas branch_determ2_exch4_apply =
  branch_determ2_exch4_def[THEN meta_eq_to_obj_eq, THEN fun_cong, simplified]
*)

lemma head_atoms_map_atom_eq:
  \<open>head_atoms (map_atom f c) = image_mset f (head_atoms c)\<close>
  by (induct c) force+

lemma bij_fun_then_any_head_guard_of_map_atom_eq:
  \<open>bij f \<Longrightarrow>
    any_head_guard (map_atom (\<lambda>a. a \<circ>\<^sub>2 f) c) = any_head_guard c \<circ> f\<close>
  apply (simp add: any_head_atom_def head_atoms_map_atom_eq image_comp del: comp_apply)
  apply (rule fun_cong[of \<open>\<lambda>A. \<Squnion> (_ ` A)\<close> \<open>\<lambda>A. \<Squnion> (_ ` A) \<circ> f\<close>])
  apply (clarsimp simp add: fun_eq_iff pre_state_def Sup_fun_def Bex_def)
  apply (metis bij_iff comp2_apply)
  done


lemma head_atomic_of_map_atom_iff:
  \<open>bij f \<Longrightarrow> head_atomic (map_atom (\<lambda>a. a \<circ>\<^sub>2 f) c) \<longleftrightarrow> head_atomic c\<close>
  apply (induct c)
        apply (clarsimp simp add: map_atom_rev_iff)+
  apply (simp add: bij_fun_then_any_head_guard_of_map_atom_eq)
  apply (metis bij_iff comp_apply)
  done


lemma aopstep_diagstep_replacement_left:
  assumes
    \<open>all_atoms (\<lambda>a. diagstep_replace (a \<circ>\<^sub>2 \<ddagger>) \<circ> \<ddagger>) c (\<ddagger> (sx, sy))\<close>
    \<open>all_head_subcomms branch_determ\<^sub>\<ddagger> c (\<ddagger> (sx, sy))\<close>
    \<open>(\<ddagger> (sx, sy), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (\<ddagger> (sx', sy'), c')\<close>
    \<open>(\<ddagger> (\<Delta> sx), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (\<ddagger> (\<Delta> sx''), c')\<close>
  shows
    \<open>(\<ddagger> (sx, sy), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (\<ddagger> (sx'', sy'), c')\<close>
  using assms
  thm same_initcomm_and_plabel_then_same_eact_and_fincomm
  apply (clarsimp simp add: aopstep_iff_aaopstep)
  apply (frule(1) same_initcomm_and_plabel_then_same_eact_and_fincomm[
        of _ \<open>\<ddagger> (sx, sy)\<close> _ _ _ _ \<open>\<ddagger> (sx, sx)\<close>])
  sorry


theorem security_implies_noninterference_bisim:
  fixes n :: nat
    and c :: \<open>('l::pre_perm_alg, 's) rgstate comm\<close>
    and s :: \<open>('l, 's) rgstate\<close>
    and F I q :: \<open>('l, 's) rgstate \<Rightarrow> bool\<close>
    and R G :: \<open>'s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool\<close>
  assumes \<open>secure R F G I q n c s\<close>
    and \<open>s = (ls, ss)\<close>
    and \<open>wssa (R \<squnion> G) F (fs, ss)\<close>
    and \<open>ls ## fs\<close>
    and \<open>I \<^emph>\<and> F \<le> all_atoms (\<lambda>a. diagstep_replace (a \<circ>\<^sub>2 \<ddagger>) \<circ> \<ddagger>) c\<close>
  shows \<open>noninterference_bisim
          (((=) \<times>\<^sub>R R) \<circ>\<^sub>2 \<ddagger>) (((=) \<times>\<^sub>R G) \<circ>\<^sub>2 \<ddagger>) ((I \<^emph>\<and> F) \<circ> \<ddagger>) n (map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) (\<ddagger> (ls + fs, ss))\<close>
  using assms
proof (induct arbitrary: ls ss rule: secure.inducts)
  case (secureI s lsz ssz c n)

  have sz_eq: \<open>lsz = ls\<close> \<open>ssz = ss\<close>
    using secureI.prems(1) secureI.hyps(1)
    by fastforce+

  have inv_lemmas: \<open>I (ls, ss)\<close> \<open>F (fs, ss)\<close> \<open>ls ## fs\<close>
    using secureI.prems(1-3) secureI.hyps(1-3)
    by (fastforce simp add: sepconj_conj_def)+

  show ?case
  proof (intro noninterference_bisimI[of _ _ n])
    show \<open>(I \<^emph>\<and> F \<circ> \<ddagger>) (\<ddagger> (ls + fs, ss))\<close>
      using inv_lemmas
      by (fastforce simp add: sepconj_conj_def)
  next
    fix n' s'
    assume assms2:
      \<open>n = Suc n'\<close>
      \<open>((=) \<times>\<^sub>R R \<circ>\<^sub>2 \<ddagger>) (\<ddagger> (ls + fs, ss)) s'\<close>
    
    have \<open>fst (\<ddagger> s') = ls + fs \<and> R ss (snd (\<ddagger> s'))\<close>
      using assms2(2)
      by (simp add: rel_times_apply)
    moreover then have \<open>s' = ((fst ls + fst fs, snd (fst s')), snd ls + snd fs, snd (snd s'))\<close>
      by (metis fst_add snd_add prod.exhaust_sel prod_destruct_exch4_eq(1,3))
    ultimately show
      \<open>noninterference_bisim ((=) \<times>\<^sub>R R \<circ>\<^sub>2 \<ddagger>) ((=) \<times>\<^sub>R G \<circ>\<^sub>2 \<ddagger>) (I \<^emph>\<and> F \<circ> \<ddagger>)
        n' (map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) s'\<close>
      using secureI.prems secureI.hyps(1-3) assms2(1)
      apply (clarsimp simp del: sup_apply)
      apply (frule secureI.hyps(5))
           apply force
          apply force
         apply (metis sup2I1 wssa_stepD)
        apply force
       apply (simp; fail)
      apply (simp add: exch4_two_apply split_pairs del: comp2_apply comp_apply)
      done
  next
    fix n' sx sy \<pi>
    assume assms2:
      \<open>n = Suc n'\<close>
      \<open>\<exists>\<alpha>. Ex (pretty_aopstep (\<ddagger> (ls + fs, ss), map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) (\<pi>, \<alpha>))\<close>
      \<open>\<ddagger> (ls + fs, ss) = (sx, sy)\<close>

    obtain \<alpha> sx' sy' cd' where some_step:
      \<open>((sx, sy), map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a ((sx', sy'), cd')\<close>
      using assms2(2-3)
      by force
    moreover then obtain c' where cd'_def: \<open>cd' = map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>)  c'\<close>
      by (force dest: aopstep_preserves_map_atom)
    ultimately have c_aopstep:
      \<open>(\<ddagger> (sx, sy), c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a (\<ddagger> (sx', sy'), c')\<close>
      by (force dest: aopstep_then_map_aopstep_then_aopstep simp add: inj_def)

    have c_opstep:
      \<open>((ls + fs, ss), c) \<midarrow>\<alpha>\<rightarrow> (\<ddagger> (sx', sy'), c')\<close>
      by (metis aopstep_then_opstep assms2(3) c_aopstep exch4_idem snd_conv)

    have tau_step_no_change:
      \<open>\<alpha> = Tau \<longrightarrow> ss = (snd sx', snd sy')\<close>
      sorry

    have diagstep_step: \<open>I \<^emph>\<and> F \<le> all_atoms (\<lambda>a. diagstep_replace (a \<circ>\<^sub>2 \<ddagger>) \<circ> \<ddagger>) c'\<close>
      using aopstep_preserves_all_atoms c_aopstep secureI.prems(4)
      by fastforce

    have security_properties:
      \<open>\<forall>\<pi>\<alpha> c' ax' ay'.
        (\<ddagger> (sx, sy), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (\<ddagger> (ax', ay'), c') \<longrightarrow>
          (\<ddagger> (sx, sx), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (\<ddagger> (ax', ax'), c') \<and>
          (\<ddagger> (sy, sy), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (\<ddagger> (ay', ay'), c')\<close>
      \<open>\<forall>\<pi>\<alpha> ax' ay' cx' cy'.
        (sx, unliftC c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (ax', cx') \<longrightarrow>
        (sy, unliftC c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (ay', cy') \<longrightarrow> cx' = cy'\<close>
      using secureI.prems secureI.hyps(1) assms2 secureI(7)
      by blast+

    {
      fix \<alpha> sx'' cx''
      assume \<open>((sx, sx), map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a ((sx'', sx''), cx'')\<close>
      then have \<open>(\<ddagger> (sx, sx), c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a (\<ddagger> (sx'', sx''), c')\<close>
        sorry

      have joint_aopstep: \<open>(\<ddagger> (sx, sy), c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a (\<ddagger> (sx', sy'), c')\<close>
        sorry
      then obtain lfs' ss' where joint_opstep:
        \<open>((ls + fs, ss), c) \<midarrow>\<alpha>\<rightarrow> ((lfs', ss'), c')\<close>
        \<open>\<ddagger> (sx', sy') = (lfs', ss')\<close>
        by (metis aopstep_then_opstep assms2(3) exch4_switch split_pairs2)

      note ih =
        secureI.hyps(6)[simplified sz_eq,
          OF assms2(1) inv_lemmas(2) inv_lemmas(3) joint_opstep]
    thm c_opstep[simplified exch4_two_apply]
    have ih_G: \<open>\<alpha> \<noteq> Tau \<longrightarrow> G ss (snd sx', snd sy')\<close>
      using ih by force
    have RG_frame: \<open>wssa (R \<squnion> G) F (fs, (snd sx', snd sy'))\<close>
      using secureI.prems(2) ih_G tau_step_no_change
      by (metis sup2I2 wssa_step)

      
      
      have \<open>(\<ddagger> (sy, sy), c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a (\<ddagger> (sy', sy'), c')\<close>
        sorry
      then have \<open>((sy, sy), map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a ((sy', sy'), cx')\<close>
        sorry
    } note xstep_to_ystep = this

    {
      fix \<alpha> sy' cy'
      assume \<open>((sy, sy), map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a ((sy', sy'), cy')\<close>
      then have \<open>(\<ddagger> (sy, sy), c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a (\<ddagger> (sy', sy'), c')\<close>
        sorry
      then have \<open>(\<ddagger> (sx, sx), c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a (\<ddagger> (sx', sx'), c')\<close>
        sorry
      have \<open>((sx, sx), map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a ((sx', sx'), cy')\<close>
        sorry
    } note ystep_to_xstep = this
    
    show \<open>
      (\<forall>\<alpha> sx' c'.
           ((sx, sx), map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a ((sx', sx'), c') \<longrightarrow>
           (\<exists>sy'. ((sy, sy), map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a ((sy', sy'), c') \<and>
                  noninterference_bisim ((=) \<times>\<^sub>R R \<circ>\<^sub>2 \<ddagger>) ((=) \<times>\<^sub>R G \<circ>\<^sub>2 \<ddagger>) (I \<^emph>\<and> F \<circ> \<ddagger>) n' c' (sx', sy'))) \<and>
       (\<forall>\<alpha> sy' c'.
           ((sy, sy), map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a ((sy', sy'), c') \<longrightarrow>
           (\<exists>sx'. ((sx, sx), map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) \<midarrow>(\<pi>, \<alpha>)\<rightarrow>\<^sub>a ((sx', sx'), c') \<and>
                  noninterference_bisim ((=) \<times>\<^sub>R R \<circ>\<^sub>2 \<ddagger>) ((=) \<times>\<^sub>R G \<circ>\<^sub>2 \<ddagger>) (I \<^emph>\<and> F \<circ> \<ddagger>) n' c' (sx', sy')))\<close>
      using ih_noninterference
      apply (intro conjI allI impI)
       apply (frule xstep_to_ystep)
       apply (rule exI, rule conjI, blast)
      subgoal sorry
      apply (frule ystep_to_xstep)
      apply (rule exI, rule conjI, blast)
      sorry
qed

section \<open> Security Theory 1 \<close>


lemma
  \<open>pa \<sqinter> pb = \<bottom> \<Longrightarrow>
    - \<lblot> pa \<bar> pb \<rblot> \<sqinter> - \<lblot> pb \<bar> pa \<rblot> \<le> \<bbbA> pa \<sqinter> \<bbbA> pb\<close>
  apply (simp add: sec_agree_def le_fun_def fun_eq_iff)
  nitpick[card 'a=2]
  oops


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
  \<open>nonfail_predrel_ff r \<equiv>
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
  \<open>purely_relational3 ar \<equiv> ar \<sqinter> (predrel (case_prod (=)) \<top> \<circ>\<^sub>2 exch4) \<le> (=)\<close>


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
      (rel_image snd (pretest (sswa R p \<^emph>\<and> F) \<sqinter> ar)) \<comment> \<open> G \<close>
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
    apply (clarsimp simp del: sup_apply inf_apply top_apply predrel_apply rel_image_apply)
    apply (rule safeI)
      (* subgoal: termination *)
       apply force
      (* subgoal: state inv *)
      apply force
      (* subgoal: rely *)
     apply (clarsimp simp del: sup_apply inf_apply predrel_apply top_apply rel_image_apply)
     apply (simp add: ih wssa_step; fail)
      (* subgoal: local framed opstep *)
    apply (rule conjI)
      (* subsubgoal: guarantee *)
     apply clarsimp
     apply (meson rely_rel_wlp_impl_sp sepconj_conjI; fail)
      (* subsubgoal: safety after opstep *)
    apply (clarsimp simp del: sup_apply inf_apply top_apply predrel_apply
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
