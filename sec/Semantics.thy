theory Semantics
  imports "../Soundness"
begin

lemma eqrel_times_eqrel_eq[simp]:
  \<open>((=) \<times>\<^sub>R (=)) = (=)\<close>
  by (force simp add: rel_Times_def)

type_synonym ('a,'b) rgstate = \<open>(('a \<times> 'a) \<times> ('b \<times> 'b))\<close>

type_synonym ('a,'b) secstate = \<open>(('a \<times> 'b) \<times> ('a \<times> 'b))\<close>

section \<open> Double-state lifting \<close>

subsection \<open> relational lifting \<close>

definition
  \<open>exch4 \<equiv> \<lambda>((a,b),(c,d)). ((a,c),(b,d))\<close>

lemma exch4_apply[simp]:
  \<open>exch4 ((a,b),(c,d)) = ((a,c),(b,d))\<close>
  by (simp add: exch4_def)

lemma exch4_idem[simp]:
  \<open>exch4 (exch4 x) = x\<close>
  by (simp add: exch4_def split: prod.splits)

lemma comp_exch4_eq_iff[simp]:
  \<open>f \<circ> exch4 = g \<circ> exch4 \<longleftrightarrow> f = g\<close>
  by (simp add: fun_eq_iff, blast)


definition twoPredLift :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> where
  \<open>twoPredLift p q \<equiv> \<lambda>(x,y). p x \<and> q y\<close>

nonterminal twoPredLiftL

syntax
  "_twoPredLiftS"  :: "('a \<Rightarrow> bool) \<Rightarrow> twoPredLiftL"  ("\<lblot> _" [0] 1000)
  "_twoPredLiftC"  :: "twoPredLiftL \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"  ("_ \<rblot>" [0] 1000)
  "_twoPredLiftL"  :: "twoPredLiftL \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("_ \<bar>" [0] 1000)
  "_twoPredLiftLR"  :: "twoPredLiftL \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("_ \<bar> _ \<rblot>" [0] 1000)
  "_twoPredLiftR"  :: "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<bar> _ \<rblot>" [0] 1000)

translations
  "_twoPredLiftC (_twoPredLiftS p)" \<rightharpoonup> "(CONST twoPredLift) p p"
  "_twoPredLiftLR (_twoPredLiftS p) q" \<rightleftharpoons> "(CONST twoPredLift) p q"
  "_twoPredLiftL (_twoPredLiftS p)" \<rightharpoonup> "(CONST twoPredLift) p \<top>"
  "_twoPredLiftR q" \<rightharpoonup> "(CONST twoPredLift) \<top> q"

lemma twoPredLift_apply[simp]:
  \<open>twoPredLift p q (x, y) \<longleftrightarrow> p x \<and> q y\<close>
  by (simp add: twoPredLift_def)

lemma twoPredLiftI[intro]:
  \<open>p x \<Longrightarrow> q y \<Longrightarrow> twoPredLift p q (x, y)\<close>
  by (simp add: twoPredLift_def)

subsection \<open> Agreement \<close>

definition sec_agree
  :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool\<close> (\<open>\<bbbA>\<close>)
  where
    \<open>\<bbbA> vf \<equiv> (\<lambda>(x,y). vf x = vf y)\<close>

lemma conj_agree_iff:
  \<open>\<bbbA> v1 \<sqinter> \<bbbA> v2 = \<bbbA> (\<lambda>x. (v1 x, v2 x))\<close>
  by (simp add: sec_agree_def exch4_def comp_def fun_eq_iff split: prod.splits)

subsection \<open> Double-state Lifting \<close>

abbreviation(input) \<open>liftP p \<equiv> \<lblot> p \<rblot>\<close>
definition \<open>liftR r \<equiv> \<lambda>(x,x') (y,y'). r x y \<and> r x' y'\<close>
definition \<open>liftC f \<equiv> map_comm (\<lambda>p q. ((liftP p \<sqinter> \<bbbA> f) \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close>

lemmas liftC_simps[simp] =
  map_comm.simps[of \<open>(\<lambda>p q. ((liftP p \<sqinter> \<bbbA> f) \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close> for f,
    simplified liftC_def[symmetric]]

lemmas liftC_rev_iff =
  map_comm_rev_iff[of \<open>(\<lambda>p q. ((liftP p \<sqinter> \<bbbA> f) \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close> for f,
    simplified liftC_def[symmetric]]

lemma liftC_cancel[simp]:
  \<open>liftC \<oo> ca = liftC \<oo> cb \<longleftrightarrow> ca = cb\<close>
  apply (induct cb arbitrary: ca)
        apply (metis liftC_rev_iff(1))
       apply (metis liftC_rev_iff(2))
      apply (metis liftC_rev_iff(3))
     apply (metis liftC_rev_iff(4))
    apply (metis liftC_rev_iff(5))
   apply (fastforce simp add: liftC_rev_iff fun_eq_iff sec_agree_def liftR_def)
  apply (metis liftC_rev_iff(6))
  done


definition \<open>unliftC \<equiv> map_comm (\<lambda>p q. (\<lambda>x. p (exch4 (x,x)), \<lambda>x y. q (exch4 (x,x)) (exch4 (y,y))))\<close>

lemma unlift_lift_cancel[simp]:
  \<open>unliftC (liftC f c) = c\<close>
  unfolding unliftC_def liftC_def
  by (induct c) (simp add: liftR_def sec_agree_def)+


definition \<open>liftC' \<equiv> map_comm (\<lambda>p q. (liftP p \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close>

lemmas liftC'_simps[simp] =
  map_comm.simps[of \<open>(\<lambda>p q. (liftP p \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close> for f,
    simplified liftC'_def[symmetric]]

lemmas liftC'_rev_iff =
  map_comm_rev_iff[of \<open>(\<lambda>p q. (liftP p \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close> for f,
    simplified liftC'_def[symmetric]]

lemma liftC'_cancel[simp]:
  \<open>liftC' ca = liftC' cb \<longleftrightarrow> ca = cb\<close>
  apply (induct cb arbitrary: ca)
        apply (metis liftC'_rev_iff(1))
       apply (metis liftC'_rev_iff(2))
      apply (metis liftC'_rev_iff(3))
     apply (metis liftC'_rev_iff(4))
    apply (metis liftC'_rev_iff(5))
   apply (fastforce simp add: liftC'_rev_iff fun_eq_iff sec_agree_def liftR_def)
  apply (metis liftC'_rev_iff(6))
  done

lemma unlift_lift'_cancel[simp]:
  \<open>unliftC (liftC' c) = c\<close>
  unfolding unliftC_def liftC'_def
  by (induct c) (simp add: liftR_def sec_agree_def)+


section \<open> Tree Noninterference \<close>

section \<open> Safe \<close>

inductive tree_weak_noninterference
  :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l::pre_perm_alg \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> 'v) \<Rightarrow>
      nat \<Rightarrow>
      ('l \<times> 's) comm \<Rightarrow>
      ('l \<times> 'l) \<times> ('s \<times> 's) + unit \<Rightarrow>
      bool\<close>
  where
  tree_weak_noninterference_nil[intro!]: \<open>tree_weak_noninterference r F \<oo> 0 c (Inl s)\<close>
| tree_weak_noninterference_suc[intro]:
  \<open>\<bbbA> \<oo> (exch4 (hl, hs)) \<Longrightarrow>
    \<comment> \<open> closed under rely steps \<close>
    (\<And>hs'. r hs hs' \<Longrightarrow> tree_weak_noninterference r F \<oo> n c (Inl (hl, hs'))) \<Longrightarrow>
    \<comment> \<open> closed under opsteps \<close>
    (\<And>\<alpha> c' hl' hs'.
        ((hl,hs), liftC' c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl',hs'), c') \<Longrightarrow>
        tree_weak_noninterference r F \<oo> n (unliftC c') (Inl (hl', hs'))) \<Longrightarrow>
    \<comment> \<open> closed under framed opsteps \<close>
    (\<And>\<alpha> c' hlf hlhlf' hs'.
        hl ## hlf \<Longrightarrow>
        ((hl + hlf, hs), liftC' c) \<midarrow>\<alpha>\<rightarrow> (Inl (hlhlf', hs'), c') \<Longrightarrow>
        F (hlf, hs) \<Longrightarrow>
        (\<exists>hl'.
          hl' ## hlf \<and>
          hlhlf' = hl' + hlf \<and>
          (\<alpha> = Tau \<longrightarrow> hl' = hl) \<and>
          tree_weak_noninterference r F \<oo> n (unliftC c') (Inl (hl', hs')))) \<Longrightarrow>
    tree_weak_noninterference r F \<oo> (Suc n) c (Inl (hl, hs))\<close>

definition quasirefl_cl (\<open>\<^bold>\<box>\<close>) where
  \<open>quasirefl_cl p \<equiv> \<lambda>(x,y). p (x,y) \<and> p (x,x) \<and> p (y,y)\<close>

lemma quasirefl_cl_mono:
  \<open>p \<le> q \<Longrightarrow> \<^bold>\<box>p \<le> \<^bold>\<box>q\<close>
  unfolding quasirefl_cl_def
  by blast

lemma
  \<open>\<^bold>\<box>p = p \<longleftrightarrow> (\<forall>x y. p (x,y) \<longrightarrow> p (x,x) \<and> p (y,y))\<close>
  unfolding quasirefl_cl_def
  by (force simp add: fun_eq_iff)


subsection \<open> Proofs about safe \<close>

inductive_cases tree_weak_noninterference_zeroE[elim!]: \<open>tree_weak_noninterference r F \<oo> 0 c s\<close>
inductive_cases tree_weak_noninterference_sucE[elim]: \<open>tree_weak_noninterference r F \<oo> (Suc n) c s\<close>

lemma safe_nil_iff[simp]:
  \<open>tree_weak_noninterference r F \<oo> 0 c s \<longleftrightarrow> (\<exists>hl hs. s = Inl (hl, hs))\<close>
  by force

lemma tree_weak_noninterference_suc_iff:
  \<open>tree_weak_noninterference r F \<oo> (Suc n) c (Inl (hl, hs)) \<longleftrightarrow>
    \<bbbA> \<oo> (exch4 (hl, hs)) \<and>
    (\<forall>hs'. r hs hs' \<longrightarrow> tree_weak_noninterference r F \<oo> n c (Inl (hl, hs'))) \<and>
    (\<forall>\<alpha> c' hl' hs'.
        ((hl,hs), liftC' c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl',hs'), c') \<longrightarrow>
        tree_weak_noninterference r F \<oo> n (unliftC c') (Inl (hl',hs'))) \<and>
    (\<forall>\<alpha> c' hlf hlhlf' hs'.
        hl ## hlf \<longrightarrow>
        ((hl + hlf,hs), liftC' c) \<midarrow>\<alpha>\<rightarrow> (Inl (hlhlf',hs'), c') \<longrightarrow>
        F (hlf, hs) \<longrightarrow>
        (\<exists>hl'.
          hl' ## hlf \<and>
          hlhlf' = hl' + hlf \<and>
          (\<alpha> = Tau \<longrightarrow> hl' = hl) \<and>
          tree_weak_noninterference r F \<oo> n (unliftC c') (Inl (hl',hs'))))\<close>
  apply (rule iffI)
   apply (erule tree_weak_noninterference_sucE, force)
  apply (rule tree_weak_noninterference_suc; presburger)
  done

lemma safe_sucD:
  \<open>tree_weak_noninterference r F \<oo> (Suc n) c (Inl (hl, hs)) \<Longrightarrow> \<bbbA> \<oo> (exch4 (hl, hs))\<close>
  \<open>tree_weak_noninterference r F \<oo> (Suc n) c (Inl (hl, hs)) \<Longrightarrow>
    r hs hs' \<Longrightarrow> tree_weak_noninterference r F \<oo> n c (Inl (hl, hs'))\<close>
  \<open>tree_weak_noninterference r F \<oo> (Suc n) c (Inl (hl, hs)) \<Longrightarrow>
    ((hl,hs), liftC' c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl',hs'), c') \<Longrightarrow>
    tree_weak_noninterference r F \<oo> n (unliftC c') (Inl (hl', hs'))\<close>
  \<open>tree_weak_noninterference r F \<oo> (Suc n) c (Inl (hl, hs)) \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    ((hl + hlf,hs), liftC' c) \<midarrow>\<alpha>\<rightarrow> (Inl (hlhlf',hs'), c') \<Longrightarrow>
    F (hlf, hs) \<Longrightarrow>
    (\<exists>hl'.
      hl' ## hlf \<and>
      hlhlf' = hl' + hlf \<and>
      (\<alpha> = Tau \<longrightarrow> hl' = hl) \<and>
      tree_weak_noninterference r F \<oo> n (unliftC c') (Inl (hl', hs')))\<close>
  by (erule tree_weak_noninterference_sucE, (simp; blast))+

lemma opstep_preserves_liftC':
  \<open>(s, liftC' c) \<midarrow>\<alpha>\<rightarrow> (z', cx') \<Longrightarrow> \<exists>c'. cx' = liftC' c'\<close>
proof (induct c arbitrary: s z' cx' \<alpha>)
  case Skip
  then show ?case by force
next
  case (Seq c1 c2)
  then show ?case
    by (simp, metis liftC'_simps(2))
next
  case (Par c1 c2)
  then show ?case
    by (simp, metis liftC'_simps(3))
next
  case (Indet c1 c2)
  then show ?case
    by force
next
  case (Endet c1 c2)
  then show ?case
    using Endet.prems
    by (simp, metis Endet.hyps(2) liftC'_simps(5))
next
  case (Atomic x1 x2)
  then show ?case
    apply (clarsimp split: if_splits)
     apply (metis liftC'_simps(1))
    apply (metis liftC'_rev_iff(7))
    done
next
  case (Iter c)
  then show ?case
    by (clarsimp split: if_splits, metis liftC'_simps(1), metis liftC'_simps(2,7))
qed

lemma opstep_preserves_liftC:
  \<open>(s, liftC \<oo> c) \<midarrow>\<alpha>\<rightarrow> (z', lc') \<Longrightarrow> \<exists>c'. lc' = liftC \<oo> c'\<close>
proof (induct c arbitrary: s \<alpha> z' lc')
  case Skip
  then show ?case
    by simp
next
  case (Seq c1 c2)
  then show ?case
    by (simp, metis liftC_simps(2))
next
  case (Par c1 c2)
  then show ?case
    by (simp, metis liftC_simps(3))
next
  case (Indet c1 c2)
  then show ?case
    by (simp, metis)
next
  case (Endet c1 c2)
  then show ?case
    by (simp, metis liftC_simps(5))
next
  case (Atomic x1 x2)
  then show ?case
    apply (clarsimp split: if_splits)
     apply (metis liftC_simps(1))
    apply (metis liftC_rev_iff(7))
    done
next
  case (Iter c)
  then show ?case
    by (simp split: if_splits, metis liftC_simps(1), metis liftC_simps(2,7))
qed

lemma opstep_prestate_liftC'_iff_liftC:
  \<open>\<bbbA> \<oo> (exch4 s) \<Longrightarrow>
    (s, liftC' c) \<midarrow>\<alpha>\<rightarrow> (z', liftC' c') \<longleftrightarrow>
      (s, liftC \<oo> c) \<midarrow>\<alpha>\<rightarrow> (z', liftC \<oo> c')\<close>
proof (induct c arbitrary: s z' \<alpha> c')
  case Skip then show ?case
    by force
next
  case (Seq c1 c2)
  show ?case
    using Seq.prems
    apply (clarsimp simp add: liftC_rev_iff liftC'_rev_iff)
    apply (metis Seq.hyps(1))
    done
next
  case (Par c1 c2)
  show ?case
    using Par.prems
    apply (clarsimp simp add: liftC_rev_iff liftC'_rev_iff)
    apply (metis Par.hyps)
    done
next
  case (Indet c1 c2)
  show ?case
    using Indet.prems
    by (clarsimp simp add: liftC_rev_iff liftC'_rev_iff)
next
  case (Endet c1 c2)
  show ?case
    using Endet.prems
    apply (clarsimp simp add: liftC_rev_iff liftC'_rev_iff)
    apply (metis Endet.hyps(1-2))
    done
next
  case (Atomic x1 x2)
  show ?case 
    using Atomic.prems
    apply (clarsimp simp add: liftC_rev_iff liftC'_rev_iff split: if_splits)
    apply (rule iffI)
     apply clarsimp
    apply clarsimp
    apply (clarsimp simp add: sec_agree_def fun_eq_iff split: prod.splits)
    apply blast
    done
next
  case (Iter c)
  show ?case
    using Iter.prems
    apply (clarsimp simp add: liftC_rev_iff liftC'_rev_iff split: if_splits)
    apply (intro conjI allI impI)
      apply clarsimp
      apply (metis Iter.hyps opstep_preserves_liftC)
     apply clarsimp
     apply (metis Iter.hyps opstep_preserves_liftC')
    apply clarsimp
    apply (metis liftC'_cancel liftC'_simps(7) liftC_cancel liftC_simps(7))
    done
qed

theorem weak_noninterference:
  \<open>safe n cc z r g q S F \<Longrightarrow>
    cc = liftC' c \<Longrightarrow>
    z = Inl s \<Longrightarrow>
    S \<le> \<bbbA> \<oo> \<circ> exch4 \<Longrightarrow>
    S \<^emph>\<and> F \<le> \<bbbA> \<oo> \<circ> exch4 \<Longrightarrow>
    tree_weak_noninterference r F \<oo> n c z\<close>
  apply (induct arbitrary: c s rule: safe.inducts)
   apply force
  apply (clarsimp simp add: liftC_rev_iff tree_weak_noninterference_suc_iff)
  apply (rename_tac c hla hlb hsa hsb)
  apply (intro conjI)
    apply (force simp add: le_fun_def)
   apply clarsimp
   apply (frule opstep_preserves_liftC')
   apply (metis unlift_lift'_cancel)
  apply clarsimp
  apply (frule opstep_preserves_liftC')
  apply clarsimp
  apply (drule meta_spec2, drule meta_spec2, drule meta_spec,
      drule meta_mp, rule conjI, assumption, assumption , drule meta_mp, assumption)
  apply blast
  done


(*
    (\<forall>c1 c2. c = c1 \<box> c2 \<or> c = c1 \<^bold>+ c2 \<longrightarrow>
      (\<exists>p1 q1 p2 q2.
        (\<exists>c1'. c1 = \<langle> p1, q1 \<rangle> ;; c1') \<and>
        (\<exists>c2'. c2 = \<langle> p2, q2 \<rangle> ;; c2') \<and>
        (\<forall>x y. exch4 (hl, hs) = (x, y) \<longrightarrow>
          \<not> (p1 \<sqinter> pre_state q1 \<sqinter> p2 \<sqinter> pre_state q2) x \<and>
          \<not> (p1 \<sqinter> pre_state q1 \<sqinter> p2 \<sqinter> pre_state q2) y))) \<and>
*)

section \<open> Aligned Traces \<close>

subsection \<open> Extended Opstep \<close>

text \<open> Extended Actions \<close>

datatype ctrl_act =
  INDetL
  | INDetR
  | ENDetL
  | ENDetR
  \<comment> \<open>
    NOTE: we don't observe the scheduling of parallel, because it acts directly on the parts,
    rather than performing a control move before actually doing the step.
    One way to change this would be to add a "current process" state, and a switching action.
    FIXME: the fact we have chosen a double skip exit, rather than a one-sided skip exit, might
    have implications on the observables.
  \<close>
  | ParExit
  | DoLoop
  | DoExit
  | Misc

datatype ('a, 'b) eact = Ctrl 'a | Vis 'b

abbreviation \<open>CtrlINDetL \<equiv> Ctrl INDetL\<close>
abbreviation \<open>CtrlINDetR \<equiv> Ctrl INDetR\<close>
abbreviation \<open>CtrlENDetL \<equiv> Ctrl ENDetL\<close>
abbreviation \<open>CtrlENDetR \<equiv> Ctrl ENDetR\<close>
abbreviation \<open>CtrlParExit \<equiv> Ctrl ParExit\<close>
abbreviation \<open>CtrlDoLoop \<equiv> Ctrl DoLoop\<close>
abbreviation \<open>CtrlDoExit \<equiv> Ctrl DoExit\<close>
abbreviation \<open>CtrlMisc \<equiv> Ctrl Misc\<close>


paragraph \<open> Extended Opstep \<close>

fun eopstep :: \<open>(ctrl_act, unit) eact \<Rightarrow> ('s, unit) pconfig \<Rightarrow> ('s, unit) cpconfig \<Rightarrow> bool\<close> where
  \<open>eopstep \<alpha> (h, Skip) s' \<longleftrightarrow> False\<close>
| \<open>eopstep \<alpha> (h, c1 ;; c2) s' \<longleftrightarrow>
    \<alpha> = CtrlMisc \<and> c1 = Skip \<and> s' = (Inl h, c2) \<or>
    (\<exists>h' c1'. eopstep \<alpha> (h,c1) (h',c1') \<and> s' = (h', c1' ;; c2))\<close>
| \<open>eopstep \<alpha> (h, c1 \<^bold>+ c2) s' \<longleftrightarrow>
    \<alpha> = CtrlINDetL \<and> s' = (Inl h, c1) \<or>
    \<alpha> = CtrlINDetR \<and> s' = (Inl h, c2)\<close>
| \<open>eopstep \<alpha> (h, c1 \<box> c2) s' \<longleftrightarrow>
    (\<forall>x. \<alpha> \<noteq> Ctrl x) \<and> eopstep \<alpha> (h, c1) s' \<or>
    (\<forall>x. \<alpha> \<noteq> Ctrl x) \<and> eopstep \<alpha> (h, c2) s' \<or>
    (\<exists>x. \<alpha> \<noteq> Ctrl x) \<and> (\<exists>h' c1'. s' = (h', c1' \<box> c2) \<and> eopstep \<alpha> (h, c1) (h', c1')) \<or>
    (\<exists>x. \<alpha> \<noteq> Ctrl x) \<and> (\<exists>h' c2'. s' = (h', c1 \<box> c2') \<and> eopstep \<alpha> (h, c2) (h', c2')) \<or>
    \<alpha> = CtrlENDetL \<and> c1 = Skip \<and> s' = (Inl h, c2) \<or>
    \<alpha> = CtrlENDetR \<and> c2 = Skip \<and> s' = (Inl h, c1)\<close>
| \<open>eopstep \<alpha> (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    \<alpha> = CtrlParExit \<and> c1 = Skip \<and> c2 = Skip \<and> s' = (Inl h, Skip) \<or>
    (\<exists>h' c1'. eopstep \<alpha> (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2)) \<or>
    (\<exists>h' c2'. eopstep \<alpha> (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2'))\<close>
| \<open>eopstep \<alpha> (h, DO c OD) s' \<longleftrightarrow>
      (if \<forall>\<alpha>' s'. \<not> eopstep \<alpha>' (h, c) s' then
        \<alpha> = CtrlDoExit \<and> s' = (Inl h, Skip)
      else
        \<alpha> = CtrlDoLoop \<and> s' = (Inl h, c ;; DO c OD))\<close>
| \<open>eopstep \<alpha> (h, Atomic ap aq) s' \<longleftrightarrow>
    (\<exists>a. \<alpha> = Vis a \<and> (if ap h
                  then \<exists>h'. aq h h' \<and> fst s' = Inl h' \<and> snd s' = Skip
                  else fst s' = Inr () \<and> snd s' = Atomic ap aq))\<close>


paragraph \<open> Pretty extended operational semantics \<close>

abbreviation pretty_eopstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sub>e _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>\<alpha>\<rightarrow>\<^sub>e ht \<equiv> eopstep \<alpha> hs ht\<close>

abbreviation pretty_no_eopstep :: \<open>_ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>|\<rightarrow>\<^sub>e\<close> [60] 60) where
  \<open>hs \<midarrow>|\<rightarrow>\<^sub>e \<equiv> \<forall>\<alpha> ht. \<not> eopstep \<alpha> hs ht\<close>


subsection \<open> Lemmas about opstep \<close>

named_theorems opstep_iff

lemma eopstep_tau_preserves_heap:
  assumes \<open>s \<midarrow>Ctrl x\<rightarrow>\<^sub>e s'\<close>
  shows \<open>fst s' = Inl (fst s)\<close>
proof -
  { fix \<alpha>
    have \<open>s \<midarrow>\<alpha>\<rightarrow>\<^sub>e s' \<Longrightarrow> \<alpha> = Ctrl x \<Longrightarrow> fst s' = Inl (fst s)\<close>
      by (induct \<alpha> s s' arbitrary: x rule: eopstep.induct) (force split: if_splits)+
  }
  then show ?thesis
    using assms by force
qed

lemma eopstep_act_cases:
  \<open>s \<midarrow>\<alpha>\<rightarrow>\<^sub>e s' \<Longrightarrow>
    (\<And>x. \<alpha> = Ctrl x \<Longrightarrow> s \<midarrow>Ctrl x\<rightarrow>\<^sub>e s' \<Longrightarrow> fst s' = Inl (fst s) \<Longrightarrow> P) \<Longrightarrow>
    (\<And>x. \<alpha> = Vis x \<Longrightarrow> s \<midarrow>Vis x\<rightarrow>\<^sub>e s' \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  by (metis eact.exhaust eopstep_tau_preserves_heap)

lemma eopstep_preserves_all_atom_comm:
  assumes
    \<open>(h, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>e (h', c')\<close>
    \<open>all_atom_comm p c\<close>
  shows
    \<open>all_atom_comm p c'\<close>
proof -
  { fix s s'
    assume \<open>eopstep \<alpha> s s'\<close>
      and \<open>all_atom_comm p (snd s)\<close>
    then have \<open>all_atom_comm p (snd s')\<close>
      by (induct \<alpha> s s' rule: eopstep.induct) (force split: if_splits)+
  }
  then show ?thesis
    using assms
    by (metis snd_conv)
qed

lemmas eopstep_preserves_all_atom_commD =
  eopstep_preserves_all_atom_comm[rotated]

subsection \<open> Trace Semantics \<close>


paragraph \<open> Pretty extended operational semantics \<close>


text \<open>
  NOTE: the most recent action is at the *end* of the list
\<close>
inductive eopsteps :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> where
  eopsteps_base: \<open>eopstep \<alpha> sc zc' \<Longrightarrow> eopsteps [\<alpha>] sc zc'\<close>
| eopsteps_step:
    \<open>eopstep \<alpha> sc (Inl s', c') \<Longrightarrow>
      eopsteps \<alpha>s (s', c') zc'' \<Longrightarrow>
      eopsteps (\<alpha>#\<alpha>s) sc zc''\<close>

abbreviation pretty_eopsteps :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sub>e\<^sup>+ _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>\<alpha>s\<rightarrow>\<^sub>e\<^sup>+ ht \<equiv> eopsteps \<alpha>s hs ht\<close>


subsection \<open> Aligned \<close>

inductive trace_alignment :: \<open>(ctrl_act, 'b) eact list \<Rightarrow> (ctrl_act, 'b) eact list \<Rightarrow> bool\<close> where
  align_base: \<open>trace_alignment [] []\<close>
| align_indetl: \<open>trace_alignment xs ys \<Longrightarrow> trace_alignment (CtrlINDetL # xs) (CtrlINDetL # ys)\<close>
| align_indetr: \<open>trace_alignment xs ys \<Longrightarrow> trace_alignment (CtrlINDetR # xs) (CtrlINDetR # ys)\<close>
| align_endetl: \<open>trace_alignment xs ys \<Longrightarrow> trace_alignment (CtrlENDetL # xs) (CtrlENDetL # ys)\<close>
| align_endetr: \<open>trace_alignment xs ys \<Longrightarrow> trace_alignment (CtrlENDetR # xs) (CtrlENDetR # ys)\<close>
| align_parexit: \<open>trace_alignment xs ys \<Longrightarrow> trace_alignment (CtrlParExit # xs) (CtrlParExit # ys)\<close>
| align_doloop: \<open>trace_alignment xs ys \<Longrightarrow> trace_alignment (CtrlDoLoop # xs) (CtrlDoLoop # ys)\<close>
| align_doexit: \<open>trace_alignment xs ys \<Longrightarrow> trace_alignment (CtrlDoExit # xs) (CtrlDoExit # ys)\<close>
| align_miscA: \<open>trace_alignment xs ys \<Longrightarrow> trace_alignment (CtrlMisc # xs) ys\<close>
| align_miscB: \<open>trace_alignment xs ys \<Longrightarrow> trace_alignment xs (CtrlMisc # ys)\<close>
| align_visA: \<open>trace_alignment xs ys \<Longrightarrow> trace_alignment (Vis b # xs) ys\<close>
| align_visB: \<open>trace_alignment xs ys \<Longrightarrow> trace_alignment xs (Vis b # ys)\<close>


section \<open> (Strong) Non-interference \<close>

inductive noleak_wf :: \<open>('s \<Rightarrow> 'v) \<Rightarrow> 's comm \<Rightarrow> bool\<close> where
  noleak_wf_skip[intro!]: \<open>noleak_wf \<oo> Skip\<close>
| noleak_wf_seq[intro!]:
  \<open>noleak_wf \<oo> c1 \<Longrightarrow> noleak_wf \<oo> c2 \<Longrightarrow> noleak_wf \<oo> (c1 ;; c2)\<close>
| noleak_wf_par[intro!]:
  \<open>noleak_wf \<oo> c1 \<Longrightarrow> noleak_wf \<oo> c2 \<Longrightarrow> noleak_wf \<oo> (c1 \<parallel> c2)\<close>
| noleak_wf_indet[intro!]:
  \<open>c1 = \<langle>p1, q1\<rangle> \<or> c1 = \<langle>p1, q1\<rangle> ;; c1' \<and> noleak_wf \<oo> c1' \<Longrightarrow>
    c2 = \<langle>p2, q2\<rangle> \<or> c2 = \<langle>p2, q2\<rangle> ;; c2' \<and> noleak_wf \<oo> c2' \<Longrightarrow>
    \<forall>sx sy. p1 sx \<longrightarrow> p2 sy \<longrightarrow> \<oo> sx \<noteq> \<oo> sy \<Longrightarrow>
    noleak_wf \<oo> (c1 \<^bold>+ c2)\<close>
| noleak_wf_endet[intro!]:
  \<open>c1 = \<langle>p1, q1\<rangle> \<or> c1 = \<langle>p1, q1\<rangle> ;; c1' \<and> noleak_wf \<oo> c1' \<Longrightarrow>
    c2 = \<langle>p2, q2\<rangle> \<or> c2 = \<langle>p2, q2\<rangle> ;; c2' \<and> noleak_wf \<oo> c2' \<Longrightarrow>
    \<comment> \<open> indistinguishable \<close>
    \<forall>sx sy. p1 sx \<longrightarrow> p2 sy \<longrightarrow> \<oo> sx \<noteq> \<oo> sy \<Longrightarrow>
    noleak_wf \<oo> (c1 \<box> c2)\<close>
| noleak_wf_iter[intro!]:
  \<open>c = \<langle>p, q\<rangle> \<or> c = \<langle>p, q\<rangle> ;; c' \<and> noleak_wf \<oo> c' \<Longrightarrow>
  \<comment> \<open> indistinguishable \<close>
    \<forall>sx sy. p sx \<longrightarrow> \<not> p sy \<longrightarrow> \<oo> sx \<noteq> \<oo> sy \<Longrightarrow>
    noleak_wf \<oo> (DO c OD)\<close>
| noleak_wf_atom[intro!]: \<open>noleak_wf \<oo> (Atomic p q)\<close>

theorem noninterference:
  \<open>safe n cc zz r g q S F \<Longrightarrow>
    cc = liftC' c \<Longrightarrow>
    zz = Inl (sx, sy) \<Longrightarrow>
    S \<le> \<bbbA> \<oo> \<circ> exch4 \<Longrightarrow>
    S \<^emph>\<and> F \<le> \<bbbA> \<oo> \<circ> exch4 \<Longrightarrow>
    noleak_wf \<oo> c \<Longrightarrow>
    (sx, c) \<midarrow>\<alpha>sx\<rightarrow>\<^sub>e\<^sup>+ (zx', cx') \<Longrightarrow>
    (sy, c) \<midarrow>\<alpha>sy\<rightarrow>\<^sub>e\<^sup>+ (zy', cy') \<Longrightarrow>
    trace_alignment \<alpha>sx \<alpha>sy \<Longrightarrow>
    \<exists>sx' sy'.
      zx' = Inl sx' \<and>
      zy' = Inl sy' \<and>
      \<bbbA> \<oo> (sx', sy')\<close>
  apply (induct arbitrary: c sx sy rule: safe.inducts)
  oops


section \<open> [OLD] Noninterference \<close>

datatype run_st = Running | Terminated | Crashed

lemma run_st_neq_iff:
  \<open>rst \<noteq> Crashed \<longleftrightarrow> rst = Running \<or> rst = Terminated\<close>
  \<open>rst \<noteq> Running \<longleftrightarrow> rst = Terminated \<or> rst = Crashed\<close>
  \<open>rst \<noteq> Terminated \<longleftrightarrow> rst = Running \<or> rst = Crashed\<close>
  by (cases rst; simp)+


type_synonym 's ptrace = \<open>'s list \<times> run_st\<close>


datatype 'a rgact = Loc 'a | Env

abbreviation \<open>LocVis a \<equiv> Loc (Vis a)\<close>
abbreviation \<open>LocTau \<equiv> Loc Tau\<close>


datatype ('s, 'a) alist1 = ASingle 's | ACons 's 'a \<open>('s, 'a) alist1\<close>

fun ahd :: \<open>('s, 'a) alist1 \<Rightarrow> 's\<close> where
  \<open>ahd (ASingle s) = s\<close>
| \<open>ahd (ACons s _ _) = s\<close>

fun ahd_act :: \<open>('s, 'a) alist1 \<Rightarrow> 'a\<close> where
  \<open>ahd_act (ASingle _) = undefined\<close>
| \<open>ahd_act (ACons _ a _) = a\<close>

definition alength :: \<open>('a, 'b) alist1 \<Rightarrow> nat\<close> where
  \<open>alength xs \<equiv> size xs - 1\<close>

lemma alength_simps[simp]:
  \<open>alength (ASingle u) = 0\<close>
  \<open>alength (ACons u w t) = Suc (alength t)\<close>
  unfolding alength_def
  using alist1.size_neq[of t]
  by force+

lemma alength_rev_iff[simp]:
  \<open>alength xs = 0 \<longleftrightarrow> (\<exists>a. xs = ASingle a)\<close>
  \<open>alength xs = Suc k \<longleftrightarrow> (\<exists>a b ys. xs = ACons a b ys \<and> alength ys = k)\<close>
  by (cases xs; simp)+

lemma alength_leq_rev_iff[simp]:
  \<open>Suc k \<le> alength xs \<longleftrightarrow> (\<exists>a b ys. xs = ACons a b ys \<and> k \<le> alength ys)\<close>
  by (cases xs; simp)
  


definition fr_opstep
  :: \<open>('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      unit act \<Rightarrow>
      ('l \<times> 's, unit) pstate \<Rightarrow>
      ('l \<times> 's, unit) cpstate \<Rightarrow>
      bool\<close>
  where
  \<open>fr_opstep F \<alpha> sc sc' \<equiv>
    \<comment> \<open> plain opstep \<close>
    sc \<midarrow>\<alpha>\<rightarrow> sc' \<or>
    \<comment> \<open> framed opstep \<close>
    (case sc of ((hl, hs), c) \<Rightarrow>
      \<exists>hlf.
        F (hlf, hs) \<and>
        hl ## hlf \<and>
        (case sc' of
          (Inl (hl', hs'), c') \<Rightarrow>
            hl' ## hlf \<and>
            (\<alpha> = Tau \<longrightarrow> hl' = hl) \<and>
            ((hl + hlf, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl' + hlf, hs'), c')
        | (Inr (), c') \<Rightarrow> 
            ((hl + hlf, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inr (), c'))
    )\<close>

abbreviation pretty_fr_opstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_, _)\<rightarrow> _\<close> [60,0,0,60] 60) where
  \<open>s \<midarrow>F, \<beta>\<rightarrow> s' \<equiv> fr_opstep F \<beta> s s'\<close>

abbreviation pretty_no_fr_opstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>(_, |)\<rightarrow>\<close> [60,0] 60) where
  \<open>s \<midarrow>F, |\<rightarrow> \<equiv> \<forall>\<beta> s'. \<not> fr_opstep F \<beta> s s'\<close>


lemma fr_opstep_from_skip_then:
  \<open>fr_opstep F \<beta> s s' \<Longrightarrow> s = (h, Skip) \<Longrightarrow> snd s' = Skip\<close>
  by (clarsimp simp add: fr_opstep_def
      split: prod.splits sum.splits unit.splits)

lemma fr_opstep_from_skip_then2[simp]:
  \<open>fr_opstep F \<beta> (h, Skip) (h', c') \<Longrightarrow> c' = Skip\<close>
  using fr_opstep_from_skip_then
  by fastforce

lemma fr_opstep_tau_preserves_state:
  \<open>s \<midarrow>F, Tau\<rightarrow> s' \<Longrightarrow> fst s' = Inl (fst s)\<close>
  unfolding fr_opstep_def
  apply (erule disjE)
   apply (force dest: opstep_tau_preserves_heap)
  apply (clarsimp split: sum.splits unit.splits)
  apply (case_tac x)
   apply (force dest: opstep_tau_preserves_heap)
  apply (force dest: opstep_tau_preserves_heap)
  done

lemma fr_opstep_tau_preserves_state_simp:
  \<open>(h, c) \<midarrow>F, Tau\<rightarrow> (h', c') \<Longrightarrow> h' = Inl h\<close>
  by (force dest: fr_opstep_tau_preserves_state)


text \<open>
  Note the the most recent state is at the *head* of the list.
  e.g. [sn, s{n-1}, ..., s1, s0].

  This is a partial trace semantics, in the style of Aczel, where environment moves are represented
  in the trace.
\<close>
inductive trsem'
  :: \<open>('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's) comm \<Rightarrow>
      ('l \<times> 's) comm \<Rightarrow>
      (('l \<times> 's) \<times> run_st, unit act rgact) alist1 \<Rightarrow>
      bool\<close>
  where
    trsem'_init[intro!]:
    \<open>p (fst sr) \<Longrightarrow>
      if c = Skip then snd sr = Terminated \<and> q (fst sr) else snd sr = Running \<Longrightarrow>
      trsem' p q r g F S c c (ASingle sr)\<close>
  | trsem'_step[intro]:
    \<open>trsem' p q r g F S cinit c t \<Longrightarrow>
      ahd t = ((hl, hs), rst) \<Longrightarrow>
      rst \<noteq> Crashed \<Longrightarrow>
      rst' = Terminated \<longrightarrow> q s \<Longrightarrow>
      (case \<gamma> of
        Loc \<alpha> \<Rightarrow> (\<exists>s'.
          ((hl, hs), c) \<midarrow>F, \<alpha>\<rightarrow> (s', c') \<and>
          (case s' of
            Inr () \<Rightarrow> hl' = hl \<and> hs' = hs \<and> rst' = Crashed
          | Inl hls' \<Rightarrow>
              hls' = (hl',hs') \<and>
              (if c' = Skip then rst' = Terminated else rst' = Running)))
      | Env \<Rightarrow> hl' = hl \<and> c' = c \<and> r hs hs' \<and> rst' = rst \<and> rst \<noteq> Crashed) \<Longrightarrow>
      trsem' p q r g F S cinit c' (ACons ((hl',hs'), rst') \<gamma> t)\<close>

inductive_cases trsem_initE[elim!]: \<open>trsem' p q r g F S cinit c (ASingle s)\<close>
inductive_cases trsem_stepE[elim!]: \<open>trsem' p q r g F S cinit c (ACons s' \<alpha> t)\<close>

definition \<open>trsem p q r g F S c \<equiv> {t. \<exists>cx. trsem' p q r g F S c cx t}\<close>


inductive trace_step_align
  :: \<open>('s, 'a act rgact) alist1 \<Rightarrow> ('s, 'a act rgact) alist1 \<Rightarrow> bool\<close>
  where
  init[intro!]: \<open>trace_step_align (ASingle s1) (ASingle s2)\<close>
| step_left_tau[intro]:
  \<open>trace_step_align t1 t2 \<Longrightarrow> trace_step_align (ACons s1 LocTau t1) t2\<close>
| step_right_tau[intro]:
  \<open>trace_step_align t1 t2 \<Longrightarrow> trace_step_align t1 (ACons s2 LocTau t2)\<close>
| step_env[intro!]:
  \<open>trace_step_align t1 t2 \<Longrightarrow>
    trace_step_align (ACons s1 Env t1) (ACons s2 Env t2)\<close>
| step_vis[intro!]:
  \<open>trace_step_align t1 t2 \<Longrightarrow>
    trace_step_align (ACons s1 (LocVis a1) t1) (ACons s2 (LocVis a2) t2)\<close>

inductive_cases trace_step_align_singleE[elim!]:
  \<open>trace_step_align (ASingle s1) (ASingle s2)\<close>
inductive_cases trace_step_align_single_leftE[elim]:
  \<open>trace_step_align (ASingle s1) t2\<close>
inductive_cases trace_step_align_single_rightE[elim]:
  \<open>trace_step_align t1 (ASingle s2)\<close>

inductive_cases trace_step_align_visE[elim!]:
  \<open>trace_step_align (ACons s1 (LocVis a1) t1) (ACons s2 (LocVis a2) t2)\<close>
inductive_cases trace_step_align_envE[elim!]:
  \<open>trace_step_align (ACons s1 Env t1) (ACons s2 Env t2)\<close>
inductive_cases trace_step_align_consE[elim]:
  \<open>trace_step_align (ACons s1 \<beta>1 t1) (ACons s2 \<beta>2 t2)\<close>

inductive_cases trace_step_align_cons_tauE[elim]:
  \<open>trace_step_align (ACons s1 \<beta>1 t1) (ACons s2 LocTau t2)\<close>
inductive_cases trace_step_align_tau_consE[elim]:
  \<open>trace_step_align (ACons s1 LocTau t1) (ACons s2 \<beta>2 t2)\<close>

lemma trace_step_align_cons_init_iff[simp]:
  \<open>trace_step_align (ACons s1 a t1) (ASingle s2)
    \<longleftrightarrow> trace_step_align t1 (ASingle s2) \<and> a = LocTau\<close>
  by (blast elim: trace_step_align.cases)

lemma trace_step_align_init_cons_iff[simp]:
  \<open>trace_step_align (ASingle s1) (ACons s2 a t2)
    \<longleftrightarrow> trace_step_align (ASingle s1) t2 \<and> a = LocTau\<close>
  by (blast elim: trace_step_align.cases)



\<comment> \<open> TODO: There's a lingering question here over how Env steps are supposed to work. \<close>
inductive trace_agree
  :: \<open>('s \<Rightarrow> 'o) \<Rightarrow> ('s, 'a act rgact) alist1 \<Rightarrow> ('s, 'a act rgact) alist1 \<Rightarrow> bool\<close>
  where
  tragree_init[intro!]: \<open>\<bbbA> \<oo> (s1,s2) \<Longrightarrow> trace_agree \<oo> (ASingle s1) (ASingle s2)\<close>
| tragree_step_left_tau[intro]:
  \<open>trace_agree \<oo> t1 t2 \<Longrightarrow> trace_agree \<oo> (ACons s1' LocTau t1) t2\<close>
| tragree_step_right_tau[intro]:
  \<open>trace_agree \<oo> t1 t2 \<Longrightarrow> trace_agree \<oo> t1 (ACons s2' LocTau t2)\<close>
| tragree_step_env[intro!]:
  \<open>trace_agree \<oo> t1 t2 \<Longrightarrow>
    \<bbbA> \<oo> (s1,s2) \<Longrightarrow>
    trace_agree \<oo> (ACons s1 Env t1) (ACons s2 Env t2)\<close>
| tragree_step_vis[intro!]:
  \<open>trace_agree \<oo> t1 t2 \<Longrightarrow>
    \<bbbA> \<oo> (s1,s2) \<Longrightarrow>
    a1 = a2 \<Longrightarrow>
    trace_agree \<oo> (ACons s1 (LocVis a1) t1) (ACons s2 (LocVis a2) t2)\<close>

inductive_cases trace_agree_initE[elim!]: \<open>trace_agree \<oo> (ASingle s1) (ASingle s2)\<close>
inductive_cases trace_agree_visE[elim!]:
  \<open>trace_agree \<oo> (ACons s1 (LocVis a1) t1) (ACons s2 (LocVis a2) t2)\<close>
inductive_cases trace_agree_envE[elim!]:
  \<open>trace_agree \<oo> (ACons s1 Env t1) (ACons s2 Env t2)\<close>

lemma agree_cons_init_iff[simp]:
  \<open>trace_agree \<oo> (ACons s1 a t1) (ASingle s2)
    \<longleftrightarrow> trace_agree \<oo> t1 (ASingle s2) \<and> a = LocTau\<close>
  by (blast elim: trace_agree.cases)

lemma agree_init_cons_iff[simp]:
  \<open>trace_agree \<oo> (ASingle s1) (ACons s2 a t2)
    \<longleftrightarrow> trace_agree \<oo> (ASingle s1) t2 \<and> a = LocTau\<close>
  by (blast elim: trace_agree.cases)


lemma alist1_le_Suc0_iff[simp]:
  fixes t :: \<open>('a,'b) alist1\<close>
  shows \<open>size t \<le> Suc 0 \<longleftrightarrow> (\<exists>a. t = ASingle a)\<close>
  by (induct t) (simp add: alist1.size_neq)+

lemma alist1_gt_Suc_iff[simp]:
  fixes t :: \<open>('a,'b) alist1\<close>
  shows
    \<open>0 < k \<Longrightarrow>
      Suc k \<le> size t \<longleftrightarrow> (\<exists>a b t'. t = ACons a b t' \<and> k \<le> size t')\<close>
  by (induct t arbitrary: k) simp+

lemma trsem'_init_skip_then:
  \<open>trsem' p q r g S F cinit c t1 \<Longrightarrow> cinit = Skip \<Longrightarrow> c = Skip\<close>
  apply (induct rule: trsem'.inducts)
   apply force
  apply (clarsimp split: rgact.splits sum.splits unit.splits)
   apply (case_tac s'; force)
  done

lemma trsem'_init_skip_then':
  \<open>trsem' p q r g S F Skip c t1 \<Longrightarrow> c = Skip\<close>
  by (simp add: trsem'_init_skip_then)

lemma ex_trsem'_init_skip_iff[simp]:
  \<open>(\<exists>c. trsem' p q r g S F Skip c t1) \<longleftrightarrow> trsem' p q r g S F Skip Skip t1\<close>
  using trsem'_init_skip_then by blast

lemma apfst_eq_conv2: "apfst f x = apfst g y \<longleftrightarrow> f (fst x) = g (fst y) \<and> snd x = snd y"
  by (cases x; cases y) clarsimp

lemma apsnd_eq_conv2:
  "apsnd f x = apsnd g y \<longleftrightarrow> f (snd x) = g (snd y) \<and> fst x = fst y"
  by (cases x; cases y) force


(* 
Let c be a simple program that operates on a single state and 
let \<oo> be  a function describing the observations the attacker can make on a given state,
the function (liftC \<oo> c) turns the program c into one that operates on a pair of states and that crashes
when run on states that are distingishable through  \<oo>. This in turn, which can be  used for info flow reasoning.



the safe judgement provides the same amount of information as a programming language semantics that 
is a tree T of all possible executions that can happen, as well as a proof that if the precondition and 
the relies, then for all possible executions in the tree
   (1) they don't fail and
   (2) the obey the guarantees and the postcondition
   (3) the frame condition is preserved


define function f ( c, n, p, r) = trees T

prove
theorems 
safe_imp_no_crash:"safe  c, n, p, r, q,g \<longrightarrow> 
  (1) the program f ( c, n, p, r) does not crash,
  (2) the program  obey the guarantees and the postcondition
  (3) the frame condition is preserved


definition noninterference is: given a pair of states s1 and s2, indistinguishable by \<oo>,
no execution of the program on s1 and s2 respectively, are pair-wise indistinguishable by \<oo> throughout execution and 
the program executions match/allign.


-------

definition noninterference is: given a pair of states, indistinguishable by \<oo>,
no execution of the program c (lifted to pairs of states) reaches a pair of states distinguishable by \<oo>.

definition noninterference on (liftC \<oo> c) is also a property s.t.
given a pair of states that are indistinguishable through \<oo>, of the program  (liftC \<oo> c) doesn't fail 
then all pairs of states throughout the 
execution of liftC \<oo> c are indistinguishable.

the noninterference judgement on (liftC \<oo> c) provides the same amount of information as a programming language semantics that 
is a tree T of all possible executions that can happen on pairs of states, as well as a proof that if the precondition and 
the relies hold and the precondition respects  \<oo>, then for all possible executions in the tree
   if the program doesn't fail 
    the indistinguishability predicate is preserved


(do we also want the frame condition to be preserved)

question
is there anything other than no-crash that is needed to prove non-interference and (e.g. there is no non-determinism), potentially?

if not,

prove 
theorem noninterference: 


If we can prove this, we are done (with the security paper).

question 
can we change liftC to not crash
then instead prove
>how can we generalise the lifting function liftC and instead of crashing 
 instantiate the guarantee in a way that enforces non-interference/indistinguishability?

then pro

If the preconditions are indistinguishable using \<oo>, and the lifted program  (liftC \<oo> c)  is safe,
and the preconditinos are indistinguishable using \<oo>.

If the preconditions are indistinguishable using \<oo>, and the lifted program  (liftC \<oo> c)  is safe,
and the preconditinos are indistinguishable using \<oo>.





properties (p, r) do not crash
these executions will 
and you can also extract a tree semantics that only contains 
split to two pieces, one is all possible executions, and the other is 
function to filter safe executions out of safe judgement
if there is no crashing anywhere 

define noninterference directly on liftC o C

lemma exact_security:
  fixes hl1 hl2 :: \<open>'l :: pre_perm_alg\<close>
    and hs1 hs2 :: 's
    and c :: \<open>('l \<times> 's, unit) comm\<close>
    and p q :: \<open>'l \<times> 's \<Rightarrow> bool\<close>
    and r g :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
  shows
  \<open>safe
      (max (alength t1) (alength t2))
      (liftC \<oo> c)
      (Inl (exch4 (fst (ahd t1), fst (ahd t2))))
      (liftR r) (liftR g)
      (liftP q \<circ> exch4)
      (liftP S \<circ> exch4) (liftP F \<circ> exch4) \<Longrightarrow> f ( c, n, p, r) 
no_crashing \<and> indistinguishable everywhere through initial_s p c  \<oo>  >
*)


(*
lemma exact security
<no_crashing \<Longrightarrow>
    t1 \<in> trsem p q r g S F c \<Longrightarrow>
    t2 \<in> trsem p q r g S F c \<Longrightarrow>
    trace_step_align t1 t2 \<Longrightarrow>
    \<lblot> p \<rblot> \<le> \<bbbA> \<oo> \<Longrightarrow>
    trace_agree (apfst \<oo>) t1 t2\<close>
*)
lemma exact_security:
  fixes hl1 hl2 :: \<open>'l :: pre_perm_alg\<close>
    and hs1 hs2 :: 's
    and c :: \<open>('l \<times> 's, unit) comm\<close>
    and p q :: \<open>'l \<times> 's \<Rightarrow> bool\<close>
    and r g :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
  shows
  \<open>safe
    (max (alength t1) (alength t2))
    (liftC \<oo> c)
    (Inl (exch4 (fst (ahd t1), fst (ahd t2))))
    (liftR r) (liftR g)
    (liftP q \<circ> exch4)
    (liftP S \<circ> exch4)
    (liftP F \<circ> exch4) \<Longrightarrow>
    t1 \<in> trsem p q r g S F c \<Longrightarrow>
    t2 \<in> trsem p q r g S F c \<Longrightarrow>
    trace_step_align t1 t2 \<Longrightarrow>
    \<lblot> p \<rblot> \<le> \<bbbA> \<oo> \<Longrightarrow>
    trace_agree (apfst \<oo>) t1 t2\<close>
proof (induct rule: trace_step_align.inducts)
  case (init s1 s2)
  then show ?case
    apply (clarsimp simp add: trsem_def sec_agree_def le_fun_def
        apfst_eq_conv2)
    apply (metis surj_pair)
    done
next
  case (step_left_tau t1 t2 s1)
  then show ?case
    apply (clarsimp simp add: trsem_def sec_agree_def le_fun_def
        apfst_eq_conv2)
    apply (frule fr_opstep_tau_preserves_state_simp)
    apply (case_tac t2)
     apply (simp, meson safe_step_SucD; fail)
    apply clarsimp
    apply (clarsimp simp add: safe_suc_iff)
    apply (rule tragree_step_left_tau)
    sorry
    apply (metis (no_types, lifting) le_Suc_eq max_def)
  done
next
  case (step_right_tau t1 t2 s2)
  then show ?case
    apply (clarsimp simp add: trsem_def sec_agree_def le_fun_def
        apfst_eq_conv2)
    apply (frule fr_opstep_tau_preserves_state_simp)
    apply (case_tac t1)
     apply (simp, meson safe_step_SucD; fail)
    apply (clarsimp simp add: safe_suc_iff)
    apply (rule tragree_step_right_tau)
    sorry
next
  case (step_env t1 t2 s1 s2)
  then show ?case
    apply (clarsimp simp add: trsem_def sec_agree_def le_fun_def
        apfst_eq_conv2)
    apply (rule tragree_step_env, blast)
    apply (clarsimp simp add: trsem_def sec_agree_def le_fun_def
        apfst_eq_conv2)
    apply (simp add: rely_preserves_agree_def)
    oops
next
  case (step_vis t1 t2 s1 a1 s2 a2)
  then show ?case sorry
qed

lemma security:
  fixes hl1 hl2 :: \<open>'l :: pre_perm_alg\<close>
    and hs1 hs2 :: 's
    and c :: \<open>('l \<times> 's, unit) comm\<close>
    and p q :: \<open>'l \<times> 's \<Rightarrow> bool\<close>
    and r g :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
  shows
  \<open>trace_step_align t1 t2 \<Longrightarrow>
    (\<And>n s.
      (liftP p \<circ> exch4) s \<Longrightarrow>
      safe n (liftC \<oo> c) (Inl s)
        (liftR r) (liftR g)
        (liftP q \<circ> exch4)
        (liftP S \<circ> exch4) (liftP F \<circ> exch4)) \<Longrightarrow>
    t1 \<in> trsem p q r g S F c \<Longrightarrow>
    t2 \<in> trsem p q r g S F c \<Longrightarrow>
    \<lblot> p \<rblot> \<le> \<bbbA> \<oo> \<Longrightarrow>
    trace_agree (apfst \<oo>) t1 t2\<close>
  sorry

end