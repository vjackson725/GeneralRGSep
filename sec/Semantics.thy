 theory Semantics
  imports "../Soundness"
begin

(* TODO: move *)

lemma eqrel_times_eqrel_eq[simp]:
  \<open>((=) \<times>\<^sub>R (=)) = (=)\<close>
  by (force simp add: rel_Times_def)

lemma ex_helpers:
  \<open>(\<exists>c1'. (\<exists>c1. P c1 \<and> c1' = f c1) \<and> Q c1') \<longleftrightarrow> (\<exists>c1. P c1 \<and> Q (f c1))\<close>
  by blast

lemma imp_iff_imp_iff:
  \<open>(A \<longrightarrow> B) = (A \<longrightarrow> C) \<longleftrightarrow> (A \<longrightarrow> B = C)\<close>
  by blast

type_synonym ('a,'b) rgstate = \<open>(('a \<times> 'a) \<times> ('b \<times> 'b))\<close>

type_synonym ('a,'b) secstate = \<open>(('a \<times> 'b) \<times> ('a \<times> 'b))\<close>


section \<open> Pred-executions \<close>

text \<open>
  Predicate over all states of all executions.
  (N.B. This does not avoid crashes.)
\<close>

type_synonym 's config = \<open>'s \<times> 's comm\<close>

inductive pred_executions
  :: \<open>(('l::pre_perm_alg  \<times> 's) config \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's) comm \<Rightarrow>
      'l \<times> 's + unit \<Rightarrow>
      nat \<Rightarrow>
      bool\<close>
  where
  pred_executions_nil[intro!]: \<open>pred_executions P F r c (Inl (hl, hs)) 0\<close>
| pred_executions_step[intro]:
  \<open>\<comment> \<open> The config predicate holds \<close>
    P ((hl, hs), c) \<Longrightarrow>
    \<comment> \<open> rely steps generate states \<close>
    (\<And>hs'. r hs hs' \<Longrightarrow> pred_executions P F r c (Inl (hl, hs')) n) \<Longrightarrow>
    \<comment> \<open> framed opsteps generate states \<close>
    (\<And>\<alpha> hlhlf' hs' c' hlf.
        hl ## hlf \<Longrightarrow>
        ((hl + hlf, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hlhlf', hs'), c') \<Longrightarrow>
        F (hlf, hs) \<Longrightarrow>
        (\<exists>hl'.
          hl' ## hlf \<and>
          hlhlf' = hl' + hlf \<and>
          (\<alpha> = Tau \<longrightarrow> hl' = hl) \<and>
          pred_executions P F r c' (Inl (hl', hs')) n)) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    pred_executions P F r c (Inl (hl, hs)) (Suc n)\<close>

subsection \<open> Proofs about safe \<close>

inductive_cases pred_executions_zeroE[elim!]: \<open>pred_executions P F r c z 0\<close>
inductive_cases pred_executions_sucE[elim]: \<open>pred_executions P F r c z (Suc n)\<close>

lemma pred_executions_nil_iff[simp]:
  \<open>pred_executions P F r c z 0 \<longleftrightarrow> (\<exists>hl hs. z = Inl (hl, hs))\<close>
  by force

lemma pred_executions_suc_iff:
  \<open>pred_executions P F r c z (Suc n) \<longleftrightarrow>
    (\<exists>hl hs. z = Inl (hl, hs) \<and>
      P ((hl, hs), c) \<and>
      (\<forall>hs'. r hs hs' \<longrightarrow> pred_executions P F r c (Inl (hl, hs')) n) \<and>
      (\<forall>\<alpha> hlhlf' hs' c' hlf.
          hl ## hlf \<longrightarrow>
          ((hl + hlf,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hlhlf',hs'), c') \<longrightarrow>
          F (hlf, hs) \<longrightarrow>
          (\<exists>hl'.
            hl' ## hlf \<and>
            hlhlf' = hl' + hlf \<and>
            (\<alpha> = Tau \<longrightarrow> hl' = hl) \<and>
            pred_executions P F r c' (Inl (hl', hs')) n)))\<close>
  apply (rule iffI)
   apply (erule pred_executions_sucE; force)
  apply (case_tac z; force)
  done

lemma pred_executions_pred_mono:
  \<open>p \<le> q \<Longrightarrow> pred_executions p F r c z n \<Longrightarrow> pred_executions q F r c z n\<close>
  apply (induct n arbitrary: c z)
   apply blast
  apply (clarsimp simp add: pred_executions_suc_iff)
  apply (intro conjI, blast, (meson; fail))
  done

lemmas pred_executions_pred_monoD = pred_executions_pred_mono[rotated]


section \<open> Double-state lifting \<close>

subsection \<open> exchange \<close>

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

lemma prod_destruct_exch4_eq[simp]:
  \<open>fst (fst (exch4 x)) = fst (fst x)\<close>
  \<open>fst (snd (exch4 x)) = snd (fst x)\<close>
  \<open>snd (fst (exch4 x)) = fst (snd x)\<close>
  \<open>snd (snd (exch4 x)) = snd (snd x)\<close>
  unfolding exch4_def
  by (clarsimp split: prod.splits)+

lemma prod_part_destruct_exch4_eq[simp]:
  \<open>fst (exch4 (ab, cd)) = (fst ab, fst cd)\<close>
  \<open>snd (exch4 (ab, cd)) = (snd ab, snd cd)\<close>
  by (simp add: exch4_def split: prod.splits)+

lemma le_exch4_shunt:
  \<open>p \<le> q \<circ> exch4 \<longleftrightarrow> p \<circ> exch4 \<le> q\<close>
  by (metis comp_def exch4_idem le_fun_def)

lemma eq_exch4_iff[simp]:
  \<open>((ax, bx), (ay, by)) = exch4 ab \<longleftrightarrow> fst ab = (ax, ay) \<and> snd ab = (bx, by)\<close>
  by (force simp add: exch4_def split: prod.splits)


subsection \<open> relational lifting \<close>

syntax
  "_twoPredLiftBasic"  :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"  ("\<lblot> _ \<rblot>" [0] 999)
  "_twoPredLiftDouble"  :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<lblot> _ \<bar> _ \<rblot>" [0,0] 998)
  "_twoPredLiftL"  :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<lblot> _ \<bar>" [0] 997)
  "_twoPredLiftR"  :: "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<bar> _ \<rblot>" [0] 997)

translations
  "_twoPredLiftBasic p" \<rightharpoonup> "(CONST pred_Times) p p"
  "_twoPredLiftDouble p q" \<rightleftharpoons> "(CONST pred_Times) p q"
  "_twoPredLiftL p" \<rightharpoonup> "(CONST pred_Times) p \<top>"
  "_twoPredLiftR q" \<rightharpoonup> "(CONST pred_Times) \<top> q"


subsection \<open> Agreement \<close>

definition sec_agree
  :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool\<close> (\<open>\<bbbA>\<close>)
  where
    \<open>\<bbbA> vf \<equiv> (\<lambda>(x,y). vf x = vf y)\<close>

lemma conj_agree_iff:
  \<open>\<bbbA> v1 \<sqinter> \<bbbA> v2 = \<bbbA> (\<lambda>x. (v1 x, v2 x))\<close>
  by (simp add: sec_agree_def exch4_def comp_def fun_eq_iff split: prod.splits)


subsection \<open> Command Times \<close>

function(sequential) comm_Times :: \<open>'a comm \<Rightarrow> 'b comm \<Rightarrow> ('a \<times> 'b) comm\<close> (infixr \<open>\<times>\<^sub>C\<close> 80) where
  \<open>Skip \<times>\<^sub>C Skip = Skip\<close>
| \<open>(cax;;cay) \<times>\<^sub>C (cbx;;cby) = (cax \<times>\<^sub>C cbx) ;; (cay \<times>\<^sub>C cby)\<close>
| \<open>(cax \<parallel> cay) \<times>\<^sub>C (cbx \<parallel> cby) = (cax \<times>\<^sub>C cbx) \<parallel> (cay \<times>\<^sub>C cby)\<close>
| \<open>(cax \<^bold>+ cay) \<times>\<^sub>C (cbx \<^bold>+ cby) = (cax \<times>\<^sub>C cbx) \<^bold>+ (cay \<times>\<^sub>C cby)\<close>
| \<open>(cax \<box> cay) \<times>\<^sub>C (cbx \<box> cby) = (cax \<times>\<^sub>C cbx) \<box> (cay \<times>\<^sub>C cby)\<close>
| \<open>(DO ca OD) \<times>\<^sub>C (DO cb OD) = DO (ca \<times>\<^sub>C cb) OD\<close>
| \<open>\<langle>pa, qa\<rangle> \<times>\<^sub>C \<langle>pb, qb\<rangle> = \<langle>pa \<times>\<^sub>P pb, qa \<times>\<^sub>R qb\<rangle>\<close>
  by pat_completeness auto (* slow *)

termination
  by (relation \<open>measure (\<lambda>(ca,cb). size ca + size cb)\<close>) simp+


subsection \<open> Double-state Lifting \<close>

(* TODO: move *)
definition diag (\<open>\<Delta>\<close>) where \<open>diag x = (x,x)\<close>
declare diag_def[simp]

abbreviation(input) \<open>liftP p \<equiv> \<lblot> p \<rblot>\<close>
abbreviation(input) \<open>liftR r \<equiv> r \<times>\<^sub>R r\<close>

definition liftC :: \<open>('l \<times> 's) comm \<Rightarrow> (('l \<times> 'l) \<times> ('s \<times> 's)) comm\<close> where
  \<open>liftC c \<equiv> map_comm (\<lambda>p q. (p \<circ> exch4, q \<circ>\<^sub>2 exch4)) (c \<times>\<^sub>C c)\<close>

definition
  \<open>unliftC \<equiv> map_comm (\<lambda>p q. (p \<circ> exch4 \<circ> \<Delta>, q \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)))\<close>

lemma liftC_def':
  \<open>liftC c = map_comm (\<lambda>p q. (liftP p \<circ> exch4, liftR q \<circ>\<^sub>2 exch4)) c\<close>
  unfolding liftC_def
  by (induct c) simp+

lemmas liftC_simps[simp] =
  map_comm.simps[of \<open>(\<lambda>p q. (liftP p \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close>,
    simplified liftC_def'[symmetric]]

lemmas liftC_rev_iff =
  map_comm_rev_iff[of \<open>(\<lambda>p q. (liftP p \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close>,
    simplified liftC_def'[symmetric]]


lemma unlift_lift_cancel[simp]:
  \<open>unliftC (liftC c) = c\<close>
  unfolding unliftC_def liftC_def'
  by (induct c) (simp add: sec_agree_def)+

lemma unliftC_atom_simp:
  \<open>unliftC \<langle>p, q\<rangle> = \<langle>\<lambda>x. p (exch4 (x, x)), \<lambda>x y. q (exch4 (x, x)) (exch4 (y, y))\<rangle>\<close>
  unfolding unliftC_def
  by force

lemmas unliftC_simp[simp] =
  map_comm.simps(1-5,7)[of \<open>(\<lambda>p q. (\<lambda>x. p (exch4 (x,x)), \<lambda>x y. q (exch4 (x,x)) (exch4 (y,y))))\<close>,
    simplified unliftC_def[symmetric]]
  unliftC_atom_simp

lemmas unliftC_rev_iff =
  map_comm_rev_iff[of
    \<open>(\<lambda>p q. (\<lambda>x. p (exch4 (x,x)), \<lambda>x y. q (exch4 (x,x)) (exch4 (y,y))))\<close>,
    simplified unliftC_def[symmetric]]

lemma liftC_cancel[simp]:
  \<open>liftC ca = liftC cb \<longleftrightarrow> ca = cb\<close>
  apply (induct cb arbitrary: ca)
        apply (metis liftC_rev_iff(1))
       apply (metis liftC_rev_iff(2))
      apply (metis liftC_rev_iff(3))
     apply (metis liftC_rev_iff(4))
    apply (metis liftC_rev_iff(5))
   apply (fastforce simp add: liftC_rev_iff fun_eq_iff sec_agree_def)
  apply (metis liftC_rev_iff(6))
  done


section \<open> Tree Noninterference \<close>

section \<open> Safe \<close>

abbreviation tree_weak_noninterference where
  \<open>tree_weak_noninterference \<oo> F \<equiv>
    pred_executions
      (\<lambda>((hl,hs),c).
        (\<forall>hlf. F (hlf,hs) \<longrightarrow> hl ## hlf \<longrightarrow> \<bbbA> \<oo> (exch4 (hl + hlf, hs))) \<and>
        (\<exists>cx. c = liftC cx))
      F\<close>

lemma opstep_preserves_liftC:
  \<open>(s, liftC c) \<midarrow>\<alpha>\<rightarrow> (z', cx') \<Longrightarrow> \<exists>c'. cx' = liftC c'\<close>
proof (induct c arbitrary: s z' cx' \<alpha>)
  case Skip
  then show ?case by force
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
    by force
next
  case (Endet c1 c2)
  then show ?case
    using Endet.prems
    by (simp, metis Endet.hyps(2) liftC_simps(5))
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
    by (clarsimp split: if_splits, metis liftC_simps(1), metis liftC_simps(2,7))
qed

theorem weak_noninterference:
  \<open>safe n c z r g q S F \<Longrightarrow>
    z = Inl s \<Longrightarrow>
    c = liftC cx \<Longrightarrow>
    S \<^emph>\<and> F \<le> \<bbbA> \<oo> \<circ> exch4 \<Longrightarrow>
    tree_weak_noninterference \<oo> F r c z n\<close>
  apply (induct arbitrary: s cx rule: safe.inducts)
   apply force
  apply (clarsimp simp add: liftC_rev_iff pred_executions_suc_iff)
  apply (rename_tac c hla hlb hsa hsb)
  apply (intro conjI)
   apply (clarsimp simp add: le_fun_def sepconj_conj_def, blast)
  apply clarsimp
  apply (frule opstep_preserves_liftC)
  apply clarsimp
  apply (drule meta_spec2, drule meta_spec2, drule meta_spec, drule meta_mp,
      rule conjI, assumption, assumption, drule meta_mp, assumption, drule meta_mp, assumption)
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

subsection \<open> Parallel-labelled actions \<close>

text \<open> Extended Actions \<close>

datatype aact =
  PL aact |
  PR aact |
  TauINdetL |
  TauINdetR |
  TauBasic | \<comment> \<open> Taus other than Taus from INdet \<close>
  AVis

fun strip_aact :: \<open>aact \<Rightarrow> unit act\<close> where
  \<open>strip_aact TauBasic = Tau\<close>
| \<open>strip_aact AVis = Vis ()\<close>
| \<open>strip_aact TauINdetL = Tau\<close>
| \<open>strip_aact TauINdetR = Tau\<close>
| \<open>strip_aact (PL \<beta>) = strip_aact \<beta>\<close>
| \<open>strip_aact (PR \<beta>) = strip_aact \<beta>\<close>

fun basic_tau_aact :: \<open>aact \<Rightarrow> bool\<close> where
  \<open>basic_tau_aact TauBasic = True\<close>
| \<open>basic_tau_aact AVis = False\<close>
| \<open>basic_tau_aact TauINdetL = False\<close>
| \<open>basic_tau_aact TauINdetR = False\<close>
| \<open>basic_tau_aact (PL \<beta>) = basic_tau_aact \<beta>\<close>
| \<open>basic_tau_aact (PR \<beta>) = basic_tau_aact \<beta>\<close>

text \<open>
  In an aact, a tau move may be buried under parallel synchronisation labels,
  or divided into an INdet Tau, which are handled separately by the evaluation semantics.
  In programs where sub-programs may take actions (\<box>), we need an
  inductive test for whether an action is internal, as the sub-program may be a parallel.
\<close>
definition \<open>tau_aact \<beta> \<equiv> strip_aact \<beta> = Tau\<close>
definition \<open>vis_aact \<beta> \<equiv> strip_aact \<beta> = Vis ()\<close>

lemma not_tau_aact_iff[simp]:
  \<open>\<not> tau_aact \<beta> \<longleftrightarrow> vis_aact \<beta>\<close>
  by (simp add: tau_aact_def vis_aact_def)

lemma not_vis_aact_iff[simp]:
  \<open>\<not> vis_aact \<beta> \<longleftrightarrow> tau_aact \<beta>\<close>
  using not_tau_aact_iff by blast

lemma vis_tau_aact_incompatible:
  \<open>vis_aact \<beta> \<Longrightarrow> tau_aact \<beta> = False\<close>
  \<open>tau_aact \<beta> \<Longrightarrow> vis_aact \<beta> = False\<close>
  by (simp add: tau_aact_def vis_aact_def)+

lemma vis_aact_unit_def:
  \<open>vis_aact \<beta> \<longleftrightarrow> strip_aact \<beta> = Vis ()\<close>
  by (simp add: vis_aact_def)

lemma vis_aact_simps[simp]:
  \<open>vis_aact (PL \<beta>) \<longleftrightarrow> vis_aact \<beta>\<close>
  \<open>vis_aact (PR \<beta>) \<longleftrightarrow> vis_aact \<beta>\<close>
  \<open>vis_aact AVis \<longleftrightarrow> True\<close>
  \<open>vis_aact TauBasic \<longleftrightarrow> False\<close>
  \<open>vis_aact TauINdetL \<longleftrightarrow> False\<close>
  \<open>vis_aact TauINdetR \<longleftrightarrow> False\<close>
  by (simp add: vis_aact_def)+

lemma tau_aact_simps[simp]:
  \<open>tau_aact (PL \<beta>) \<longleftrightarrow> tau_aact \<beta>\<close>
  \<open>tau_aact (PR \<beta>) \<longleftrightarrow> tau_aact \<beta>\<close>
  \<open>tau_aact AVis \<longleftrightarrow> False\<close>
  \<open>tau_aact TauBasic \<longleftrightarrow> True\<close>
  \<open>tau_aact TauINdetL \<longleftrightarrow> True\<close>
  \<open>tau_aact TauINdetR \<longleftrightarrow> True\<close>
  by (simp add: tau_aact_def)+

lemma all_aact_or_iff[simp]:
  \<open>(\<forall>\<beta>. vis_aact \<beta> \<or> P \<beta>) \<longleftrightarrow> (\<forall>\<beta>. tau_aact \<beta> \<longrightarrow> P \<beta>)\<close>
  \<open>(\<forall>\<beta>. tau_aact \<beta> \<or> P \<beta>) \<longleftrightarrow> (\<forall>\<beta>. vis_aact \<beta> \<longrightarrow> P \<beta>)\<close>
  using not_tau_aact_iff by blast+

lemma basic_tau_aact_then_vis_aact_false[simp]:
  \<open>basic_tau_aact \<alpha> \<Longrightarrow> vis_aact \<alpha> = False\<close>
  by (induct \<alpha>) simp+

lemma vis_aact_then_basic_tau_aact_false:
  \<open>vis_aact \<alpha> \<Longrightarrow> basic_tau_aact \<alpha> = False\<close>
  by (induct \<alpha>) simp+


subsection \<open> Parallel Opstep \<close>

text \<open>
  Unfortunately, because acts are often universally quantified,
  using a general type variable becomes prohibitively unwieldy.
  (Due to \<open>itself\<close> types and schematics type vars in \<open>induct\<close>.)
  Thus we just use unit.
\<close>
fun aopstep :: \<open>aact \<Rightarrow> 's pconfig \<Rightarrow> 's cpconfig \<Rightarrow> bool\<close> where
  \<open>aopstep \<beta> (h, Skip) s' \<longleftrightarrow> False\<close>
| \<open>aopstep \<beta> (h, c1 ;; c2) s' \<longleftrightarrow>
    \<beta> = TauBasic \<and> c1 = Skip \<and> s' = (Inl h, c2) \<or>
    (\<exists>h' c1'. aopstep \<beta> (h,c1) (h',c1') \<and> s' = (h', c1' ;; c2))\<close>
| \<open>aopstep \<beta> (h, c1 \<^bold>+ c2) s' \<longleftrightarrow>
    \<beta> = TauINdetL \<and> s' = (Inl h, c1) \<or>
    \<beta> = TauINdetR \<and> s' = (Inl h, c2)\<close>
| \<open>aopstep \<beta> (h, c1 \<box> c2) s' \<longleftrightarrow>
    (\<beta> = TauBasic \<and> c1 = Skip \<and> s' = (Inl h, c2) \<or>
      \<beta> = TauBasic \<and> c2 = Skip \<and> s' = (Inl h, c1) \<or>
      (if tau_aact \<beta> then
        (\<exists>h' c1'. s' = (h', c1' \<box> c2) \<and> aopstep \<beta> (h, c1) (h', c1')) \<or>
        (\<exists>h' c2'. s' = (h', c1 \<box> c2') \<and> aopstep \<beta> (h, c2) (h', c2'))
      else
        aopstep \<beta> (h, c1) s' \<or> aopstep \<beta> (h, c2) s'))\<close>
| \<open>aopstep \<beta> (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    \<beta> = TauBasic \<and> c1 = Skip \<and> c2 = Skip \<and> s' = (Inl h, Skip) \<or>
    (\<exists>\<beta>x. \<beta> = PL \<beta>x \<and> (\<exists>h' c1'. aopstep \<beta>x (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2))) \<or>
    (\<exists>\<beta>x. \<beta> = PR \<beta>x \<and> (\<exists>h' c2'. aopstep \<beta>x (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2')))\<close>
| \<open>aopstep \<beta> (h, DO c OD) s' \<longleftrightarrow>
      ((\<forall>\<alpha> h' c'. \<not> aopstep \<alpha> (h, c) (Inl h', c')) \<and>
        \<beta> = TauBasic \<and> s' = (Inl h, Skip)) \<or>
      (\<exists>h' c'.
        aopstep \<beta> (h, c) (Inl h', c') \<and>
        s' = (Inl h', c' ;; DO c OD)) \<or>
      ((\<exists>c'. aopstep \<beta> (h, c) (Inr (), c')) \<and>
        s' = (Inr (), DO c OD))\<close>
| \<open>aopstep \<beta> (h, Atomic ap aq) s' \<longleftrightarrow>
    (\<beta> = AVis \<and>
      (if ap h
        then \<exists>h'. aq h h' \<and> fst s' = Inl h' \<and> snd s' = Skip
        else fst s' = Inr () \<and> snd s' = Atomic ap aq))\<close>

lemmas aopstep_induct = aopstep.induct[case_names Skip Seq Indet Endet Par DoLoop Atom]
hide_fact aopstep.induct


paragraph \<open> Pretty parallel operational semantics \<close>

text \<open> \<open>sc\<close> can step to \<open>zc'\<close> \<close>
abbreviation pretty_aopstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sub>a _\<close> [60,0,60] 60) where
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>a zc' \<equiv> aopstep \<beta> sc zc'\<close>

text \<open> no steps from \<open>sc\<close> can take place, except perhaps crashes \<close>
abbreviation pretty_no_good_aopstep :: \<open>'s \<times> 's comm \<Rightarrow> bool\<close> (\<open>_ \<midarrow>'/\<rightarrow>\<^sub>a\<close> [60] 60) where
  \<open>sc \<midarrow>/\<rightarrow>\<^sub>a \<equiv> \<forall>\<beta> s' c'. \<not> aopstep \<beta> sc (Inl s', c')\<close>

text \<open> no steps from \<open>sc\<close> can take place at all \<close>
abbreviation pretty_no_aopstep :: \<open>'s \<times> 's comm \<Rightarrow> bool\<close> (\<open>_ \<midarrow>\<sslash>\<rightarrow>\<^sub>a\<close> [60] 60) where
  \<open>sc \<midarrow>\<sslash>\<rightarrow>\<^sub>a \<equiv> \<forall>\<beta> zc'. \<not> aopstep \<beta> sc zc'\<close>


subsubsection \<open> aopstep lemmas \<close>

lemma aopstep_iter_stepD:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>a zc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    zc' = (Inl s', c') \<Longrightarrow>
    (s, DO c OD) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl s', c' ;; DO c OD)\<close>
  by fastforce

lemma aopstep_tau_preserves_state:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>a zc' \<Longrightarrow> tau_aact \<beta> \<Longrightarrow> fst zc' = Inl (fst sc)\<close>
  by (induct rule: aopstep_induct)
    (fastforce split: if_splits simp add: tau_aact_def)+

lemma no_opstep_then_no_aopstep:
  \<open>sc \<midarrow>|\<rightarrow> \<Longrightarrow> sc \<midarrow>\<sslash>\<rightarrow>\<^sub>a\<close>
  apply (induct rule: aopstep_induct)
        apply (clarsimp split: if_splits; fail)
       apply (clarsimp simp add: all_conj_distrib disj_imp split: if_splits; fail)
      apply fastforce
     apply (clarsimp simp add: all_conj_distrib disj_imp split: if_splits)
     apply (subgoal_tac \<open>(\<forall>\<alpha> a b. \<not> (h, c1) \<midarrow>\<alpha>\<rightarrow> (a, b)) \<and> (\<forall>\<alpha> a b. \<not> (h, c2) \<midarrow>\<alpha>\<rightarrow> (a, b))\<close>)
      prefer 2
      apply (metis (full_types) unit.exhaust opstep_act_cases)
     apply (case_tac \<open>strip_aact \<beta>\<close>; metis not_tau_aact_iff)
    apply (clarsimp simp add: all_conj_distrib disj_imp split: if_splits; fail)
   apply (clarsimp simp add: all_conj_distrib split: if_splits, blast)
  apply (simp; fail)
  done

lemma no_aopstep_then_no_opstep:
  \<open>sc \<midarrow>\<sslash>\<rightarrow>\<^sub>a \<Longrightarrow> sc \<midarrow>|\<rightarrow>\<close>
  apply (induct rule: aopstep_induct)
        apply (clarsimp split: if_splits; fail)
       apply (clarsimp simp add: all_conj_distrib disj_imp split: if_splits; fail)
      apply fastforce
     apply (clarsimp simp add: all_conj_distrib disj_imp split: if_splits)
     apply (case_tac \<open>strip_aact \<beta>\<close>)
      apply (metis not_vis_aact_iff)
     apply (clarsimp, metis not_vis_aact_iff)
    apply (clarsimp, metis)
   apply (clarsimp, metis)
  apply force
  done

(*
lemma strip_aopstep:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>a zc' \<Longrightarrow> sc \<midarrow>strip_aact \<beta>\<rightarrow> zc'\<close>
  apply (induct \<beta> sc zc' rule: aopstep_induct)
        apply fastforce
       apply fastforce
      apply fastforce
  subgoal sorry
    apply fastforce
   apply clarsimp
(* TODO: haven't updated the original definition yet *)
(*
   apply (force simp add: no_aopstep_then_no_opstep split: if_splits)
*)
  subgoal sorry
  apply fastforce
  done
*)

lemma vis_aopstep_impl_atom:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>a zc' \<Longrightarrow>
    vis_aact \<beta> \<Longrightarrow>
    \<exists>p q.
      (p, q) \<in> head_atoms (snd sc) \<and>
      (p (fst sc) \<longrightarrow> (\<exists>s'. fst zc' = Inl s' \<and> q (fst sc) s')) \<and>
      (\<not> p (fst sc) \<longrightarrow> fst zc' = Inr ())\<close>
  apply (induct rule: aopstep_induct)
        apply fastforce
       apply fastforce
      apply fastforce
    (* Endet *)
     apply (clarsimp simp add: vis_aact_def tau_aact_def)
     apply (elim disjE)
        apply force
       apply force
      apply metis
     apply metis
    (* Parallel *)
    apply (clarsimp simp add: vis_aact_def tau_aact_def)
    apply (elim disjE)
      apply force
     apply (clarsimp, metis)
    apply (clarsimp, metis)
    (* DoLoop *)
   apply fastforce
    (* Atom *)
  apply fastforce
  done

lemma aopstep_then_aopstep_right_seqD:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>a zc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    zc' = (Inl s', c') \<Longrightarrow>
    (s, c ;; cx) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl s', c' ;; cx)\<close>
  by (induct \<beta> sc zc' arbitrary: s c s' c' rule: aopstep_induct) simp+

lemma aopstep_then_aopstep_right_endetD:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>a zc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    zc' = (Inl s', c') \<Longrightarrow>
    (vis_aact \<beta> \<longrightarrow> (s, c \<box> cb) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl s', c')) \<and>
    (tau_aact \<beta> \<longrightarrow> (s, c \<box> cb) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl s', c' \<box> cb))\<close>
  by (induct \<beta> sc zc' arbitrary: s c s' c' rule: aopstep_induct)
    (simp add: vis_aact_def tau_aact_def)+

lemma aopstep_then_aopstep_left_endetD:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>a zc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    zc' = (Inl s', c') \<Longrightarrow>
    (vis_aact \<beta> \<longrightarrow> (s, ca \<box> c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl s', c')) \<and>
    (tau_aact \<beta> \<longrightarrow> (s, ca \<box> c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl s', ca \<box> c'))\<close>
  by (induct \<beta> sc zc' arbitrary: s c s' c' rule: aopstep_induct)
    (simp add: vis_aact_def tau_aact_def)+

lemma aopstep_aact_cases:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>a zc' \<Longrightarrow>
    (sc \<midarrow>\<beta>\<rightarrow>\<^sub>a zc' \<Longrightarrow> vis_aact \<beta> \<Longrightarrow> P) \<Longrightarrow>
    (sc \<midarrow>\<beta>\<rightarrow>\<^sub>a zc' \<Longrightarrow> tau_aact \<beta> \<Longrightarrow> fst zc' = Inl (fst sc) \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  unfolding vis_aact_def tau_aact_def
  using not_vis_aact_iff aopstep_tau_preserves_state tau_aact_def vis_aact_unit_def by blast

lemma aopstep_no_new_atoms:
  \<open>(s, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (ms', c') \<Longrightarrow> all_atoms c' \<subseteq> all_atoms c\<close>
  by (induct c arbitrary: \<alpha> c') (fastforce split: if_splits)+


subsubsection \<open> Self-aopstep Impossible \<close>

lemma comm_self_containment_impossible[simp]:
  \<open>c1 ;; c2 \<le> c1 \<longleftrightarrow> False\<close>
  \<open>c1 ;; c2 \<le> c2 \<longleftrightarrow> False\<close>
  \<open>c1 \<parallel> c2 \<le> c1 \<longleftrightarrow> False\<close>
  \<open>c1 \<parallel> c2 \<le> c2 \<longleftrightarrow> False\<close>
  \<open>c1 \<^bold>+ c2 \<le> c1 \<longleftrightarrow> False\<close>
  \<open>c1 \<^bold>+ c2 \<le> c2 \<longleftrightarrow> False\<close>
  \<open>c1 \<box> c2 \<le> c1 \<longleftrightarrow> False\<close>
  \<open>c1 \<box> c2 \<le> c2 \<longleftrightarrow> False\<close>
  \<open>DO c OD \<le> c \<longleftrightarrow> False\<close>
  using less_comm_simps_right
  by (fastforce dest: leD)+

fun eval_focus :: \<open>'a comm \<Rightarrow> 'a comm set\<close> where
  \<open>eval_focus Skip = {Skip}\<close>
| \<open>eval_focus (ca ;; cb) = (if ca = Skip then {ca ;; cb} else eval_focus ca)\<close>
| \<open>eval_focus (ca \<parallel> cb) = (eval_focus ca \<union> eval_focus cb)\<close>
| \<open>eval_focus (ca \<^bold>+ cb) = {ca \<^bold>+ cb}\<close>
| \<open>eval_focus (ca \<box> cb) = eval_focus ca \<union> eval_focus cb\<close>
| \<open>eval_focus \<langle>p, q\<rangle> = {\<langle>p, q\<rangle>}\<close>
| \<open>eval_focus (DO c OD) = {c, DO c OD}\<close>

inductive endet_expansion :: \<open>'a comm \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  eexp_reflI[intro!]: \<open>endet_expansion c c\<close>
| eexp_leftI[intro]: \<open>endet_expansion c ca \<Longrightarrow> endet_expansion c (ca \<box> cb)\<close>
| eexp_rightI[intro]: \<open>endet_expansion c cb \<Longrightarrow> endet_expansion c (ca \<box> cb)\<close>

inductive_cases endet_expansion_right_SkipE[elim!]: \<open>endet_expansion c Skip\<close>
inductive_cases endet_expansion_right_SeqE[elim!]: \<open>endet_expansion c (ca ;; cb)\<close>
inductive_cases endet_expansion_right_IndetE[elim!]: \<open>endet_expansion c (ca \<^bold>+ cb)\<close>
inductive_cases endet_expansion_right_EndetE[elim]: \<open>endet_expansion c (ca \<box> cb)\<close>
inductive_cases endet_expansion_right_ParE[elim!]: \<open>endet_expansion c (ca \<parallel> cb)\<close>
inductive_cases endet_expansion_right_AtomE[elim!]: \<open>endet_expansion c \<langle>p, q\<rangle>\<close>
inductive_cases endet_expansion_right_IterE[elim!]: \<open>endet_expansion c (DO cx OD)\<close>

lemma endet_expansion_subcomm_antisym:
  \<open>endet_expansion ca cb \<Longrightarrow> cb \<le> ca \<Longrightarrow> ca = cb\<close>
  apply (induct cb arbitrary: ca)
        apply force
       apply force
      apply force
     apply force
    apply (metis comm_self_containment_impossible(7,8) less_eq_comm_leftD(7,8)
      endet_expansion_right_EndetE)
   apply force
  apply force
  done

lemma endet_expansion_indet_left[simp]:
  \<open>endet_expansion (c ;; cb) c = False\<close>
  \<open>endet_expansion (ca ;; c) c = False\<close>
  \<open>endet_expansion (c \<parallel> cb) c = False\<close>
  \<open>endet_expansion (ca \<parallel> c) c = False\<close>
  \<open>endet_expansion (c \<^bold>+ cb) c = False\<close>
  \<open>endet_expansion (ca \<^bold>+ c) c = False\<close>
  \<open>endet_expansion (c \<box> cb) c = False\<close>
  \<open>endet_expansion (ca \<box> c) c = False\<close>
  \<open>endet_expansion (DO c OD) c = False\<close>
  using endet_expansion_subcomm_antisym
  by fastforce+

lemma endet_expansion_endet_leftD:
  \<open>endet_expansion (ca \<box> cb) c' \<Longrightarrow> endet_expansion ca c'\<close>
  \<open>endet_expansion (ca \<box> cb) c' \<Longrightarrow> endet_expansion cb c'\<close>
  by (induct c') blast+

lemma self_aopstep_endet_cluster_impossible:
  \<open>endet_expansion c c' \<Longrightarrow> (s, c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl s', c') = False\<close>
  apply (induct c arbitrary: \<beta> c')
        apply force
       apply force
      apply force
     apply force
    apply clarsimp
    apply (intro conjI impI allI)
           apply force
          apply force
         apply (metis comm.inject(4) eexp_reflI endet_expansion_endet_leftD(1)
      endet_expansion_indet_left(8) endet_expansion_right_EndetE)
        apply (metis comm.inject(4) eexp_reflI endet_expansion_endet_leftD(2)
      endet_expansion_indet_left(7) endet_expansion_right_EndetE)
       apply force
      apply force
     apply (meson endet_expansion_endet_leftD(1); fail)
    apply (meson endet_expansion_endet_leftD(2); fail)
   apply force
  apply force
  done

lemma self_aopstep_impossible:
  \<open>(s, c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl s', c) = False\<close>
  by (simp add: eexp_reflI self_aopstep_endet_cluster_impossible)


lemma aopstep_endet_skip_then:
  \<open>(s, c \<box> Skip) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl s', c) \<Longrightarrow> tau_aact \<beta> \<and> s' = s\<close>
  \<open>(s, Skip \<box> c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl s', c) \<Longrightarrow> tau_aact \<beta> \<and> s' = s\<close>
  by (metis fst_conv not_tau_aact_iff aopstep.simps(1,4) strip_aact.simps(1) sum.inject(1)
      tau_aact_def aopstep_aact_cases self_aopstep_impossible)+


subsection \<open> parallel-annotated opsteps \<close>

inductive aopsteps
  :: \<open>_ list \<Rightarrow>
      ('l \<times> 's) \<times> ('l \<times> 's) comm \<Rightarrow>
      ('l \<times> 's + unit) \<times> ('l \<times> 's) comm \<Rightarrow>
      bool\<close>
  where
  aopsteps_nil[intro!]:
  \<open>fst zc' = Inl (fst sc) \<Longrightarrow> snd zc' = snd sc \<Longrightarrow> aopsteps [] sc zc'\<close>
| aopsteps_cons[intro!]:
  \<open>aopstep \<gamma> sc (Inl s', c') \<Longrightarrow>
    aopsteps \<gamma>s (s', c') zc'' \<Longrightarrow>
    aopsteps (\<gamma> # \<gamma>s) sc zc''\<close>

inductive_cases aopsteps_nilE[elim!]: \<open>aopsteps [] sc zc'\<close>
inductive_cases aopsteps_consE[elim!]: \<open>aopsteps (\<gamma> # \<gamma>s) sc zc'\<close>

abbreviation aopsteps_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_\<rightarrow>\<^sub>a\<^sup>* _\<close> [50, 0, 50]) where
  \<open>sc \<midarrow>\<gamma>s\<rightarrow>\<^sub>a\<^sup>* zc' \<equiv> aopsteps \<gamma>s sc zc'\<close>

lemma aopsteps_simps[simp]:
  \<open>aopsteps [] sc zc' \<longleftrightarrow> fst zc' = Inl (fst sc) \<and> snd zc' = snd sc\<close>
  \<open>aopsteps (\<gamma> # \<gamma>s) sc zc'' \<longleftrightarrow>
    (\<exists>s' c'. aopstep \<gamma> sc (Inl s', c') \<and> aopsteps \<gamma>s (s', c') zc'')\<close>
  by force+


section \<open> Extended step \<close>

datatype 'a eact =
  Env
  | Loc \<open>'a\<close>
(*
  | Crash 'a

lemma eact_eq_iff[simp]:
  \<open>Env = Crash ac \<longleftrightarrow> False\<close>
  \<open>Crash ac = Env \<longleftrightarrow> False\<close>
  \<open>Loc \<rho> = Crash ac \<longleftrightarrow> False\<close>
  \<open>Crash ac = Loc \<rho> \<longleftrightarrow> False\<close>
  by force+
*)

definition
  \<open>estep step r F \<equiv>
    \<lambda>\<beta>. case \<beta> of Env \<Rightarrow>
      (\<lambda>((xl,xs),c) (mx', c').
        c' = c \<and>
        (\<exists>xs'.
          mx' = Inl (xl, xs') \<and>
          r xs xs' \<and>
          (\<exists>xf. F (xf, xs) \<and> xl ## xf) \<and>
          (\<exists>xf'. F (xf', xs') \<and> xl ## xf')))
      | Loc \<alpha> \<Rightarrow>
        (\<lambda>((xl,xs),c) (mx',c').
          \<exists>xf.
            F (xf, xs) \<and>
            xl ## xf \<and>
            (\<exists>mxf'.
              step \<alpha> ((xl + xf,xs),c) (mxf', c') \<and>
              ((\<exists>xl' xlf' xs'.
                  mxf' = Inl (xlf', xs') \<and>
                  F (xf, xs') \<and>
                  xl' ## xf \<and>
                  xlf' = xl' + xf \<and>
                  mx' = Inl (xl', xs')) \<or>
                mxf' = Inr () \<and> mx' = Inr ())))
      \<comment> \<open>| Crash \<beta> \<Rightarrow>
        (\<lambda>((xl,xs),c) (mx',c').
          \<exists>xf.
            F (xf, xs) \<and>
            xl ## xf \<and>
            aopstep \<beta> ((xl + xf,xs),c) (Inr (), c') \<and>
            mx' = Inr ())\<close>\<close>

paragraph \<open> Pretty extended extended opsem \<close>

abbreviation pretty_estep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e _\<close> [60,0,0,0,60] 60) where
  \<open>sc \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e zc' \<equiv> estep opstep r F \<gamma> sc zc'\<close>

abbreviation pretty_no_estep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, _ '/\<rightarrow>\<^sub>e\<close> [60, 0, 0] 60) where
  \<open>sc \<midarrow>r, F /\<rightarrow>\<^sub>e \<equiv> \<forall>\<gamma>. \<forall>zc'::(_+unit)\<times>_. \<not> estep opstep r F \<gamma> sc zc'\<close>

abbreviation pretty_eastep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e\<^sub>a _\<close> [60,0,0,0,60] 60) where
  \<open>sc \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a zc' \<equiv> estep aopstep r F \<gamma> sc zc'\<close>

abbreviation prsetty_no_eastep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, _ '/\<rightarrow>\<^sub>e\<^sub>a\<close> [60, 0, 0] 60) where
  \<open>sc \<midarrow>r, F /\<rightarrow>\<^sub>e\<^sub>a \<equiv> \<forall>\<gamma>. \<forall>zc'::(_+unit)\<times>_. \<not> estep aopstep r F \<gamma> sc zc'\<close>


subsection \<open> Lemmas about estep \<close>

lemma estep_simps[simp]:
  \<open>estep step r F Env sc zc' =
    (snd zc' = snd sc \<and>
      (\<exists>xs'.
        fst zc' = Inl (fst (fst sc), xs') \<and>
        r (snd (fst sc)) xs' \<and>
        (\<exists>xf. F (xf, snd (fst sc)) \<and> fst (fst sc) ## xf) \<and>
        (\<exists>xf'. F (xf', xs') \<and> fst (fst sc) ## xf')))\<close>
  \<open>estep step r F (Loc \<alpha>) sc zc' =
    (\<exists>xf.
      F (xf, snd (fst sc)) \<and>
      fst (fst sc) ## xf \<and>
      (\<exists>mxf'.
        step \<alpha> ((fst (fst sc) + xf, snd (fst sc)), snd sc) (mxf', snd zc') \<and>
        ((\<exists>xl' xs'.
          xl' ## xf \<and>
          mxf' = Inl (xl' + xf, xs') \<and>
          F (xf, xs') \<and>
          fst zc' = Inl (xl', xs')) \<or>
        mxf' = Inr () \<and> fst zc' = Inr ())))\<close>
(* \<open>estep r F (Crash \<beta>) sc zc' =
    (\<exists>xf.
      F (xf, snd (fst sc)) \<and>
      fst (fst sc) ## xf \<and>
      aopstep \<beta> ((fst (fst sc) + xf, snd (fst sc)), snd sc) (Inr (), snd zc') \<and>
      fst zc' = Inr ())\<close> *)
  by (force simp add: estep_def split: sum.splits unit.splits prod.splits)+

lemma estepE[elim]:
  \<open>estep step r F \<gamma> sc zc' \<Longrightarrow>
    (\<And>xl xs c xs' xf xf'.
      sc = ((xl, xs), c) \<Longrightarrow>
      zc' = (Inl (xl, xs'), c) \<Longrightarrow>
      r xs xs' \<Longrightarrow>
      F (xf, xs) \<Longrightarrow>
      xl ## xf \<Longrightarrow>
      F (xf', xs') \<Longrightarrow>
      xl ## xf' \<Longrightarrow>
      P) \<Longrightarrow>
    (\<And>\<beta> xl xs c mx' c' xf mxf'.
      \<gamma> = Loc \<beta> \<Longrightarrow>
      sc = ((xl,xs),c) \<Longrightarrow>
      zc' = (mx',c') \<Longrightarrow>
      F (xf, xs) \<Longrightarrow>
      xl ## xf \<Longrightarrow>
      step \<beta> ((xl + xf,xs),c) (mxf', c') \<and>
      (\<exists>xl' xlf' xs'.
        mxf' = Inl (xlf', xs') \<and>
        F (xf, xs') \<and>
        xl' ## xf \<and>
        xlf' = xl' + xf \<and>
        mx' = Inl (xl', xs')) \<or>
      (mxf' = Inr () \<and> mx' = Inr()) \<Longrightarrow>
      P) \<Longrightarrow>
    P\<close>
  by (cases sc, cases zc', cases \<gamma>; force)

lemma estep_def':
  \<open>estep step r F \<gamma> sc zc' \<longleftrightarrow>
    \<gamma> = Env \<and>
      snd zc' = snd sc \<and>
      (\<exists>xs'.
        fst zc' = Inl (fst (fst sc), xs') \<and>
        r (snd (fst sc)) xs' \<and>
        (\<exists>xf. F (xf, snd (fst sc)) \<and> fst (fst sc) ## xf) \<and>
        (\<exists>xf'. F (xf', xs') \<and> fst (fst sc) ## xf')) \<or>
    (\<exists>\<beta>. \<gamma> = Loc \<beta> \<and>
      (\<exists>xf.
      F (xf, snd (fst sc)) \<and>
      fst (fst sc) ## xf \<and>
      (\<exists>mxf'.
        step \<beta> ((fst (fst sc) + xf, snd (fst sc)), snd sc) (mxf', snd zc') \<and>
        ((\<exists>xl' xs'.
          xl' ## xf \<and>
          mxf' = Inl (xl' + xf, xs') \<and>
          F (xf, xs') \<and>
          fst zc' = Inl (xl', xs')) \<or>
        (mxf' = Inr () \<and> fst zc' = Inr ())))))\<close>
(*  by (force simp add: estep_def split: sum.splits unit.splits prod.splits) *)
  oops

lemma estep_skip_iff[simp]:
  \<open>\<forall>\<alpha> s msc'. \<not> step \<alpha> (s, Skip) msc' \<Longrightarrow>
    estep step r F \<alpha>e (s, Skip) zc' \<longleftrightarrow>
    \<alpha>e = Env \<and>
    (\<exists>xs'.
      zc' = (Inl (fst s, xs'), Skip) \<and>
      fst zc' = Inl (fst s, xs') \<and>
      r (snd s) xs' \<and>
      (\<exists>xf. F (xf, snd s) \<and> fst s ## xf) \<and>
      (\<exists>xf'. F (xf', xs') \<and> fst s ## xf'))\<close>
  unfolding estep_def
  by (cases \<alpha>e; force simp add: estep_def split: prod.splits)+

lemma estep_crash_iff[simp]:
  \<open>estep step r F \<gamma> sc (Inr (), c') \<longleftrightarrow>
    (\<exists>\<alpha>. \<gamma> = Loc \<alpha> \<and>
      (\<exists>xf.
        F (xf, snd (fst sc)) \<and>
        fst (fst sc) ## xf \<and>
        step \<alpha> ((fst (fst sc) + xf, snd (fst sc)), snd sc) (Inr (), c')))\<close>
  by (clarsimp simp add: estep_def split: prod.splits eact.splits)


lemma eastep_then_eastep_right_par:
  \<open>(s, c) \<midarrow>r, F, \<alpha>e\<rightarrow>\<^sub>e\<^sub>a (Inl s', c') \<Longrightarrow>
    (s, c \<parallel> cb) \<midarrow>r, F, map_eact PL \<alpha>e\<rightarrow>\<^sub>e\<^sub>a (Inl s', c' \<parallel> cb)\<close>
  unfolding estep_def
  by (clarsimp split: prod.splits eact.splits)

lemma eastep_then_eastep_left_par:
  \<open>(s, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (Inl s', c') \<Longrightarrow>
    (s, ca \<parallel> c) \<midarrow>r, F, map_eact PR \<gamma>\<rightarrow>\<^sub>e\<^sub>a (Inl s', ca \<parallel> c')\<close>
  unfolding estep_def
  by (clarsimp split: prod.splits eact.splits)

lemma eastep_then_eastep_right_endet:
  \<open>(s, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (Inl s', c') \<Longrightarrow>
    (\<forall>\<beta>. \<gamma> = Env \<longrightarrow> (s, c \<box> cb) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (Inl s', c' \<box> cb)) \<and>
    (\<forall>\<beta>. \<gamma> = Loc \<beta> \<longrightarrow>
      (vis_aact \<beta> \<longrightarrow> (s, c \<box> cb) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (Inl s', c')) \<and>
      (tau_aact \<beta> \<longrightarrow> (s, c \<box> cb) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (Inl s', c' \<box> cb)))\<close>
  unfolding estep_def
  by (force split: prod.splits simp add: vis_aact_def tau_aact_def)

lemma eastep_then_eastep_left_endet:
  \<open>(s, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (Inl s', c') \<Longrightarrow>
    (\<forall>\<beta>. \<gamma> = Env \<longrightarrow> (s, ca \<box> c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (Inl s', ca \<box> c')) \<and>
    (\<forall>\<beta>. \<gamma> = Loc \<beta> \<longrightarrow>
      (vis_aact \<beta> \<longrightarrow> (s, ca \<box> c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (Inl s', c')) \<and>
      (tau_aact \<beta> \<longrightarrow> (s, ca \<box> c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (Inl s', ca \<box> c')))\<close>
  unfolding estep_def
  by (force split: prod.splits simp add: vis_aact_def tau_aact_def)

lemma estep_then_estep_doloop:
  \<open>(s, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (Inl s', c') \<Longrightarrow>
    (\<forall>\<beta>. \<gamma> = Env \<longrightarrow> (s, DO c OD) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (Inl s', DO c' OD)) \<and>
    (\<forall>\<beta>. \<gamma> = Loc \<beta> \<longrightarrow> (s, DO c OD) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (Inl s', c' ;; DO c OD))\<close>
  unfolding estep_def
  by (force split: prod.splits)


subsection \<open> Extended steps \<close>

inductive esteps :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> where
  nil: \<open>c' = c \<Longrightarrow> z' = Inl s \<Longrightarrow> esteps step r F [] (s, c) (z', c')\<close>
| crashstep: \<open>
  estep step r F \<gamma> (s, c) (Inr (), c'') \<Longrightarrow>
    z'' = Inr () \<Longrightarrow>
    esteps step r F [\<gamma>] (s, c) (z'', c'')\<close>
| opstep: \<open>
  estep step r F \<gamma> (s, c) (Inl s', c') \<and>
  esteps step r F \<gamma>s (s', c') (z'', c'') \<Longrightarrow>
  esteps step r F (\<gamma> # \<gamma>s) (s, c) (z'', c'')\<close>

inductive_cases esteps_nilE[elim!]: \<open>esteps step r F [] sc zc'\<close>
inductive_cases esteps_consE[elim]: \<open>esteps step r F (\<gamma> # \<gamma>s) sc zc'\<close>

abbreviation esteps_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e\<^sup>* _\<close> [50, 0, 0, 50])
  where
    \<open>sc \<midarrow>r, F, \<gamma>s\<rightarrow>\<^sub>e\<^sup>* zc' \<equiv> esteps opstep r F \<gamma>s sc zc'\<close>

abbreviation easteps_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e\<^sub>a\<^sup>* _\<close> [50, 0, 0, 50])
  where
    \<open>sc \<midarrow>r, F, \<gamma>s\<rightarrow>\<^sub>e\<^sub>a\<^sup>* zc' \<equiv> esteps aopstep r F \<gamma>s sc zc'\<close>


section \<open> Double Step \<close>

inductive dstep
  :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
        (('l::pre_perm_alg \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow>
      (('l \<times> 's) comm \<Rightarrow> ('l \<times> 's) comm \<Rightarrow> bool) \<Rightarrow>
        _ eact \<times> _ eact \<Rightarrow>
        (('l \<times> 's) \<times> ('l \<times> 's) comm) \<times> (('l \<times> 's) \<times> ('l \<times> 's) comm) \<Rightarrow>
        (('l \<times> 's + unit) \<times> ('l \<times> 's) comm) \<times> (('l \<times> 's + unit) \<times> ('l \<times> 's) comm) \<Rightarrow> bool\<close>
  where
  dstep_env:
    \<open>RR (sx,sy) (sx',sy') \<Longrightarrow>
      CC cx cy \<Longrightarrow>
      dstep RR FF CC (Env, Env)
        (((lx,sx),cx), ((ly,sy),cy))
        ((Inl (lx, sx'),cx), (Inl (ly,sy'),cy))\<close>
| dstep_local:
  \<open>FF ((fx,fy),(sx,sy)) \<Longrightarrow>
    CC cx cy \<Longrightarrow>
    \<comment> \<open> left steps \<close>
    lx ## fx \<Longrightarrow>
    aopsteps \<rho>x ((lx+fx,sx),cx) (Inl (lx'+fx,sx'),cx') \<Longrightarrow>
    \<comment> \<open> right steps \<close>
    ly ## fy \<Longrightarrow>
    aopsteps \<rho>y ((ly+fy,sy),cy) (Inl (ly'+fy,sy'),cy') \<Longrightarrow>
    \<rho>x \<noteq> [] \<or> \<rho>y \<noteq> [] \<Longrightarrow>
    dstep RR FF CC (Loc \<rho>x, Loc \<rho>y)
      (((lx,sx),cx), ((ly,sy),cy))
      ((Inl (lx',sx'), cx'), (Inl (ly',sy'), cy'))\<close>

inductive_cases dstep_EnvXE[elim!]: \<open>dstep RR FF CC (Env, X) ss zz'\<close>
inductive_cases dstep_XEnvE[elim!]: \<open>dstep RR FF CC (X, Env) ss zz'\<close>

inductive_cases dstep_LocXE[elim!]: \<open>dstep RR FF CC (Loc \<rho>x, X) ss zz'\<close>
inductive_cases dstep_XLocE[elim!]: \<open>dstep RR FF CC (X, Loc \<rho>y) ss zz'\<close>


abbreviation pretty_dstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ =_, _, _, _\<Rightarrow> _\<close> [55, 0,0,0,0, 55]) where
  \<open>cc =RR, FF, CC, \<gamma>\<gamma>\<Rightarrow> cc' \<equiv> dstep RR FF CC \<gamma>\<gamma> cc cc'\<close>

inductive dsteps :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> where
  dsteps_nil:
  \<open>zz' = ((Inl (fst (fst ss)), snd (fst ss)), (Inl (fst (snd ss)), snd (snd ss))) \<Longrightarrow>
    dsteps RR FF CC ([], []) ss zz'\<close>
| dsteps_step:
  \<open>dstep RR FF CC (\<alpha>\<^sub>ex, \<alpha>\<^sub>ey) ss ((Inl sx', cy'), (Inl sy', cy')) \<Longrightarrow>
    dsteps RR FF CC (\<rho>x, \<rho>y) ((sx', cy'), (sy', cy')) zz'' \<Longrightarrow>
    dsteps RR FF CC (\<alpha>\<^sub>ex # \<rho>x, \<alpha>\<^sub>ey # \<rho>y) ss zz''\<close>

inductive_cases dsteps_nilE[elim!]: \<open>dsteps RR FF CC ([], []) sc zc'\<close>
inductive_cases dsteps_cons_leftE[elim]: \<open>dsteps RR FF CC (\<alpha>\<^sub>ex # \<rho>x, \<rho>y) sc zc'\<close>
inductive_cases dsteps_cons_rightE[elim]: \<open>dsteps RR FF CC (\<rho>x, \<alpha>\<^sub>ey # \<rho>y) sc zc'\<close>

abbreviation dsteps_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ =_, _, _, _\<Rightarrow>\<^sup>* _\<close> [50, 0, 0, 0, 0, 50])
  where
    \<open>ss =RR, FF, CC, \<rho>xy\<Rightarrow>\<^sup>* zz' \<equiv> dsteps RR FF CC \<rho>xy ss zz'\<close>


section \<open> (Strong) Non-interference \<close>

definition
  \<open>rely_obs_safe \<oo> RR \<equiv>
    \<forall>hlx hly hsx hsy hsx' hsy'.
      \<bbbA> \<oo> ((hlx,hsx), (hly,hsy)) \<longrightarrow>
      RR (hsx, hsy) (hsx', hsy') \<longrightarrow>
      \<bbbA> \<oo> ((hlx, hsx'), (hly, hsy'))\<close>


definition                                                                      
  \<open>head_obs_determ \<oo> c \<equiv>
    (\<forall>px qx. (px,qx) \<in> head_atoms c \<longrightarrow>
      (\<forall>py qy. (py,qy) \<in> head_atoms c \<longrightarrow>
        (\<forall>x. px x \<longrightarrow> Ex (qx x) \<longrightarrow>
          (\<forall>y. py y \<longrightarrow> Ex (qy y) \<longrightarrow>
            \<bbbA> \<oo> (x,y) \<longrightarrow>
            px = py \<and> qx = qy))))\<close>

definition                                                                      
  \<open>head_step_obs_safe \<oo> c \<equiv> \<lambda>(x, y).
      \<bbbA> \<oo> (x, y) \<longrightarrow>
        (\<forall>p q x'. (p,q) \<in> head_atoms c \<longrightarrow> p x \<longrightarrow> q x x' \<longrightarrow> \<bbbA> \<oo> (x', y)) \<and>
        (\<forall>p q y'. (p,q) \<in> head_atoms c \<longrightarrow> p y \<longrightarrow> q y y' \<longrightarrow> \<bbbA> \<oo> (x, y')) \<and>
        (\<forall>px qx. (px,qx) \<in> head_atoms c \<longrightarrow>
          (\<forall>py qy. (py,qy) \<in> head_atoms c \<longrightarrow>
          (\<forall>x'. px x \<longrightarrow> qx x x' \<longrightarrow>
          (\<forall>y'. py y \<longrightarrow> qy y y' \<longrightarrow>
            \<bbbA> \<oo> (x',y')))))\<close>


subsection \<open> Determinism \<close>

subsubsection \<open> head domain \<close>

definition                                                                      
  \<open>heads_dom c \<equiv> \<Squnion>{p \<sqinter> pre_state q|p q. (p,q) \<in> head_atoms c}\<close>

lemma heads_domD:
  \<open>(p, q) \<in> head_atoms c \<Longrightarrow> p \<sqinter> pre_state q \<le> heads_dom c\<close>
  unfolding heads_dom_def
  by blast


subsubsection \<open> head could crash domain \<close>

definition                                                                      
  \<open>heads_ccrash_dom c \<equiv> \<Squnion>{-p|p q. (p,q) \<in> head_atoms c}\<close>

lemma heads_ccrash_domD:
  \<open>(p, q) \<in> head_atoms c \<Longrightarrow> -p \<le> heads_ccrash_dom c\<close>
  unfolding heads_ccrash_dom_def
  by blast


subsubsection \<open> security deterministic endent \<close>

definition
  \<open>sec_head_determ c \<equiv> \<lambda>(sx,sy).
    (\<forall>ca cb. ca \<box> cb \<in> all_subcomm_eq c \<longrightarrow>
      head_atomic ca \<and> head_atomic cb \<and>
      \<not> (heads_dom ca sx \<and> heads_dom cb sy) \<and>
      \<not> (heads_dom cb sx \<and> heads_dom ca sy) \<and>
      \<not> (heads_ccrash_dom ca sx \<and> heads_ccrash_dom cb sy) \<and>
      \<not> (heads_ccrash_dom cb sx \<and> heads_ccrash_dom ca sy)) \<and>
    (\<forall>ca. DO ca OD \<in> all_subcomm_eq c \<longrightarrow>
      head_atomic ca \<and>
      heads_dom ca sx = heads_dom ca sy \<and>
      heads_ccrash_dom ca sx = heads_ccrash_dom ca sy)\<close>

lemma sec_head_determ_comm_simps[simp]:
  \<open>sec_head_determ Skip ss = True\<close>
  \<open>sec_head_determ (c1 ;; c2) ss = (sec_head_determ c1 ss \<and> sec_head_determ c2 ss)\<close>
  \<open>sec_head_determ (c1 \<parallel> c2) ss = (sec_head_determ c1 ss \<and> sec_head_determ c2 ss)\<close>
  \<open>sec_head_determ (c1 \<^bold>+ c2) ss = (sec_head_determ c1 ss \<and> sec_head_determ c2 ss)\<close>
  \<open>sec_head_determ (ca \<box> cb) (sx, sy) =
    (head_atomic ca \<and> head_atomic cb \<and>
      \<not> (heads_dom ca sx \<and> heads_dom cb sy) \<and>
      \<not> (heads_dom cb sx \<and> heads_dom ca sy) \<and>
      \<not> (heads_ccrash_dom ca sx \<and> heads_ccrash_dom cb sy) \<and>
      \<not> (heads_ccrash_dom cb sx \<and> heads_ccrash_dom ca sy) \<and>
      sec_head_determ ca (sx, sy) \<and>
      sec_head_determ cb (sx, sy))\<close>
  \<open>sec_head_determ \<langle>p, q\<rangle> ss = True\<close>
  \<open>sec_head_determ (DO ca OD) (sx, sy) =
    (head_atomic ca \<and>
      \<not> (heads_dom ca sx \<and> \<not> heads_dom ca sy) \<and>
      \<not> (\<not> heads_dom ca sx \<and> heads_dom ca sy) \<and>
      \<not> (heads_ccrash_dom ca sx \<and> \<not> heads_ccrash_dom ca sy) \<and>
      \<not> (\<not> heads_ccrash_dom ca sx \<and> heads_ccrash_dom ca sy) \<and>
      sec_head_determ ca (sx, sy))\<close>
  unfolding sec_head_determ_def
  by (clarsimp simp add: all_conj_distrib split: prod.splits; fast)+


section \<open> Noninterference \<close>

definition doubled_atom :: \<open>
    (('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow>
    (('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> ('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow>
    bool\<close>
  where
    \<open>doubled_atom pp qq \<equiv>
      (\<exists>p. pp = liftP p \<circ> exch4) \<and> (\<exists>q. qq = liftR q \<circ>\<^sub>2 exch4)\<close>

lemma all_doubled_atom_liftC_iff[simp]:
  \<open>all_atom_comm doubled_atom (liftC c)\<close>
  by (induct c)
    (force simp add: doubled_atom_def)+


section \<open> Double step aggregation lemmas \<close>

lemma two_aopstep_crash_then_same_post_comm:
  \<open>((sxl, sxs), c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inr (), cx') \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inr (), cy') \<Longrightarrow>
    sec_head_determ c ((sxl, sxs), (syl, sys)) \<Longrightarrow>
    cx' = cy'\<close>
  apply (induct c arbitrary: sxl syl sxs sys cx' cy' \<beta>)
        apply force
       apply force
      apply force
     apply force
    apply (clarsimp simp del: disj_not1 split: if_splits)
     apply (metis Inr_not_Inl aopstep_tau_preserves_state split_pairs2)
    apply (elim disjE[of \<open>aopstep _ _ _\<close>]) (* 1 \<rightarrow> 4 *)
    (* 1/1 *)
       apply (simp add: vis_tau_aact_incompatible; fail)
    (* 1/2 *)
      apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
      apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
      apply (simp add: heads_ccrash_dom_def vis_tau_aact_incompatible)
      apply (metis ComplI Collect_neg_eq mem_Collect_eq)
    (* 2/1 *)
     apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
     apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
     apply (simp add: heads_ccrash_dom_def vis_tau_aact_incompatible)
     apply (metis ComplI Collect_neg_eq mem_Collect_eq)
    (* 2/2 *)
    apply (simp add: vis_tau_aact_incompatible; fail)
   apply (clarsimp split: if_splits; fail)
  apply force
  done

lemma double_step_crashI:
  \<open>((sxl, sxs), c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inr (), c') \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inr (), c') \<Longrightarrow>
    sec_head_determ c ((sxl, sxs), (syl, sys)) \<Longrightarrow>
    (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inr (), liftC c')\<close>
  apply (induct c arbitrary: sxl syl sxs sys c' \<beta>)
        apply force
       apply force
    (* parallel *)
      apply fastforce
    (* indet *)
     apply force
    (* endet *)
    apply (clarsimp split: if_splits)
     apply (metis Inl_Inr_False fst_conv aopstep_tau_preserves_state)
    apply (elim disjE) (* 1 \<rightarrow> 4 *)
    (** 1/1 *)
       apply (simp add: vis_tau_aact_incompatible; fail)
    (** 1/2 *)
      apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
      apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
      apply (simp add: heads_ccrash_dom_def vis_tau_aact_incompatible)
      apply (metis ComplI Collect_neg_eq mem_Collect_eq)
    (** 2/1 *)
     apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
     apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
     apply (simp add: heads_ccrash_dom_def vis_tau_aact_incompatible)
     apply (metis ComplI Collect_neg_eq mem_Collect_eq)
    (** 2/2 *)
    apply (simp add: vis_tau_aact_incompatible; fail)
    (* atom *)
   apply (clarsimp split: if_splits; fail)
    (* do-loop *)
  apply clarsimp
  apply (metis two_aopstep_crash_then_same_post_comm)
  done

lemma double_no_stepI:
  fixes sxl syl :: \<open>'l::pre_perm_alg\<close>
    and sxs sys :: \<open>'s\<close>
  shows
    \<open>((sxl, sxs), c) \<midarrow>\<sslash>\<rightarrow>\<^sub>a \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<sslash>\<rightarrow>\<^sub>a \<Longrightarrow>
    (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>\<sslash>\<rightarrow>\<^sub>a\<close>
  apply (induct c arbitrary: sxl syl sxs sys)
    (* Skip *)
        apply force
    (* Seq *)
       apply (clarsimp simp add: liftC_rev_iff, metis)
    (* Parallel *)
      apply simp
      apply (intro allI conjI impI)
        apply (metis liftC_rev_iff(1))
       apply metis
      apply metis
    (* INDet *)
     apply (simp, fast)
    (* ENDet *)
    apply (clarsimp simp add: liftC_rev_iff, metis)
    (* Atom *)
   apply (simp, fastforce)
    (* DoLoop *)
  apply (simp, metis)
  done

lemma double_no_good_stepI:
  fixes sxl syl :: \<open>'l::pre_perm_alg\<close>
    and sxs sys :: \<open>'s\<close>
  shows
    \<open>((sxl, sxs), c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow>
    ((syl, sys), c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow>
    (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  apply (induct c arbitrary: sxl syl sxs sys)
    (* Skip *)
        apply force
    (* Seq *)
       apply (clarsimp simp add: liftC_rev_iff, metis)
    (* Parallel *)
      apply simp
      apply (intro allI conjI impI)
        apply (metis liftC_rev_iff(1))
       apply metis
      apply metis
    (* INDet *)
     apply (simp, fast)
    (* ENDet *)
    apply (clarsimp simp add: liftC_rev_iff, metis)
    (* Atom *)
   apply (simp, fastforce)
    (* DoLoop *)
  apply (simp, metis)
  done

lemma double_no_tau_aopstep:
  fixes sxl syl :: \<open>'l::pre_perm_alg\<close>
    and sxs sys :: \<open>'s\<close>
  assumes
    \<open>\<forall>s' c'. \<not> ((sxl, sxs), c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl s', c')\<close>
    \<open>\<forall>s' c'. \<not> ((syl, sys), c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl s', c')\<close>
    \<open>tau_aact \<beta>\<close>
  shows
    \<open>\<forall>s' c'. \<not> (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl s', c')\<close>
  using assms
proof (induct c arbitrary: \<beta> sxl syl sxs sys)
  case Skip
  then show ?case by force
next
  case (Seq c1 c2)
  then show ?case
    by (clarsimp simp add: liftC_rev_iff, metis)
next
  case (Par c1 c2)
  show ?case
    using Par.prems
    apply (clarsimp simp add: liftC_rev_iff)
    apply (intro conjI)
      apply blast
     apply (clarsimp simp add: Par.hyps(1); fail)
    apply (clarsimp simp add: Par.hyps(2); fail)
    done
next
  case (Indet c1 c2)
  then show ?case
    by (simp, metis)
next
  case (Endet c1 c2)
  then show ?case
    by (simp add: liftC_rev_iff, fast)
next
  case (Atomic p q)
  then show ?case
    by clarsimp
next
  case (Iter c)
  then show ?case
    apply (clarsimp simp add: all_conj_distrib)
    oops

lemma double_step_endent_tau_helper1:
  shows
    \<open>(\<beta> = TauBasic \<and> c1 = Skip \<and> syl' = syl \<and> sys' = sys \<and> c' = c2 \<or>
      \<beta> = TauBasic \<and> c2 = Skip \<and> syl' = syl \<and> sys' = sys \<and> c' = c1 \<or>
      (\<exists>c1'. c' = c1' \<box> c2 \<and> ((syl, sys), c1) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl (syl', sys'), c1')) \<or>
      (\<exists>c2'. c' = c1 \<box> c2' \<and> ((syl, sys), c2) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl (syl', sys'), c2'))) \<and>
    (\<beta> = TauBasic \<and> c1 = Skip \<and> sxl' = sxl \<and> sxs' = sxs \<and> c' = c2 \<or>
      \<beta> = TauBasic \<and> c2 = Skip \<and> sxl' = sxl \<and> sxs' = sxs \<and> c' = c1 \<or>
      (\<exists>c1'. c' = c1' \<box> c2 \<and> ((sxl, sxs), c1) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl (sxl', sxs'), c1')) \<or>
      (\<exists>c2'. c' = c1 \<box> c2' \<and> ((sxl, sxs), c2) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl (sxl', sxs'), c2'))) \<longleftrightarrow>
    (\<exists>c1'. c' = c1' \<box> c2 \<and>
      ((syl, sys), c1) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl (syl', sys'), c1') \<and>
      ((sxl, sxs), c1) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl (sxl', sxs'), c1')) \<or>
    (\<exists>c2'. c' = c1 \<box> c2' \<and>
      ((syl, sys), c2) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl (syl', sys'), c2') \<and>
      ((sxl, sxs), c2) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl (sxl', sxs'), c2')) \<or>
    (\<beta> = TauBasic \<and> c1 = Skip \<and> c2 = c' \<or>
      \<beta> = TauBasic \<and> c1 = c' \<and> c2 = Skip) \<and>
      sxl' = sxl \<and> sxs' = sxs \<and> syl' = syl \<and> sys' = sys\<close>
  apply (simp add: conj_disj_distribL conj_disj_distribR)
  apply (rule iffI)
   apply (elim disjE)
                  apply force
                 apply force
                apply force
               apply (metis Pair_inject aopstep_endet_skip_then(2))
              apply force
             apply force
            apply (metis Pair_inject aopstep_endet_skip_then(1))
           apply force
          apply (metis aopstep.simps(1))
         apply (metis Pair_inject aopstep_endet_skip_then(1))
        apply force
       apply (clarsimp, metis self_aopstep_impossible(1))
      apply (metis Pair_inject aopstep_endet_skip_then(2))
     apply (metis aopstep.simps(1))
    apply (clarsimp, metis self_aopstep_impossible(1))
   apply force
  apply (elim disjE; metis)
  done

lemma double_stepI:
  fixes sxl syl :: \<open>'l::pre_perm_alg\<close>
    and sxs sys :: \<open>'s\<close>
  shows
  \<open>((sxl, sxs), c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl (sxl', sxs'), c') \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl (syl', sys'), c') \<Longrightarrow>
    sec_head_determ c ((sxl, sxs), (syl, sys)) \<Longrightarrow>
    (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>\<beta>\<rightarrow>\<^sub>a
      (Inl ((sxl', syl'), (sxs', sys')), liftC c')\<close>
  apply (induct c arbitrary: sxl syl sxs sys sxl' syl' sxs' sys' c' \<beta>)
    (* Skip *)
        apply force
    (* Seq *)
       apply clarsimp
       apply (elim disjE)
          apply force
         apply force
        apply force
       apply (clarsimp, metis)
    (* Parallel *)
      apply (clarsimp simp add: liftC_rev_iff)
      apply (elim disjE; clarsimp; metis)
      (* INDet *)
     apply fastforce
      (* ENDet *)
    apply (clarsimp del: disjCI split: if_splits simp del: disj_not1)
    (** Tau *)
     apply (simp add: liftC_rev_iff vis_tau_aact_incompatible del: disj_not1)
     apply (drule(1) iffD1[OF double_step_endent_tau_helper1, OF conjI])+
     apply (thin_tac \<open>Not _ \<or> Not _\<close>)+
     apply (thin_tac \<open>_ \<or> _ \<or> _ \<or> _\<close>)+
     apply (elim disjE)
       apply metis
      apply metis
     apply metis
    (** non-Tau *)
    apply (subgoal_tac \<open>\<beta> \<noteq> TauBasic\<close>)
     prefer 2
     apply force
    apply simp
    apply (elim disjE)
    (*** 1/1 *)
       apply (metis not_vis_aact_iff)
    (*** 2/1: forbidden *)
      apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
      apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
      apply (simp add: heads_dom_def)
      apply (metis (mono_tags) inf1I pre_state_def)
    (*** 1/2: forbidden *)
     apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
     apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
     apply (simp add: heads_dom_def)
     apply (metis (mono_tags) inf1I pre_state_def)
    (*** 2/2 *)
    apply (metis not_vis_aact_iff)
    (* Atom *)
   apply (clarsimp split: if_splits; fail)
    (* Do-loop *)
  apply (clarsimp simp add: liftC_rev_iff del: disjCI)
  apply (subgoal_tac \<open>c' = Skip \<or> (\<exists>ca cb. c' = ca ;; DO cb OD)\<close>)
   prefer 2
   apply blast
  apply (erule disjE[of \<open>_ = _\<close> \<open>Ex _\<close>])
    (* in order to complete a do-loop, it must be impossible for the sub-program
        to take a step. *)
  subgoal sorry
  oops


section \<open> Non-interference \<close>

lemma aopsteps_iff:
  \<open>(s, Skip) \<midarrow>\<beta>s\<rightarrow>\<^sub>a\<^sup>* zc'' \<longleftrightarrow> zc'' = (Inl s, Skip) \<and> \<beta>s = []\<close>
  \<open>(s, ca ;; cb) \<midarrow>\<beta>s\<rightarrow>\<^sub>a\<^sup>* zc'' \<longleftrightarrow>
    \<beta>s = [] \<and> zc'' = (Inl s, ca ;; cb) \<or>
    (\<exists>\<beta> \<beta>s'.
      \<beta>s = \<beta> # \<beta>s' \<and>
      (\<exists>s' c'.
        (\<beta> = TauBasic \<and> ca = Skip \<and> s' = s \<and> c' = cb \<or>
          (\<exists>ca'. (s, ca) \<midarrow>\<beta>\<rightarrow>\<^sub>a (Inl s', ca') \<and> c' = ca' ;; cb)) \<and>
        (s', c') \<midarrow>\<beta>s'\<rightarrow>\<^sub>a\<^sup>* zc''))\<close>
(*
  \<open>(s, ca \<^bold>+ cb) \<midarrow>\<beta>s\<rightarrow>\<^sub>a\<^sup>* zc'' \<longleftrightarrow>
    \<beta>s = [] \<and> zc'' = (Inl s, ca \<^bold>+ cb) \<or>
    (\<exists>\<beta> \<beta>s'.
      \<beta>s = TauBasic # \<beta>s' \<and>
      (\<exists>c'. (c' = ca \<or> c' = cb) \<and> (s, c') \<midarrow>\<beta>s'\<rightarrow>\<^sub>a\<^sup>* zc''))\<close>
*)
    apply (cases zc'', induct \<beta>s; force)
   apply (cases zc'', induct \<beta>s; force)
  (*apply (cases zc'', cases s, induct \<beta>s; (clarsimp; blast))*)
  done


section \<open> Security \<close>

lemma safe_ensures_exec_no_crash:
  \<open>safe n c z r g q S F \<Longrightarrow>
    z = Inl s \<Longrightarrow>
    (s, c) \<midarrow>r, F, \<rho>\<rightarrow>\<^sub>e\<^sup>* (ms', c') \<Longrightarrow>
    length \<rho> \<le> n \<Longrightarrow>
    \<forall>f s. F (f,s) \<longrightarrow> cancellative f \<Longrightarrow>
    \<exists>s'. ms' = Inl s'\<close>
  apply (induct arbitrary: s \<rho> rule: safe.inducts)
   apply force
  apply clarsimp
  apply (erule esteps.cases)
    apply force
   apply (clarsimp, blast)
  apply clarsimp
  apply (erule estepE)
   apply force
  apply clarsimp
  apply (drule meta_spec2, drule meta_spec2, drule meta_mp, assumption,
      drule meta_mp, assumption, drule meta_mp, assumption)
  apply clarsimp
  apply (metis cancellativeD)
  done

(* TODO: probably could be moved. *)
text \<open>
  A simple lemma: execution to any state means the state predicate holds on that state.
\<close>
lemma safe_ensures_exec_always_state_pred:
  \<open>safe n c z R G q S F \<Longrightarrow>
    z = Inl s \<Longrightarrow>
    (s, c) \<midarrow>R, F, \<rho>\<rightarrow>\<^sub>e\<^sup>* (Inl s', c') \<Longrightarrow>
    length \<rho> \<le> n \<Longrightarrow>
    \<forall>f s. F (f,s) \<longrightarrow> cancellative f \<Longrightarrow>
    \<forall>s s' l. R s s' \<longrightarrow> S (l,s) \<longrightarrow> S (l,s') \<Longrightarrow>
    S s \<Longrightarrow>
    S s'\<close>
  apply (induct arbitrary: s \<rho> rule: safe.inducts)
   apply force
  apply clarsimp
  apply (erule esteps.cases)
    apply force
   apply force
  apply clarsimp
  apply (rename_tac la' sa' la'' sa'' ca' \<rho>)
  apply (erule estepE)
   apply force
  apply clarsimp
  apply (drule meta_spec2, drule meta_spec2, drule meta_mp, assumption,
      drule meta_mp, assumption, drule meta_mp, assumption)
  apply clarsimp
  apply (subgoal_tac \<open>la'' = hl'\<close>)
   prefer 2
   apply (metis cancellativeD)
  apply clarsimp
  done


lemma esteps_implies_weak_double_step:
  \<open>(ss, c) \<midarrow>RR, FF, \<rho>\<rightarrow>\<^sub>e\<^sup>* (Inl ss', c') \<Longrightarrow>
    exch4 ss = (sx, sy) \<Longrightarrow>
    exch4 ss' = (sx', sy') \<Longrightarrow>
    ((sx, c), (sy, c)) =RR, FF, CC, (\<rho>, \<rho>)\<Rightarrow>\<^sup>* ((sx', c'), (sy', c'))\<close>
  sorry

text \<open> The important lemma for proving info-flow security. \<close>


lemma determ_and_weak_double_sync_implies_double_sync:
  \<open>\<forall>\<rho> msx' cx' msy' cy'.
    ((sx, c), (sy, c)) =RR, FF, (=), (\<rho>, \<rho>)\<Rightarrow>\<^sup>* ((msx', cx'), (msy', cy')) \<Longrightarrow>
  \<bbbA> \<oo> \<le> sec_head_determ c \<Longrightarrow>
  \<bbbA> \<oo> (sx, sy) \<Longrightarrow>
  ((sx, c), (sy, c)) =RR, FF, \<top>, (\<rho>x, \<rho>y)\<Rightarrow>\<^sup>* ((msx', cx'), (msy', cy'))\<close>
  apply (induct \<rho>x \<rho>y rule: list_induct2')
     apply blast
    apply blast
   apply blast
  apply clarsimp
  sorry



text \<open> Double execution aggregation lemma \<close>
theorem determ_double_exec_then_safe_state:
  fixes n :: nat
    and c :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
    and sx sy :: \<open>'l \<times> 's\<close>
    and r :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
    and F :: \<open>'l \<times> 's \<Rightarrow> bool\<close>
  assumes inductive_assms:
    \<open>safe n cc zz rr gg qq SS FF\<close>
    \<open>cc = liftC c\<close>
    \<open>zz = Inl (exch4 (sx, sy))\<close>
    \<open>((sx, c), (sy, c)) =rr, FF, (=), (\<rho>x, \<rho>y)\<Rightarrow>\<^sup>* ((msx', c'), (msy', c'))\<close>
    \<open>length \<rho>x < n\<close>
    \<open>length \<rho>y < n\<close>
  and noninductive_assms:
    \<open>\<forall>l s. FF (l, s) \<longrightarrow> (cancellative \<times>\<^sub>P cancellative) l\<close>
    \<comment> \<open>rely_obs_safe \<oo> r\<close> \<comment> \<open> we don't need this because rr is inherently declassifying \<close>
  shows
    \<open>cx' = cy' \<and> (\<exists>sx' sy'. msx' = Inl sx' \<and> msy' = Inl sy' \<and> SS (exch4 (sx', sy')))\<close>
  using inductive_assms
proof (induct n arbitrary: cc zz c sx sy \<rho>x \<rho>y cx' cy')
  case 0
  then show ?case
    by (clarsimp simp add: le_fun_def)
next
  case (Suc n)

  obtain sxl sxs where sx_split: \<open>sx = (sxl, sxs)\<close>
    by fastforce
  obtain syl sys where sy_split: \<open>sy = (syl, sys)\<close>
    by fastforce

  show ?case
    using Suc.prems sx_split sy_split
    apply (clarsimp simp add: liftC_rev_iff simp del: comp_apply)
    apply (erule dsteps.cases, force)
    apply (clarsimp simp del: comp_apply)
    apply (erule dstep.cases; clarsimp)
      (* Env *)
     apply (rename_tac sxs' sys' \<gamma>\<gamma>s)
     apply (clarsimp simp add: safe_suc_iff)
     apply (drule spec2, drule mp, assumption)
     apply (drule Suc.hyps)
          apply (simp; fail)
         apply (simp; fail)
        apply (simp; fail)
       apply (simp; fail)
      apply (clarsimp simp add: pred_executions_suc_iff)
      apply (metis (no_types, lifting) ext comp_apply)
     apply (simp; fail)
      (* Local *)
    apply (rename_tac sx' c' ly' sy' \<gamma>\<gamma>s' fx fy \<tau>xs cx' \<beta>x lx' \<tau>ys cy' \<beta>y)
    apply (clarsimp simp add: safe_suc_iff)
    apply (subgoal_tac \<open>\<beta>y = \<beta>x\<close>)
     prefer 2 (* TODO: not true *)
    subgoal sorry
    apply (subgoal_tac \<open>cx' = cy'\<close>)
     prefer 2 (* TODO: not true *)
    subgoal sorry
    apply clarsimp
    apply (frule(1) double_stepI[where sxs=sxs and sys=sys])
     apply (clarsimp simp add: pred_executions_suc_iff le_fun_def sepconj_conjI)
    subgoal sorry
    apply (drule_tac x=\<open>strip_aact \<beta>x\<close> in spec, drule spec2, drule spec2,
        drule mp, (rule conjI; assumption))
    apply (drule mp, rule strip_aopstep, assumption)
    apply clarsimp
    apply (rename_tac lx'2 ly'2)
    apply (subgoal_tac \<open>lx'2 = lx' \<and> ly'2 = ly'\<close>)
     prefer 2
     apply (cut_tac noninductive_assms(1))
     apply (simp add: pred_Times_def)
     apply (metis cancellativeD)
    apply (clarify, simp)
    apply (drule Suc.hyps)
         apply (simp add: exch4_def; fail)
        apply (simp; fail)
       apply (simp; fail)
      apply (simp; fail)
     apply (clarsimp simp add: pred_executions_suc_iff)
     apply (drule spec2, drule spec2, drule spec2, drule spec2,
        drule mp, (rule conjI; assumption))
     apply (drule mp, rule strip_aopstep, assumption)
     apply clarsimp
     apply (rename_tac lx'2 ly'2)
     apply (subgoal_tac \<open>lx'2 = lx' \<and> ly'2 = ly'\<close>)
      prefer 2
      apply (cut_tac noninductive_assms(1))
      apply (simp add: pred_Times_def)
      apply (metis cancellativeD)
     apply (clarify, simp)
     apply (simp add: le_fun_def; fail)
    apply force
    done
qed

corollary noninterference:
  fixes n :: nat
    and c :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
    and sx sy :: \<open>'l \<times> 's\<close>
    and r :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
    and F :: \<open>'l \<times> 's \<Rightarrow> bool\<close>
  assumes inductive_assms:
    \<open>safe n cc zz rr gg qq SS FF\<close>
    \<open>cc = liftC c\<close>
    \<open>zz = Inl (exch4 (sx, sy))\<close>
    \<open>(sfx, c) \<midarrow>r, \<gamma>s\<rightarrow>\<^sub>e\<^sup>* (Inl sfx', cx')\<close>
    \<open>(sfy, c) \<midarrow>r, \<gamma>s\<rightarrow>\<^sub>e\<^sup>* (Inl sfy', cy')\<close>
    \<open>((=) sx \<^emph>\<and> F) sfx\<close>
    \<open>((=) sy \<^emph>\<and> F) sfy\<close>
    \<open>length \<gamma>s < n\<close>
    \<open>pred_executions
      (\<lambda>(s, c).
        (FF \<midarrow>\<^emph>\<^sub>\<and> (determ_steps (SS \<^emph>\<and> FF) r (unliftC c) \<circ> exch4)) s \<and>
        (FF \<midarrow>\<^emph>\<^sub>\<and> (sec_head_determ (unliftC c) \<circ> exch4)) s)
      FF rr cc zz n\<close>
  and noninductive_assms:
    \<open>\<forall>xl xs. F (xl, xs) \<longrightarrow> cancellative xl\<close>
    \<open>rr = liftR r\<close>
    \<open>FF = liftP F \<circ> exch4\<close>
    \<open>SS = liftP S \<circ> exch4\<close>
    \<open>rely_obs_safe \<oo> rr\<close>
    \<open>\<forall>xl xs xs'. r xs xs' \<longrightarrow> F (xl, xs) \<longrightarrow> F (xl, xs')\<close>
    \<open>SS \<^emph>\<and> FF \<le> \<bbbA> \<oo> \<circ> exch4\<close>
  shows
    \<open>(=) (sfx', sfy') \<le> \<bbbA> \<oo>\<close>
  using determ_double_exec_then_safe_state[OF assms(1-15)] assms(16)
  by (clarsimp simp add: sepconj_conj_def exch4_def le_fun_def imp_ex_conjL imp_conjL
      split: prod.splits)



section \<open> TMP \<close>

text \<open>
  TODO
  unfortunately dependent on the state the command is executed in, because of loops.
\<close>
inductive basic_tau_reducts :: \<open>'s \<Rightarrow> 's comm \<Rightarrow> 's comm \<Rightarrow> bool\<close> where
  btr_skip[intro!]: \<open>basic_tau_reducts s Skip Skip\<close>
| btr_seq_left[intro]:
  \<open>basic_tau_reducts s ca ca' \<Longrightarrow> ca' \<noteq> Skip \<Longrightarrow>
    basic_tau_reducts s (ca ;; cb) (ca' ;; cb)\<close>
| btr_seq_right[intro]:
  \<open>basic_tau_reducts s ca Skip \<Longrightarrow>
    basic_tau_reducts s cb cb' \<Longrightarrow>
    basic_tau_reducts s (ca ;; cb) cb'\<close>
| btr_indet[intro!]:
  \<open>basic_tau_reducts s (ca \<^bold>+ cb) (ca \<^bold>+ cb)\<close>
| btr_endet_nonskip[intro]:
  \<open>basic_tau_reducts s ca ca' \<Longrightarrow> ca' \<noteq> Skip \<Longrightarrow>
    basic_tau_reducts s cb cb' \<Longrightarrow> cb' \<noteq> Skip \<Longrightarrow>
    basic_tau_reducts s (ca \<box> cb) (ca' \<box> cb')\<close>
| btr_endet_skip_left[intro]:
  \<open>basic_tau_reducts s ca Skip \<Longrightarrow>
    basic_tau_reducts s cb cb' \<Longrightarrow>
    basic_tau_reducts s (ca \<box> cb) cb'\<close>
| btr_endet_skip_right[intro]:
  \<open>basic_tau_reducts s ca ca' \<Longrightarrow>
    basic_tau_reducts s cb Skip \<Longrightarrow>
    basic_tau_reducts s (ca \<box> cb) ca'\<close>
| btr_par_nonend[intro]:
  \<open>basic_tau_reducts s ca ca' \<Longrightarrow>
    basic_tau_reducts s cb cb' \<Longrightarrow>
    ca' \<noteq> Skip \<or> cb' \<noteq> Skip \<Longrightarrow>
    basic_tau_reducts s (ca \<parallel> cb) (ca' \<parallel> cb')\<close>
| btr_par_end[intro]:
  \<open>basic_tau_reducts s ca Skip \<Longrightarrow>
    basic_tau_reducts s cb Skip \<Longrightarrow>
    basic_tau_reducts s (ca \<parallel> cb) Skip\<close>
| btr_loop_done[intro]:
  \<open>\<forall>\<alpha> s' c'. \<not> aopstep \<alpha> (s, c) (Inl s', c') \<Longrightarrow>
    basic_tau_reducts s (DO ca OD) Skip\<close>
| btr_loop_steps[intro]:
  \<comment> \<open> Note: an infinite tau loop is related to everything. \<close>
  \<open>basic_tau_reducts s ca ca' \<Longrightarrow>
    ca' \<noteq> Skip \<Longrightarrow>
    basic_tau_reducts s (ca' ;; DO ca OD) cx \<Longrightarrow>
    basic_tau_reducts s (DO ca OD) cx\<close>
| btr_atom[intro!]:
  \<open>basic_tau_reducts s (Atomic pa qa) (Atomic pa qa)\<close>

inductive_cases btr_skipE[elim!]: \<open>basic_tau_reducts s Skip c'\<close>
inductive_cases btr_seqE[elim]: \<open>basic_tau_reducts s (ca ;; cb) c'\<close>
inductive_cases btr_indetE[elim!]: \<open>basic_tau_reducts s (ca \<^bold>+ cb) c'\<close>
inductive_cases btr_endetE[elim]: \<open>basic_tau_reducts s (ca \<box> cb) c'\<close>
inductive_cases btr_parE[elim]: \<open>basic_tau_reducts s (ca \<parallel> cb) c'\<close>
inductive_cases btr_loopE[elim]: \<open>basic_tau_reducts s (DO ca OD) c'\<close>
inductive_cases btr_atomE[elim!]: \<open>basic_tau_reducts s \<langle>pa, qa\<rangle> c'\<close>

lemma btr_skip_left_iff[simp]: \<open>basic_tau_reducts s Skip c' \<longleftrightarrow> c' = Skip\<close>
  by (cases c') force+


fun etrace_aact_reduce :: \<open>aact eact list \<Rightarrow> aact list\<close> where
  \<open>etrace_aact_reduce [] = []\<close>
| \<open>etrace_aact_reduce (Env # \<sigma>) = etrace_aact_reduce \<sigma>\<close>
| \<open>etrace_aact_reduce (Loc \<rho> # \<sigma>) = \<rho> @ etrace_aact_reduce \<sigma>\<close>
| \<open>etrace_aact_reduce (Crash x # \<sigma>) = etrace_aact_reduce \<sigma>\<close>

lemma basic_tau_reducts_from_basic_tau_step:
  \<open>(s, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (ms', c') \<Longrightarrow>
    basic_tau_reducts s c c' \<Longrightarrow>
    ms' = Inl s \<and> basic_tau_aact \<alpha>\<close>
  apply (induct c arbitrary: \<alpha> s ms' c')
        apply force
       apply clarsimp
  sorry

lemma no_aopstep_then_basic_tau_reduct_false[simp]:
  \<open>(s, c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow> basic_tau_reducts s c c' \<longleftrightarrow> c' = c\<close>
  apply (induct c arbitrary: c')
        apply force
       apply (force simp add: all_conj_distrib)
      apply (clarsimp simp add: all_conj_distrib)
      apply (rule iffI)
       apply (erule btr_parE; force)
      apply blast
     apply (force simp add: all_conj_distrib)
    apply (clarsimp simp add: all_conj_distrib if_bool_eq_disj)
    apply (rule iffI)
     apply (erule btr_endetE; metis aopstep_aact_cases)
    apply (metis btr_endet_nonskip aopstep_aact_cases)
   apply (force simp add: if_bool_eq_disj)
  apply (clarsimp simp add: if_bool_eq_disj, metis)
  done

lemma basic_tau_reducts_step:
  \<open>(s, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inl s', c') \<Longrightarrow>
    basic_tau_aact \<alpha> \<Longrightarrow>
    basic_tau_reducts s c c'' \<Longrightarrow>
    basic_tau_reducts s c' c''\<close>
  apply (induct c arbitrary: \<alpha> s s' c' c'')
        apply fastforce
       apply fastforce
      apply clarsimp
      apply (elim disjE)
        apply blast
       apply (metis basic_tau_aact.simps(5) btr_parE btr_par_end btr_par_nonend)
      apply (metis basic_tau_aact.simps(6) btr_parE btr_par_end btr_par_nonend)
     apply fastforce
    apply (clarsimp simp add: if_bool_eq_disj, fast)
   apply fastforce
  apply simp
  apply (elim disjE)
   apply clarsimp
  sorry


lemma basic_tau_reducts_from_basic_tau_exec:
  \<open>(s, c) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (ms', c') \<Longrightarrow>
    basic_tau_reducts s c c' \<Longrightarrow>
    ms' = Inl s \<and> list_all basic_tau_aact \<rho>\<close>
  apply (induct \<rho>)
   apply force
  apply clarsimp
  apply (frule basic_tau_reducts_from_basic_tau_step)
  oops

lemma basic_tau_equiv_dstep_secure:
  \<open>xyc =RR, FF, CC, (\<sigma>x, \<sigma>y)\<Rightarrow> xyc' \<Longrightarrow>
    xyc = ((tx, cx), (ty, cy)) \<Longrightarrow>
    xyc' = ((Inl tx', cx'), (Inl ty', cy')) \<Longrightarrow>
    list_all basic_tau_aact (etrace_aact_reduce \<sigma>x) \<Longrightarrow>
    list_all basic_tau_aact (etrace_aact_reduce \<sigma>y) \<Longrightarrow>
    basic_tau_succ (tx, cx) = basic_tau_succ (tx', cx') \<Longrightarrow>
    basic_tau_succ (ty, cy) = basic_tau_succ (tx', cy') \<Longrightarrow>
    rely_obs_safe \<oo> RR \<Longrightarrow>
    \<bbbA> \<oo> (tx, ty) \<Longrightarrow>
    \<bbbA> \<oo> (tx', ty')\<close>
proof (induct arbitrary: tx cx ty cy tx' cx' ty' cy' rule: dstep.induct)
  case (dstep_env RR sx sy sx' sy' CC cxx cyy FF lx ly)
  then show ?case
    unfolding rely_obs_safe_def
    by fast
next
  case (dstep_local FF fx fy sx sy CC cxx cyy lx \<rho>x lx' sx' cxx' ly \<rho>y ly' sy' cyy' RR)
  then show ?case
    apply clarsimp
    sorry
qed


section \<open> Examples \<close>

(* TODO: move *)

lemma eq_rtimes_R_iff:
  \<open>((=) \<times>\<^sub>R r) s s' \<longleftrightarrow> r (snd s) (snd s') \<and> fst s = fst s'\<close>
  by (cases s, cases s', force)

lemma top_rtimes_R_iff:
  \<open>(\<top> \<times>\<^sub>R r) s s' \<longleftrightarrow> r (snd s) (snd s')\<close>
  by (cases s, cases s', force)

(* TODO: write examples: (1) Arthur's nointerference, (2) observing local state *)

lemma sepimp_conj_step_mp:
  \<open>p \<le> p' \<Longrightarrow> (p' \<midarrow>\<^emph>\<^sub>\<and> q) \<^emph>\<and> p \<le> q\<close>
  by (meson order_refl sepimp_conj_mono sepimp_conj_sepconj_conj_shunt)

lemma comp2_exch4_over_rel_times[simp]:
  fixes ra :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
    and rb :: \<open>'b \<Rightarrow> 'b \<Rightarrow> bool\<close>
  shows \<open>((ra \<times>\<^sub>R rb) \<times>\<^sub>R (rc \<times>\<^sub>R rd)) \<circ>\<^sub>2 exch4 = ((ra \<times>\<^sub>R rc) \<times>\<^sub>R (rb \<times>\<^sub>R rd))\<close>
  by (force simp add: comp_rel_def exch4_def rel_Times_def)

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
    \<open>r, g \<turnstile>\<^bsub>S, F\<^esub> { p } c { q }\<close>
    \<open>\<forall>p q.
        (p,q) \<in> all_atoms c \<longrightarrow>
        (\<forall>x x'. (S \<^emph>\<and> F) x \<longrightarrow> p x \<longrightarrow> q x x' \<longrightarrow>
          {\<rho>. fst x \<rho> \<noteq> fst x' \<rho>} \<subseteq> V)\<close>
  shows
    \<open>liftR r, liftR g \<turnstile>\<^bsub>\<bbbA> f \<circ> exch4, liftP F \<circ> exch4\<^esub> { liftP p \<circ> exch4 } liftC c { liftP q \<circ> exch4 }\<close>
  sorry

lemma opstep_all_atoms_antimono:
  \<open>sc \<midarrow>\<alpha>\<rightarrow> zc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    zc' = (Inl s', c') \<Longrightarrow>
    all_atoms c' \<le> all_atoms c\<close>
  apply (induct \<alpha> sc zc' arbitrary: s c s' c' rule: opstep.induct)
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
    \<open>z = Inl s\<close>
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